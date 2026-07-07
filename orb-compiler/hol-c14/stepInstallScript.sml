(* ===========================================================================
   C14 probe, PART D1 — whole-program Link A at the DECLS level.
   Installing stepGateProg (single Function «main», empty struct context) and
   running `semantics_decls` yields exactly the spec-word FFI trace.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open stepLinkBInstTheory;      (* stepGateProg, stepGateProg_def *)
open stepCoreTheory;           (* stepCore_def, mstep *)
open stepWrapperTheory;        (* stepMainBody, stepMainBody_def, stepFFI, stepFFI_def *)
open stepSemTheory;            (* main_semantics *)

val _ = new_theory "stepInstall";

val decs_ev = (REWRITE_CONV [stepGateProg_def] THENC EVAL)
                ``decs_stcnames [] stepGateProg``;
val evd_ev  = (REWRITE_CONV [stepGateProg_def] THENC EVAL)
                ``evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    stepGateProg``;

Theorem stepGateProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\ stepFFI c b s ==>
  ?loadEv rb.
    semantics_decls s «main» stepGateProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall «report_vec»)
            (word_to_bytes (n2w (mstep c b) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) stepGateProg)` >>
  `semantics_decls s «main» stepGateProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], stepMainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [stepGateProg_def] >> EVAL_TAC >>
         REWRITE_TAC [stepMainBody_def, stepCore_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [stepGateProg_def] >> EVAL_TAC) >>
  `!Kc. stepFFI c b
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `stepFFI c b s` mp_tac >>
         asm_simp_tac (srw_ss()) [stepFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ExtCall «report_vec»)
           (word_to_bytes (n2w (mstep c b) : word64) F) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();
