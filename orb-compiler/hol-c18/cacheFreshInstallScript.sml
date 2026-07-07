(* ===========================================================================
   C15 probe, PART E1 — whole-program Link A at the DECLS level.
   Installing cacheFreshProg (single Function «main», empty struct context) and
   running `semantics_decls` yields exactly the spec-word FFI trace.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open cacheFreshLinkBInstTheory;    (* cacheFreshProg, cacheFreshProg_def *)
open cacheFreshCoreTheory;         (* cacheFreshCore_def, cacheFresh *)
open cacheFreshWrapperTheory;      (* cacheFreshMainBody, cacheFreshMainBody_def, cacheFreshFFI, cacheFreshFFI_def *)
open cacheFreshSemTheory;          (* main_semantics *)

val _ = new_theory "cacheFreshInstall";

val decs_ev = (REWRITE_CONV [cacheFreshProg_def] THENC EVAL)
                ``decs_stcnames [] cacheFreshProg``;
val evd_ev  = (REWRITE_CONV [cacheFreshProg_def] THENC EVAL)
                ``evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    cacheFreshProg``;

Theorem cacheFreshProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\ cacheFreshFFI code s ==>
  ?loadEv rb.
    semantics_decls s «main» cacheFreshProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall «report_vec»)
            (word_to_bytes (n2w (cacheFresh code) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) cacheFreshProg)` >>
  `semantics_decls s «main» cacheFreshProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], cacheFreshMainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [cacheFreshProg_def] >> EVAL_TAC >>
         REWRITE_TAC [cacheFreshMainBody_def, cacheFreshCore_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [cacheFreshProg_def] >> EVAL_TAC) >>
  `!Kc. cacheFreshFFI code
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `cacheFreshFFI code s` mp_tac >>
         asm_simp_tac (srw_ss()) [cacheFreshFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ExtCall «report_vec»)
           (word_to_bytes (n2w (cacheFresh code) : word64) F) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();
