(* ===========================================================================
   C15 probe, PART E1 — whole-program Link A at the DECLS level.
   Installing redirectStatusProg (single Function «main», empty struct context) and
   running `semantics_decls` yields exactly the spec-word FFI trace.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open redirectLinkBInstTheory;    (* redirectStatusProg, redirectStatusProg_def *)
open redirectCoreTheory;         (* redirectCore_def, redirectStatus *)
open redirectWrapperTheory;      (* redirectMainBody, redirectMainBody_def, redirectFFI, redirectFFI_def *)
open redirectSemTheory;          (* main_semantics *)

val _ = new_theory "redirectInstall";

val decs_ev = (REWRITE_CONV [redirectStatusProg_def] THENC EVAL)
                ``decs_stcnames [] redirectStatusProg``;
val evd_ev  = (REWRITE_CONV [redirectStatusProg_def] THENC EVAL)
                ``evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    redirectStatusProg``;

Theorem redirectStatusProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\ redirectFFI code s ==>
  ?loadEv rb.
    semantics_decls s «main» redirectStatusProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall «report_vec»)
            (word_to_bytes (n2w (redirectStatus code) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) redirectStatusProg)` >>
  `semantics_decls s «main» redirectStatusProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], redirectMainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [redirectStatusProg_def] >> EVAL_TAC >>
         REWRITE_TAC [redirectMainBody_def, redirectCore_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [redirectStatusProg_def] >> EVAL_TAC) >>
  `!Kc. redirectFFI code
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `redirectFFI code s` mp_tac >>
         asm_simp_tac (srw_ss()) [redirectFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ExtCall «report_vec»)
           (word_to_bytes (n2w (redirectStatus code) : word64) F) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();
