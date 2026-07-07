(* ===========================================================================
   C15 probe, PART E1 — whole-program Link A at the DECLS level.
   Installing gzipUpperProg (single Function «main», empty struct context) and
   running `semantics_decls` yields exactly the spec-word FFI trace.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open gzipUpperLinkBInstTheory;    (* gzipUpperProg, gzipUpperProg_def *)
open gzipUpperCoreTheory;         (* gzipUpperCore_def, gzipUpper *)
open gzipUpperWrapperTheory;      (* gzipUpperMainBody, gzipUpperMainBody_def, gzipUpperFFI, gzipUpperFFI_def *)
open gzipUpperSemTheory;          (* main_semantics *)

val _ = new_theory "gzipUpperInstall";

val decs_ev = (REWRITE_CONV [gzipUpperProg_def] THENC EVAL)
                ``decs_stcnames [] gzipUpperProg``;
val evd_ev  = (REWRITE_CONV [gzipUpperProg_def] THENC EVAL)
                ``evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    gzipUpperProg``;

Theorem gzipUpperProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\ gzipUpperFFI code s ==>
  ?loadEv rb.
    semantics_decls s «main» gzipUpperProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall «report_vec»)
            (word_to_bytes (n2w (gzipUpper code) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) gzipUpperProg)` >>
  `semantics_decls s «main» gzipUpperProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], gzipUpperMainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [gzipUpperProg_def] >> EVAL_TAC >>
         REWRITE_TAC [gzipUpperMainBody_def, gzipUpperCore_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [gzipUpperProg_def] >> EVAL_TAC) >>
  `!Kc. gzipUpperFFI code
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `gzipUpperFFI code s` mp_tac >>
         asm_simp_tac (srw_ss()) [gzipUpperFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ExtCall «report_vec»)
           (word_to_bytes (n2w (gzipUpper code) : word64) F) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();
