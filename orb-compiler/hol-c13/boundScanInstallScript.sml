(* ===========================================================================
   C13 probe, PART D1 — whole-program Link A at the DECLS level.
   Installing boundScanProg (single Function «main», empty struct context) into
   any FEMPTY-code state and running the observational `semantics_decls` yields
   exactly the spec-word FFI trace.  C13's mainBody_refines / main_semantics
   lifted through the trivial single-Function install.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open boundScanLinkBInstTheory;      (* boundScanProg, boundScanProg_def *)
open boundScanCoreLinkATheory;      (* innerCore_def, boundScan, c0_encode *)
open boundScanDigestLinkATheory;    (* digLoop_def, digBody_def *)
open boundScanWrapperLinkATheory;   (* mainBody, mainBody_def, boundScanFFI, boundScanFFI_def *)
open boundScanSemTheory;            (* main_semantics *)

val _ = new_theory "boundScanInstall";

val decs_ev = (REWRITE_CONV [boundScanProg_def] THENC EVAL)
                ``decs_stcnames [] boundScanProg``;
val evd_ev  = (REWRITE_CONV [boundScanProg_def] THENC EVAL)
                ``evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    boundScanProg``;

Theorem boundScanProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\
  boundScanFFI a off len s /\ (?K. 0 < K /\ len < K) ==>
  ?loadEv rb.
    semantics_decls s «main» boundScanProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall «report_vec»)
            (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) boundScanProg)` >>
  `semantics_decls s «main» boundScanProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], mainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [boundScanProg_def] >> EVAL_TAC >>
         REWRITE_TAC [mainBody_def, innerCore_def, digLoop_def, digBody_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [boundScanProg_def] >> EVAL_TAC) >>
  `!Kc. boundScanFFI a off len
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `boundScanFFI a off len s` mp_tac >>
         asm_simp_tac (srw_ss()) [boundScanFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ExtCall «report_vec»)
           (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();
