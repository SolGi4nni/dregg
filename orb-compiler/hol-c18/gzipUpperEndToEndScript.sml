(* ===========================================================================
   C15 probe, PART E2 — THE FINAL COMPOSITION: spec -> machine code, for the
   THIRD (loop-free classifier) primitive.  Composes
   gzipUpperProg_semantics_decls (whole-program Link A) with
   gzipUpperProg_linkB (Link B backend) into ONE kernel-checked theorem: every
   observable behaviour of the installed x64 machine code emitted for the status
   classifier is the single terminating trace whose reported word is EXACTLY the
   Lean spec `C15.gzipUpper` value `n2w (gzipUpper code)`.  The install-
   package hypotheses are taken VERBATIM from gzipUpperProg_linkB; the only
   extra hypothesis is the single FFI-oracle contract `gzipUpperFFI`.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open gzipUpperLinkBInstTheory;    (* gzipUpperProg, gzipUpperProg_linkB *)
open gzipUpperCoreTheory;         (* gzipUpper *)
open gzipUpperWrapperTheory;      (* gzipUpperFFI *)
open gzipUpperInstallTheory;      (* gzipUpperProg_semantics_decls *)

val _ = new_theory "gzipUpperEndToEnd";

val linkB_ant    = gzipUpperProg_linkB |> concl |> dest_imp |> #1;
val linkB_concl  = gzipUpperProg_linkB |> concl |> dest_imp |> #2;
val sd_tm        = find_term (fn t => same_const (fst (strip_comb t)) ``semantics_decls``
                              handle _ => false) linkB_concl;
val notFail_tm   = valOf (List.find (fn c => is_neg c andalso
     (let val e = dest_neg c in is_eq e andalso
        (same_const (fst (strip_comb (lhs e))) ``semantics_decls`` handle _ => false) end))
     (boolSyntax.strip_conj linkB_ant));
val pkg_tm       = list_mk_conj (filter (fn c => not (aconv c notFail_tm))
                                   (boolSyntax.strip_conj linkB_ant));

val trace_tm =
  ``(s:(64,'ffi) panSem$state).ffi.io_events ++ loadEv ++
    [IO_event (ffi$ExtCall «report_vec»)
       (word_to_bytes (n2w (gzipUpper code) : word64) F) rb]``;

val subset_sd    = linkB_concl;
val subset_spec  = subst [sd_tm |-> ``Terminate Success ^trace_tm``] linkB_concl;

val e2e_goal =
  mk_imp (list_mk_conj [pkg_tm,
                        ``gzipUpperFFI code (s:(64,'ffi) panSem$state)``],
          mk_exists (``loadEv:io_event list``,
            mk_exists (``rb:(word8 # word8) list``, subset_spec)));

Theorem gzipUpper_machine_code = prove (e2e_goal,
  strip_tac >>
  `?loadEv rb. ^sd_tm = Terminate Success ^trace_tm`
     by (irule gzipUpperProg_semantics_decls >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >>
  `^notFail_tm`
     by (qpat_x_assum `^sd_tm = _` (fn th => simp [th])) >>
  `^subset_sd`
     by (match_mp_tac gzipUpperProg_linkB >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qpat_x_assum `^sd_tm = _` (fn th => gvs [th]));

val _ = export_theory ();
