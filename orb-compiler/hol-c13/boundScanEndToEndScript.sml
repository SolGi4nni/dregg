(* ===========================================================================
   C13 probe, PART D2 — THE FINAL COMPOSITION: spec  ->  machine code.

   Composes the whole-program Link-A wrapper (C13 boundScanInstall:
   boundScanProg_semantics_decls — spec  <=>  the observable
   `semantics_decls s «main» boundScanProg` trace) with C11's Link-B backend
   theorem (`boundScanProg_linkB`: machine_sem  SUBSET  { semantics_decls ... })
   into ONE kernel-checked theorem:

       machine_sem mc ffi ms  SUBSET
         extend_with_resource_limit' (...)
           { Terminate Success <trace carrying n2w (c0_encode (boundScan a off len))> }

   i.e. every observable behaviour of the INSTALLED x64 MACHINE CODE emitted for
   boundScan is the single terminating trace whose reported result word is
   EXACTLY the Lean spec `model/BoundScan.lean` `C0.encode (C0.boundScan a off len)`.

   The install-package hypotheses are taken VERBATIM (antiquoted) from
   boundScanProg_linkB's own antecedent, so the standard CakeML machine-state
   package is neither weakened nor re-transcribed; the ONLY extra hypotheses are
   the single FFI-oracle contract `boundScanFFI` and a witness clock.  The
   backend's `semantics_decls <> Fail` side condition is PROVED here (from the
   Link-A wrapper), not assumed.

   Trust ledger: HOL4 + CakeML kernels; the standard CakeML machine-state install
   package (the boundScanProg_linkB antecedents, kept as hypotheses); and the
   SINGLE FFI-oracle contract `boundScanFFI`.  NOT leanc: `boundScanProg` is the
   CakeML-verified Pancake parser's output on leanc's exact bytes (C10/C11).
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open boundScanLinkBInstTheory;      (* boundScanProg, boundScanProg_linkB *)
open boundScanCoreLinkATheory;      (* boundScan, c0_encode *)
open boundScanWrapperLinkATheory;   (* boundScanFFI *)
open boundScanInstallTheory;        (* boundScanProg_semantics_decls *)

val _ = new_theory "boundScanEndToEnd";

(* --- take boundScanProg_linkB's install-package antecedent and conclusion
       VERBATIM (antiquoted), so the standard CakeML machine-state package is
       neither weakened nor re-transcribed; drop only its `semantics_decls <>
       Fail` conjunct (which we PROVE from the Link-A wrapper). --- *)
val linkB_ant    = boundScanProg_linkB |> concl |> dest_imp |> #1;
val linkB_concl  = boundScanProg_linkB |> concl |> dest_imp |> #2;   (* = subset_sd *)
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
       (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb]``;

val subset_sd    = linkB_concl;
val subset_spec  = subst [sd_tm |-> ``Terminate Success ^trace_tm``] linkB_concl;

val e2e_goal =
  mk_imp (list_mk_conj [pkg_tm,
                        ``boundScanFFI a off len (s:(64,'ffi) panSem$state)``,
                        ``?K. 0 < K /\ len < K``],
          mk_exists (``loadEv:io_event list``,
            mk_exists (``rb:(word8 # word8) list``, subset_spec)));

Theorem boundScan_machine_code = prove (e2e_goal,
  strip_tac >>
  (* (Link A) the observable declaration semantics IS the spec-word trace *)
  `?loadEv rb. ^sd_tm = Terminate Success ^trace_tm`
     by (irule boundScanProg_semantics_decls >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >>
  (* the backend non-Fail side condition, PROVED from the Link-A value *)
  `^notFail_tm`
     by (qpat_x_assum `^sd_tm = _` (fn th => simp [th])) >>
  (* (Link B) at the concrete program: machine_sem SUBSET { semantics_decls ... } *)
  `^subset_sd`
     by (match_mp_tac boundScanProg_linkB >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  (* substitute the Link-A value of semantics_decls into the singleton set *)
  qpat_x_assum `^sd_tm = _` (fn th => gvs [th]));

val _ = export_theory ();
