open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open machineLoopLinkATheory;         (* memRel, memRel_def, Seq_NONE *)
open boundScanCoreLinkATheory;       (* innerCore, coreRel, evaluate_innerCore, boundScan, c0_encode *)
open boundScanDigestLinkATheory;     (* digLoop, digBody *)
open semLiftTheory;                  (* semantics_Return_lift *)
(* NB: boundScanLinkBInstTheory (which loads the CakeML backend proofs) is
   deliberately NOT opened here — opening it makes `state_component_equality`
   / record syntax ambiguous across the backend `state` types.  The link to
   `boundScanProg` and the Link-B composition live in the separate
   boundScanEndToEnd theory, which uses only backend-robust tactics. *)

val _ = new_theory "boundScanWrapperLinkA";

(* --- noFFI: a syntactic class of programs that make no FFI/oracle call --- *)
Definition noFFI_def:
  (noFFI Skip = T) /\
  (noFFI (Dec _ _ _ p) = noFFI p) /\
  (noFFI (Assign _ _ _) = T) /\
  (noFFI (Primitive _ _ _) = T) /\
  (noFFI (Store _ _) = T) /\
  (noFFI (Store32 _ _) = T) /\
  (noFFI (StoreByte _ _) = T) /\
  (noFFI (Seq p1 p2) = (noFFI p1 /\ noFFI p2)) /\
  (noFFI (If _ p1 p2) = (noFFI p1 /\ noFFI p2)) /\
  (noFFI (While _ p) = noFFI p) /\
  (noFFI Break = T) /\
  (noFFI Continue = T) /\
  (noFFI (Call _ _ _) = F) /\
  (noFFI (DecCall _ _ _ _ _) = F) /\
  (noFFI (ExtCall _ _ _ _ _) = F) /\
  (noFFI (Raise _ _) = T) /\
  (noFFI (Return _) = T) /\
  (noFFI (ShMemLoad _ _ _ _) = F) /\
  (noFFI (ShMemStore _ _ _) = F) /\
  (noFFI Tick = T) /\
  (noFFI (Annot _ _) = T)
End

Theorem noFFI_io_events:
  !p s res t. evaluate (p,s) = (res,t) /\ noFFI p ==>
              t.ffi.io_events = s.ffi.io_events
Proof
  recInduct evaluate_ind >> rpt strip_tac >> fs [noFFI_def]
  >~ [`While`]
  >- (qpat_x_assum `evaluate _ = _`
        (strip_assume_tac o ONCE_REWRITE_RULE [evaluate_def]) >>
      gvs [AllCaseEqs (), empty_locals_def, ELIM_UNCURRY, dec_clock_def] >>
      metis_tac [PAIR, FST, SND]) >>
  qpat_x_assum `evaluate _ = _` mp_tac >>
  simp [Once evaluate_def] >>
  rpt (pairarg_tac >> gvs []) >>
  gvs [AllCaseEqs (), empty_locals_def, ELIM_UNCURRY, dec_clock_def, set_var_def,
       set_kvar_def, kvar_defs] >>
  rw [] >> gvs [] >>
  metis_tac [PAIR, FST, SND]
QED

(* --- threading a NONE-producing Seq into any continuation --- *)
Theorem Seq_thread:
  evaluate (p1,s) = (NONE,sa) /\ sa.clock <= s.clock /\
  evaluate (p2,sa) = (res,sb) ==>
  evaluate (Seq p1 p2, s) = (res, sb)
Proof
  rpt strip_tac >> simp [Once evaluate_def] >>
  `fix_clock s (evaluate (p1,s)) = (NONE, sa)`
     by (rw [fix_clock_def] >> gvs [state_component_equality]) >>
  gvs []
QED

(* --- an Annot-prefixed statement is transparent --- *)
Theorem Annot_Seq:
  evaluate (X, s) = (res, sb) ==>
  evaluate (Seq (Annot l m) X, s) = (res, sb)
Proof
  strip_tac >> irule Seq_thread >> qexists_tac `s` >> simp [evaluate_def]
QED

(* --- a Dec with its (arbitrary-result) body --- *)
Theorem Dec_eval:
  !v sh e prog s res st val.
    eval s e = SOME val /\ sh = shape_of val /\
    evaluate (prog, s with locals := s.locals |+ (v,val)) = (res, st) ==>
    evaluate (Dec v sh e prog, s) =
      (res, st with locals := res_var st.locals (v, FLOOKUP s.locals v))
Proof
  rpt strip_tac >> simp [evaluate_def]
QED

(* --- trace-threading wrappers: carry only the io_events of the body --- *)
Theorem Dec_trace:
  eval s e = SOME val /\ sh = shape_of val /\
  (?st. evaluate (prog, s with locals := s.locals |+ (v,val)) = (res, st) /\
        st.ffi.io_events = tr) ==>
  ?st'. evaluate (Dec v sh e prog, s) = (res, st') /\ st'.ffi.io_events = tr
Proof
  rpt strip_tac >> drule_all Dec_eval >> strip_tac >>
  qexists_tac `st with locals := res_var st.locals (v, FLOOKUP s.locals v)` >> simp []
QED

Theorem Annot_trace:
  (?st. evaluate (X, s) = (res, st) /\ st.ffi.io_events = tr) ==>
  ?st'. evaluate (Seq (Annot l m) X, s) = (res, st') /\ st'.ffi.io_events = tr
Proof
  rpt strip_tac >> drule Annot_Seq >> strip_tac >> qexists_tac `st` >> simp []
QED

Theorem Seq_trace:
  evaluate (p1, s) = (NONE, sa) /\ sa.clock <= s.clock /\
  (?st. evaluate (p2, sa) = (res, st) /\ st.ffi.io_events = tr) ==>
  ?st'. evaluate (Seq p1 p2, s) = (res, st') /\ st'.ffi.io_events = tr
Proof
  rpt strip_tac >> drule_all Seq_thread >> strip_tac >> qexists_tac `st` >> simp []
QED

(* --- a Dec, tracking only the observable trace (ffi) of its body --- *)
Theorem Dec_ffi:
  !v sh e prog s res st val.
    eval s e = SOME val /\ sh = shape_of val /\
    evaluate (prog, s with locals := s.locals |+ (v,val)) = (res, st) ==>
    ?st'. evaluate (Dec v sh e prog, s) = (res, st') /\ st'.ffi = st.ffi
Proof
  rpt strip_tac >> drule_all Dec_eval >> strip_tac >>
  qexists_tac `st with locals := res_var st.locals (v, FLOOKUP s.locals v)` >>
  simp []
QED

(* --- the `st base+24, result` store of the computed result word --- *)
Theorem evaluate_store_result:
  !s ba w.
    FLOOKUP s.locals «base» = SOME (ValWord ba) /\
    FLOOKUP s.locals «result» = SOME (ValWord w) /\
    (ba + 24w) IN s.memaddrs ==>
    evaluate (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»), s) =
      (NONE, s with memory := ((ba + 24w) =+ Word w) s.memory)
Proof
  rpt strip_tac >>
  simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        flatten_def, mem_stores_def, mem_store_def]
QED

(* --- reading a control-block word from staged memory (context-free) --- *)
Theorem eval_load_ctrl:
  !s ba w.
    FLOOKUP s.locals «base» = SOME (ValWord ba) /\ ba IN s.memaddrs /\
    s.memory ba = Word w ==>
    eval s (Load One (Var Local «base»)) = SOME (ValWord w)
Proof
  rpt strip_tac >> simp [eval_def, is_wf_shape_def, mem_load_def]
QED

Theorem eval_var_add:
  !s ba k.
    FLOOKUP s.locals «base» = SOME (ValWord ba) ==>
    eval s (Op Add [Var Local «base»; Const k]) = SOME (ValWord (ba + k))
Proof
  rpt strip_tac >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]
QED

Theorem eval_load_off:
  !s ba k w.
    FLOOKUP s.locals «base» = SOME (ValWord ba) /\ (ba + k) IN s.memaddrs /\
    s.memory (ba + k) = Word w ==>
    eval s (Load One (Op Add [Var Local «base»; Const k])) = SOME (ValWord w)
Proof
  rpt strip_tac >>
  simp [eval_def, is_wf_shape_def, mem_load_def, OPT_MMAP_def,
        wordLangTheory.word_op_def]
QED

(* ---------------------------------------------------------------------------
   The staged control block + arena the load_vec oracle must establish.
   Word-addressed control block at base: [0)=alen, [8)=off, [16)=len, [24)=result;
   arena bytes at base+32 (the `memRel` byte relation the scan loop reads).
   --------------------------------------------------------------------------- *)
Definition ctrlStaged_def:
  ctrlStaged (a:num list) off len (ba:word64) (s:(64,'ffi) panSem$state) <=>
    ba IN s.memaddrs /\ s.memory ba = Word (n2w (LENGTH a)) /\
    (ba + 8w) IN s.memaddrs /\ s.memory (ba + 8w) = Word (n2w off) /\
    (ba + 16w) IN s.memaddrs /\ s.memory (ba + 16w) = Word (n2w len) /\
    (ba + 24w) IN s.memaddrs /\
    memRel a (ba + 32w) s /\
    LENGTH a < 2n ** 63 /\ off + len < 2n ** 63 /\ EVERY (\x. x < 256) a
End

(* ---------------------------------------------------------------------------
   THE SINGLE NAMED TRUSTED ASSUMPTION — the FFI-oracle contract.
   (L) @load_vec stages the control block + arena into memory (per ctrlStaged),
       preserving clock/locals/config, extending the trace by some prefix.
   (R) @report_vec emits the result word `w` (read from the result slot base+24)
       onto the observable FFI trace as an IO_event carrying `word_to_bytes w`.
   This is NOT a proof of the oracle; it is the contract the oracle satisfies,
   irreducible because the observable behaviour IS an FFI I/O trace.
   --------------------------------------------------------------------------- *)
Definition boundScanFFI_def:
  boundScanFFI (a:num list) off len (s0:(64,'ffi) panSem$state) <=>
    (* (L) *)
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «base» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «buf»  = SOME (ValWord (s.base_addr + 32w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «base») (Const 24w)
                     (Var Local «buf») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         ctrlStaged a off len s.base_addr s1 /\
         s1.ffi.io_events = s.ffi.io_events ++ loadEv) /\
    (* (R) *)
    (!(s:(64,'ffi) panSem$state) (w:word64).
           FLOOKUP s.locals «base» = SOME (ValWord s.base_addr) /\
           (s.base_addr + 24w) IN s.memaddrs /\
           s.memory (s.base_addr + 24w) = Word w ==>
       ?s2 rb.
         evaluate (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w])
                     (Const 8w) (Var Local «base») (Const 8w), s) = (NONE, s2) /\
         s2.clock = s.clock /\
         s2.ffi.io_events =
           s.ffi.io_events ++ [IO_event (ffi$ExtCall «report_vec») (word_to_bytes w F) rb])
End

(* ---------------------------------------------------------------------------
   `mainBody` = the VERBATIM body of «main» in boundScanProg (extracted by EVAL
   from `functions boundScanProg`), with the C12 `innerCore` constant in place
   of its decision+digest `If` node.
   --------------------------------------------------------------------------- *)
Definition mainBody_def:
  mainBody =
    Seq (Annot «location» «(UNKNOWN 44:10)»)
      (Dec «base» One BaseAddr
         (Seq (Annot «location» «(UNKNOWN 44:10)»)
            (Dec «buf» One (Op Add [Var Local «base»; Const 32w])
               (Seq
                  (Seq (Annot «location» «(23:2 23:27)»)
                     (ExtCall «load_vec» (Var Local «base») (Const 24w)
                        (Var Local «buf») (Const 4096w)))
                  (Seq (Annot «location» «(UNKNOWN 44:10)»)
                     (Dec «alen» One (Load One (Var Local «base»))
                        (Seq (Annot «location» «(UNKNOWN 44:10)»)
                           (Dec «off» One
                              (Load One (Op Add [Var Local «base»; Const 8w]))
                              (Seq (Annot «location» «(UNKNOWN 44:10)»)
                                 (Dec «len» One
                                    (Load One
                                       (Op Add [Var Local «base»; Const 16w]))
                                    (Seq (Annot «location» «(UNKNOWN 44:10)»)
                                       (Dec «result» One (Const 0w)
                                          (Seq
                                             (Seq
                                                (Annot «location» «(31:5 40:15)»)
                                                innerCore)
                                             (Seq
                                                (Seq (Annot «location» «(42:5 42:20)»)
                                                   (Store
                                                      (Op Add
                                                         [Var Local «base»;
                                                          Const 24w])
                                                      (Var Local «result»)))
                                                (Seq
                                                   (Seq (Annot «location» «(43:2 43:30)»)
                                                      (ExtCall «report_vec»
                                                         (Op Add
                                                            [Var Local «base»;
                                                             Const 24w])
                                                         (Const 8w)
                                                         (Var Local «base»)
                                                         (Const 8w)))
                                                   (Seq
                                                      (Annot «location» «(44:9 44:10)»)
                                                      (Return (Const 0w))))))))))))))))))
End

(* innerCore performs no FFI: its run leaves the observable trace unchanged. *)
Theorem innerCore_noFFI:
  noFFI innerCore
Proof
  REWRITE_TAC [innerCore_def, digLoop_def, digBody_def] >> EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   evaluate_innerCore (C12) STRENGTHENED with the locals frame: the core writes
   ONLY «result»/«acc»/«i», so «base»/«buf» survive it into the Store/report.
   Re-derived here (C12 is not modified) reusing the C12 sub-lemmas verbatim.
   --------------------------------------------------------------------------- *)
Theorem evaluate_innerCore_framed:
  coreRel a off len buf r0 s /\ len <= s.clock ==>
  ?s'. evaluate (innerCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «result»
         = SOME (ValWord (n2w (c0_encode (boundScan a off len)))) /\
       (!v. v <> «result» /\ v <> «acc» /\ v <> «i» ==>
            FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >>
  drule eval_core_guard >> strip_tac >>
  Cases_on `boundScan a off len = NONE`
  >- (
    qabbrev_tac `sR = set_var «result» (ValWord (0xFFFFFFFFw:word64)) s` >>
    `FLOOKUP s.locals «result» = SOME (ValWord r0)` by fs [coreRel_def] >>
    `evaluate (Annot «location» «(32:4 32:22)», s) = (NONE, s)`
       by simp [evaluate_def] >>
    `evaluate (Assign Local «result» (Const 0xFFFFFFFFw), s) = (NONE, sR)`
       by (simp [Once evaluate_def, eval_def, Abbr `sR`] >>
           simp [is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
    `evaluate (innerCore, s) = (NONE, sR)`
       by (simp [innerCore_def, Once evaluate_def] >> fs [] >>
           irule Seq_NONE >> qexists_tac `s` >> rpt conj_tac >>
           (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
    qexists_tac `sR` >> simp [] >>
    `(0xFFFFFFFFw:word64) = n2w 4294967295` by EVAL_TAC >>
    conj_tac
    >- simp [Abbr `sR`, set_var_def, FLOOKUP_UPDATE, c0_encode_def] >>
    rpt strip_tac >> simp [Abbr `sR`, set_var_def, FLOOKUP_UPDATE]) >>
  `off + len <= LENGTH a` by (Cases_on `off + len <= LENGTH a` >> fs [boundScan_def]) >>
  `evaluate (Annot «location» «(UNKNOWN 40:15)», s) = (NONE, s)` by simp [evaluate_def] >>
  qabbrev_tac `s1 = s with locals := s.locals |+ («acc», ValWord 0w)` >>
  qabbrev_tac `s2 = s1 with locals := s1.locals |+ («i», ValWord 0w)` >>
  `s1.clock = s.clock /\ s2.clock = s.clock` by simp [Abbr `s1`, Abbr `s2`] >>
  `«acc» <> «i» /\ «acc» <> «len» /\ «acc» <> «buf» /\ «acc» <> «off» /\
   «acc» <> «result» /\ «i» <> «len» /\ «i» <> «buf» /\ «i» <> «off» /\
   «i» <> «result»` by EVAL_TAC >>
  `digInv a off buf len 0 0 s2`
     by (simp [digInv_def, Abbr `s2`, Abbr `s1`, FLOOKUP_UPDATE] >>
         fs [coreRel_def, memRel_def, FLOOKUP_UPDATE]) >>
  `len <= s2.clock` by fs [] >>
  drule_all digLoop_refines_scanFrom >> strip_tac >>
  qmatch_asmsub_rename_tac `evaluate (digLoop, s2) = (NONE, sL)` >>
  `sL.clock <= s2.clock` by (imp_res_tac evaluate_clock >> fs []) >>
  qabbrev_tac `sA = set_var «result» (ValWord (n2w (dscan a off len 0))) sL` >>
  `FLOOKUP sL.locals «acc» = SOME (ValWord (n2w (dscan a off len 0)))` by fs [] >>
  `FLOOKUP s2.locals «result» = SOME (ValWord r0)`
     by (simp [Abbr `s2`, Abbr `s1`, FLOOKUP_UPDATE] >> fs [coreRel_def]) >>
  `FLOOKUP sL.locals «result» = SOME (ValWord r0)`
     by (`FLOOKUP sL.locals «result» = FLOOKUP s2.locals «result»`
            by (first_x_assum irule >> EVAL_TAC) >> fs []) >>
  `evaluate (Annot «location» «(40:4 40:15)», sL) = (NONE, sL)` by simp [evaluate_def] >>
  `evaluate (Assign Local «result» (Var Local «acc»), sL) = (NONE, sA)`
     by (simp [Once evaluate_def, eval_def, Abbr `sA`] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  `evaluate (Annot «location» «(36:10 38:13)», s2) = (NONE, s2)` by simp [evaluate_def] >>
  `evaluate (Seq (Annot «location» «(36:10 38:13)») digLoop, s2) = (NONE, sL)`
     by (irule Seq_NONE >> qexists_tac `s2` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  `evaluate (Seq (Annot «location» «(40:4 40:15)»)
       (Assign Local «result» (Var Local «acc»)), sL) = (NONE, sA)`
     by (irule Seq_NONE >> qexists_tac `sL` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  `evaluate (Seq (Seq (Annot «location» «(36:10 38:13)») digLoop)
       (Seq (Annot «location» «(40:4 40:15)»)
            (Assign Local «result» (Var Local «acc»))), s2) = (NONE, sA)`
     by (irule Seq_NONE_le >> qexists_tac `sL` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE fs [])) >>
  qabbrev_tac `sI = sA with locals := res_var sA.locals («i», FLOOKUP s1.locals «i»)` >>
  `s1 with locals := s1.locals |+ («i», ValWord 0w) = s2` by simp [Abbr `s2`] >>
  `evaluate (Dec «i» One (Const 0w)
       (Seq (Seq (Annot «location» «(36:10 38:13)») digLoop)
            (Seq (Annot «location» «(40:4 40:15)»)
                 (Assign Local «result» (Var Local «acc»)))), s1) = (NONE, sI)`
     by (simp [Once evaluate_def, eval_def, shape_of_def, Abbr `sI`]) >>
  `evaluate (Annot «location» «(UNKNOWN 40:15)», s1) = (NONE, s1)` by simp [evaluate_def] >>
  `evaluate (Seq (Annot «location» «(UNKNOWN 40:15)»)
       (Dec «i» One (Const 0w)
          (Seq (Seq (Annot «location» «(36:10 38:13)») digLoop)
               (Seq (Annot «location» «(40:4 40:15)»)
                    (Assign Local «result» (Var Local «acc»))))), s1) = (NONE, sI)`
     by (irule Seq_NONE_le >> qexists_tac `s1` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE fs [])) >>
  qabbrev_tac `sAcc = sI with locals := res_var sI.locals («acc», FLOOKUP s.locals «acc»)` >>
  `s with locals := s.locals |+ («acc», ValWord 0w) = s1` by simp [Abbr `s1`] >>
  `evaluate (Dec «acc» One (Const 0w)
       (Seq (Annot «location» «(UNKNOWN 40:15)»)
            (Dec «i» One (Const 0w)
               (Seq (Seq (Annot «location» «(36:10 38:13)») digLoop)
                    (Seq (Annot «location» «(40:4 40:15)»)
                         (Assign Local «result» (Var Local «acc»)))))), s) = (NONE, sAcc)`
     by (simp [Once evaluate_def, eval_def, shape_of_def, Abbr `sAcc`]) >>
  `evaluate (Seq (Annot «location» «(UNKNOWN 40:15)»)
       (Dec «acc» One (Const 0w)
          (Seq (Annot «location» «(UNKNOWN 40:15)»)
               (Dec «i» One (Const 0w)
                  (Seq (Seq (Annot «location» «(36:10 38:13)») digLoop)
                       (Seq (Annot «location» «(40:4 40:15)»)
                            (Assign Local «result» (Var Local «acc»))))))), s) = (NONE, sAcc)`
     by (irule Seq_NONE_le >> qexists_tac `s` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE fs [])) >>
  `evaluate (innerCore, s) = (NONE, sAcc)`
     by (simp [innerCore_def, Once evaluate_def] >> fs []) >>
  qexists_tac `sAcc` >> simp [] >>
  `«result» <> «i» /\ «result» <> «acc»` by EVAL_TAC >>
  `boundScan a off len = SOME (dscan a off len 0)` by fs [boundScan_def] >>
  conj_tac
  >- (`FLOOKUP sAcc.locals «result» = FLOOKUP sA.locals «result»`
        by (simp [Abbr `sAcc`, Abbr `sI`, FLOOKUP_res_var_neq]) >>
      `FLOOKUP sA.locals «result» = SOME (ValWord (n2w (dscan a off len 0)))`
        by simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
      simp [c0_encode_def]) >>
  (* the locals frame: v not in {result,acc,i} survives the whole core *)
  rpt strip_tac >>
  `FLOOKUP sAcc.locals v = FLOOKUP sI.locals v`
     by (simp [Abbr `sAcc`, FLOOKUP_res_var_neq]) >>
  `FLOOKUP sI.locals v = FLOOKUP sA.locals v`
     by (simp [Abbr `sI`, FLOOKUP_res_var_neq]) >>
  `FLOOKUP sA.locals v = FLOOKUP sL.locals v`
     by (simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE]) >>
  `FLOOKUP sL.locals v = FLOOKUP s2.locals v` by (first_x_assum irule >> simp []) >>
  `FLOOKUP s2.locals v = FLOOKUP s.locals v`
     by (simp [Abbr `s2`, Abbr `s1`, FLOOKUP_UPDATE]) >>
  fs []
QED

val _ = export_theory ();
