(* ===========================================================================
   C15 probe, PART 0 — the PROGRAM-AGNOSTIC descent machinery.

   Byte-identical to C14's c14Generic (which was byte-identical to C13's generic
   lemmas + semLift) EXCEPT `evaluate_store_result`, which is here GENERALIZED
   from a fixed +24w result-slot offset to an arbitrary offset parameter `koff`
   — a strict generalization that makes the store lemma reusable at any control-
   block layout (the status classifier's result slot is at +8w).  Every theorem
   below is program-agnostic and reusable for ANY straight-line/branch Pancake
   program with the load_vec/report_vec FFI shape.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory optionTheory;

val _ = new_theory "c14Generic";

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

Theorem Annot_Seq:
  evaluate (X, s) = (res, sb) ==>
  evaluate (Seq (Annot l m) X, s) = (res, sb)
Proof
  strip_tac >> irule Seq_thread >> qexists_tac `s` >> simp [evaluate_def]
QED

Theorem Dec_eval:
  !v sh e prog s res st val.
    eval s e = SOME val /\ sh = shape_of val /\
    evaluate (prog, s with locals := s.locals |+ (v,val)) = (res, st) ==>
    evaluate (Dec v sh e prog, s) =
      (res, st with locals := res_var st.locals (v, FLOOKUP s.locals v))
Proof
  rpt strip_tac >> simp [evaluate_def]
QED

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

(* PROGRAM-AGNOSTIC store lemma, generalized over the result-slot OFFSET koff
   (C13/C14 fixed this at +24w; a loop-free primitive whose control block puts
   the result slot at any offset — e.g. the status classifier at +8w — reuses
   this at its own koff).  Strictly more general; the proof is unchanged. *)
Theorem evaluate_store_result:
  !s ba w koff.
    FLOOKUP s.locals «base» = SOME (ValWord ba) /\
    FLOOKUP s.locals «result» = SOME (ValWord w) /\
    (ba + koff) IN s.memaddrs ==>
    evaluate (Store (Op Add [Var Local «base»; Const koff]) (Var Local «result»), s) =
      (NONE, s with memory := ((ba + koff) =+ Word w) s.memory)
Proof
  rpt strip_tac >>
  simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        flatten_def, mem_stores_def, mem_store_def]
QED

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

(* --- the program-agnostic all-clocks semantics lift (from C13 semLift) --- *)
Theorem semantics_Return_lift:
  !s start K v t.
    evaluate (Call NONE start [], s with clock := K) = (SOME (Return v), t) ==>
    semantics s start = Terminate Success t.ffi.io_events
Proof
  rpt strip_tac >>
  qabbrev_tac `pgm = Call NONE start []` >>
  `?k0. evaluate (pgm, s with clock := k0) = (SOME (Return v), t with clock := 0)`
    by (`SOME (Return v) <> SOME TimeOut` by simp [] >>
        drule_all evaluate_min_clock >> strip_tac >> qexists_tac `k` >> fs []) >>
  `!k q' t'. evaluate (pgm, s with clock := k) = (q',t') ==>
             q' = SOME TimeOut \/ q' = SOME (Return v)`
    by (rpt gen_tac >> strip_tac >>
        `evaluate (pgm, (s with clock := k0) with clock := k) = (q',t')` by simp [] >>
        drule evaluate_add_clock_or_timeout >> simp [] >>
        disch_then drule >> strip_tac >> fs []) >>
  simp [semantics_def] >>
  `~(?k. case FST (evaluate (pgm, s with clock := k)) of
           SOME TimeOut => F | SOME (FinalFFI _) => F
         | SOME (Return _) => F | _ => T)`
    by (CCONTR_TAC >> fs [] >>
        Cases_on `evaluate (pgm, s with clock := k)` >>
        first_x_assum drule >> strip_tac >> fs []) >>
  simp [] >>
  (DEEP_INTRO_TAC some_intro >> conj_tac)
  >- (gen_tac >> strip_tac >> simp [] >> fs [] >>
      qmatch_asmsub_rename_tac `evaluate (pgm, s with clock := kk) = (rr,tt)` >>
      `rr = SOME TimeOut \/ rr = SOME (Return v)` by (first_x_assum drule >> simp []) >>
      fs [] >>
      `evaluate (pgm, (s with clock := k0) with clock := kk) = (SOME (Return v),tt)` by simp [] >>
      drule evaluate_add_clock_or_timeout >> simp [] >> disch_then drule >>
      strip_tac >> gvs [])
  >- (strip_tac >>
      `?k t' r outcome. evaluate (pgm,s with clock:=k) = (r,t') /\
          (case r of SOME (Return v6) => outcome = Success
                   | SOME (FinalFFI e) => outcome = FFI_outcome e | _ => F) /\
          Terminate Success t.ffi.io_events = Terminate outcome t'.ffi.io_events`
        by (qexists_tac `k0` >> qexists_tac `t with clock:=0` >>
            qexists_tac `SOME (Return v)` >> qexists_tac `Success` >> simp []) >>
      metis_tac [])
QED

val _ = export_theory ();
