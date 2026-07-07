(* ===========================================================================
   C14 probe, PART A — the BESPOKE branch-only core Link A.

   The SECOND primitive is a MACHINE step (model/MachineStep.lean C2.step):
   a saturating event-counter transition, emitted as a NESTED DECISION with
   NO loop.  This is the structurally-different counterpart to boundScan's
   scan-`While`: its Link A is a pure case-split (decidable), with NO loop
   invariant and — crucially — NO clock precondition.

   `stepCore` is the VERBATIM `If` node lifted from `functions stepGateProg`
   (the parser's output on the emitted machinestep_gate.pnk).  We prove, against
   real `panSem$evaluate`, that it writes EXACTLY the Lean spec's next counter
   `n2w (mstep c b)` into the local «result».  Reuses the c2 machineStepLinkA
   guard lemmas (`eval_class_guard`, `eval_cap_guard`, `mstep`, `mstep_le`).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open machineStepLinkATheory;        (* mstep, mstep_le, mRel, eval_class_guard, eval_cap_guard *)
open c14GenericTheory;                (* Annot_Seq, Seq_thread, noFFI (generic, reused) *)

val _ = new_theory "stepCore";

(* stepCore = the VERBATIM emitted branch-only If (from `functions stepGateProg`),
   with the two Assign arms behind their location Annots. *)
Definition stepCore_def:
  stepCore =
    If (Cmp Less (Var Local «b») (Const (128w:word64)))
       (Seq (Annot «location» «(26:4 26:13)»)
          (Assign Local «result» (Var Local «c»)))
       (Seq (Annot «location» «(28:7 31:17)»)
          (If (Cmp Less (Var Local «c») (Const (255w:word64)))
             (Seq (Annot «location» «(29:6 29:18)»)
                (Assign Local «result»
                   (Op Add [Var Local «c»; Const (1w:word64)])))
             (Seq (Annot «location» «(31:6 31:17)»)
                (Assign Local «result» (Const (255w:word64))))))
End

(* The core relation: c/b/result in locals, ranges for the (signed) guards. *)
Definition stepRel_def:
  stepRel (c:num) (b:num) (r0:word64) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «c» = SOME (ValWord (n2w c)) /\
    FLOOKUP s.locals «b» = SOME (ValWord (n2w b)) /\
    FLOOKUP s.locals «result» = SOME (ValWord r0) /\
    c <= 255 /\ b < 256
End

Theorem stepRel_mRel:
  stepRel c b r0 s ==> mRel c b s
Proof
  rw [stepRel_def, mRel_def]
QED

(* --- the three leaves, each a straight-line Annot;Assign --- *)
Theorem stepCore_hold:
  stepRel c b r0 s /\ b < 128 ==>
  evaluate (stepCore, s) = (NONE, set_var «result» (ValWord (n2w c)) s)
Proof
  strip_tac >>
  `mRel c b s` by metis_tac [stepRel_mRel] >>
  drule eval_class_guard >> strip_tac >>
  `FLOOKUP s.locals «c» = SOME (ValWord (n2w c))` by fs [stepRel_def] >>
  `FLOOKUP s.locals «result» = SOME (ValWord r0)` by fs [stepRel_def] >>
  `(1w:word64) <> 0w` by EVAL_TAC >>
  simp [stepCore_def, Once evaluate_def] >> fs [] >>
  `evaluate (Assign Local «result» (Var Local «c»), s)
     = (NONE, set_var «result» (ValWord (n2w c)) s)`
     by (simp [Once evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def,
               shape_of_def, set_kvar_def, set_var_def]) >>
  irule Annot_Seq >> first_assum ACCEPT_TAC
QED

Theorem stepCore_event:
  stepRel c b r0 s /\ ~(b < 128) ==>
  evaluate (stepCore, s) = (NONE, set_var «result» (ValWord (n2w (mstep c b))) s)
Proof
  strip_tac >>
  `mRel c b s` by metis_tac [stepRel_mRel] >>
  drule eval_class_guard >> drule eval_cap_guard >> rpt strip_tac >>
  `FLOOKUP s.locals «c» = SOME (ValWord (n2w c))` by fs [stepRel_def] >>
  `FLOOKUP s.locals «result» = SOME (ValWord r0)` by fs [stepRel_def] >>
  `(1w:word64) <> 0w` by EVAL_TAC >>
  simp [stepCore_def, Once evaluate_def] >> fs [] >>
  (* take the else-arm: inner If on c<255 *)
  `evaluate
     (If (Cmp Less (Var Local «c») (Const 255w))
         (Seq (Annot «location» «(29:6 29:18)»)
            (Assign Local «result» (Op Add [Var Local «c»; Const 1w])))
         (Seq (Annot «location» «(31:6 31:17)»)
            (Assign Local «result» (Const 255w))), s)
     = (NONE, set_var «result» (ValWord (n2w (mstep c b))) s)`
     by (Cases_on `c < 255` >>
         simp [Once evaluate_def] >> fs [] >>
         irule Annot_Seq >>
         simp [Once evaluate_def, eval_def, OPT_MMAP_def,
               wordLangTheory.word_op_def, word_add_n2w, is_valid_value_def,
               lookup_kvar_def, shape_of_def, set_kvar_def, set_var_def,
               mstep_def]) >>
  irule Annot_Seq >> first_assum ACCEPT_TAC
QED

(* --- the headline core equation: writes exactly the Lean next counter --- *)
Theorem evaluate_stepCore:
  stepRel c b r0 s ==>
  evaluate (stepCore, s) = (NONE, set_var «result» (ValWord (n2w (mstep c b))) s)
Proof
  strip_tac >> Cases_on `b < 128`
  >- (drule_all stepCore_hold >> simp [mstep_def]) >>
  drule_all stepCore_event >> simp []
QED

(* --- framed: for the whole-main wrapper; NO clock precondition (branch-only) --- *)
Theorem evaluate_stepCore_framed:
  stepRel c b r0 s ==>
  ?s'. evaluate (stepCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (mstep c b))) /\
       (!v. v <> «result» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >> drule evaluate_stepCore >> strip_tac >>
  qexists_tac `set_var «result» (ValWord (n2w (mstep c b))) s` >>
  simp [set_var_def, FLOOKUP_UPDATE] >> rw [] >> simp [FLOOKUP_UPDATE]
QED

(* stepCore performs no FFI: reusing the generic noFFI predicate. *)
Theorem stepCore_noFFI:
  noFFI stepCore
Proof
  REWRITE_TAC [stepCore_def] >> EVAL_TAC
QED

val _ = export_theory ();
