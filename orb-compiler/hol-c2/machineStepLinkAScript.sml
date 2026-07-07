(* ===========================================================================
   C2 probe — LINK A for a MACHINE primitive (a stateful transition step).

   C0/C1 dual-emitted and preservation-proved a REGION primitive (a bounds
   decision over a byte view): `boundScanLinkAScript.sml` proves the emitted
   bounds `If` refines the Lean model `boundScan`/`c0_encode` against the REAL
   Pancake source semantics `panSem$evaluate`/`panSem$eval`.

   This file GENERALIZES that Link A from a one-shot bounds decision to a
   STATEFUL TRANSITION: `State -> Input -> State`. The primitive is one step of
   a saturating event-counter FSM (model/MachineStep.lean `C2.step`):

       step c b  =  if b < 128 then c                    (* low byte: hold  *)
                    else if c < 255 then c + 1 else 255   (* high: saturate  *)

   We prove, against real `panSem$evaluate`, that running the emitted `.pnk`
   step body updates the machine's state local `c` to EXACTLY `n2w (step c b)`,
   AND re-establishes the state relation `mRel` at the new counter — i.e. the
   emitted transition refines the Lean transition and the relation is an
   INVARIANT the step preserves (so the machine can iterate). That invariant
   carries the saturation MEANING (`mstep_le`: the counter never exceeds 255).

   Scope, honestly: the whole machine `run` folds `step` over an input stream
   with a `While` loop. Link A for that fold — a loop-invariant induction over
   `panSem`'s clocked `While` clause (`c_n = FOLDL step c0 inputs`) — is NOT
   proven here; it is the exact analogue of C1's deferred scan `While` and is
   named UNCLOSED at the end. What IS closed end-to-end is the SINGLE transition.

   The comparison faithfulness note from C1 carries over verbatim: Pancake `<`
   is `LessT` -> `Cmp Less`, the SIGNED word comparison. Both operands here
   (`b < 256`, `c <= 255`) sit in the non-negative signed range, so the same
   `signed_lt_n2w64` convention lemma discharges both guards.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib;
open panLangTheory panSemTheory;

val _ = new_theory "machineStepLinkA";

(* ---------------------------------------------------------------------------
   The Lean SPEC, re-declared in HOL (byte-identical to C2.step over `num`).
   --------------------------------------------------------------------------- *)
Definition mstep_def:
  mstep (c:num) (b:num) =
    if b < 128 then c else if c < 255 then c + 1 else 255
End

(* The saturation MEANING (C2.step_le_cap): the transition never lets the
   counter exceed the cap. This is the load-bearing safety property and it is
   what keeps `mRel` an invariant across the step. *)
Theorem mstep_le:
  !c b. c <= 255 ==> mstep c b <= 255
Proof
  rw [mstep_def]
QED

(* ---------------------------------------------------------------------------
   The IMPLEMENTATION: the .pnk step body, as a real panLang AST.

     if b < 128 { c = c; }
     else { if c < 255 { c = c + 1; } else { c = 255; } }

   `Cmp Less` = the SIGNED test Pancake `<` compiles to. Word literals fixed to
   the word64 x64 target.
   --------------------------------------------------------------------------- *)
Definition stepBody_def:
  stepBody =
    If (Cmp Less (Var Local (strlit "b")) (Const (128w:word64)))
       (Assign Local (strlit "c") (Var Local (strlit "c")))
       (If (Cmp Less (Var Local (strlit "c")) (Const (255w:word64)))
           (Assign Local (strlit "c")
                   (Op Add [Var Local (strlit "c"); Const (1w:word64)]))
           (Assign Local (strlit "c") (Const (255w:word64))))
End

(* ---------------------------------------------------------------------------
   The state relation: the local env encodes state `c` and input `b` as words,
   and the sizes fit the (signed, non-negative) range the guards need.
   --------------------------------------------------------------------------- *)
Definition mRel_def:
  mRel (c:num) (b:num) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "c") = SOME (ValWord (n2w c)) /\
    FLOOKUP s.locals (strlit "b") = SOME (ValWord (n2w b)) /\
    c <= 255 /\ b < 256
End

(* ---------------------------------------------------------------------------
   The convention lemma (identical to C1's): on the non-negative signed range
   the SIGNED word order agrees with the nat order. Discharges both guards.
   --------------------------------------------------------------------------- *)
Theorem signed_lt_n2w64:
  !x y. x < 2n ** 63 /\ y < 2n ** 63 ==>
        (((n2w x):word64) < n2w y <=> x < y)
Proof
  rw [] >>
  `(2:num) ** 63 < 2 ** 64` by EVAL_TAC >>
  `x < dimword(:64) /\ y < dimword(:64)` by
    (`dimword(:64) = 2 ** 64` by EVAL_TAC >> fs [] >>
     conj_tac >> metis_tac [LESS_TRANS]) >>
  `~word_msb ((n2w x):word64) /\ ~word_msb ((n2w y):word64)` by
    (rw [word_msb_n2w] >> irule NOT_BIT_GT_TWOEXP >> fs []) >>
  rw [WORD_LT, w2n_n2w] >> fs []
QED

(* ---------------------------------------------------------------------------
   Guard evaluations: real `panSem$eval` of each guard = 1w EXACTLY on the arm
   the Lean SPEC takes. `eval_class_guard` decides hold-vs-event; `eval_cap_guard`
   decides advance-vs-saturate.
   --------------------------------------------------------------------------- *)
Theorem eval_class_guard:
  mRel c b s ==>
  eval s (Cmp Less (Var Local (strlit "b")) (Const (128w:word64)))
    = SOME (ValWord (if b < 128 then 1w else 0w))
Proof
  strip_tac >>
  qpat_x_assum `mRel _ _ _`
    (strip_assume_tac o SIMP_RULE std_ss [mRel_def]) >>
  `(128w:word64) = n2w 128` by EVAL_TAC >>
  `(n2w b:word64 < n2w 128) = (b < 128)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        asmTheory.word_cmp_def] >> fs []
QED

Theorem eval_cap_guard:
  mRel c b s ==>
  eval s (Cmp Less (Var Local (strlit "c")) (Const (255w:word64)))
    = SOME (ValWord (if c < 255 then 1w else 0w))
Proof
  strip_tac >>
  qpat_x_assum `mRel _ _ _`
    (strip_assume_tac o SIMP_RULE std_ss [mRel_def]) >>
  `(255w:word64) = n2w 255` by EVAL_TAC >>
  `(n2w c:word64 < n2w 255) = (c < 255)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        asmTheory.word_cmp_def] >> fs []
QED

(* ---------------------------------------------------------------------------
   LINK A, the transition core: real `panSem$evaluate` of the step body updates
   the state local `c` to EXACTLY the Lean model's next state `n2w (mstep c b)`,
   with no error. A kernel-checked equation between the actual Pancake source
   semantics and the Lean transition. This is the stateful generalization of
   C1's `evaluate_boundsChk` (which wrote a constant sentinel; this writes a
   data-dependent next state that is a function of the old state).
   --------------------------------------------------------------------------- *)
Theorem evaluate_stepBody:
  mRel c b s ==>
  evaluate (stepBody, s) =
    (NONE, set_var (strlit "c") (ValWord (n2w (mstep c b))) s)
Proof
  strip_tac >>
  `eval s (Cmp Less (Var Local (strlit "b")) (Const (128w:word64)))
     = SOME (ValWord (if b < 128 then 1w else 0w))` by metis_tac [eval_class_guard] >>
  `eval s (Cmp Less (Var Local (strlit "c")) (Const (255w:word64)))
     = SOME (ValWord (if c < 255 then 1w else 0w))` by metis_tac [eval_cap_guard] >>
  `FLOOKUP s.locals (strlit "c") = SOME (ValWord (n2w c))` by fs [mRel_def] >>
  `(1w:word64) <> 0w` by EVAL_TAC >>
  (* split the transition's three arms (hold / advance / saturate) and reduce
     each leaf against real `panSem$evaluate` uniformly. *)
  Cases_on `b < 128` >> Cases_on `c < 255` >>
  asm_simp_tac (srw_ss())
    [stepBody_def, evaluate_def, eval_def, OPT_MMAP_def,
     wordLangTheory.word_op_def, word_add_n2w, asmTheory.word_cmp_def,
     is_valid_value_def, lookup_kvar_def, shape_of_def, set_kvar_def,
     mstep_def]
QED

(* ---------------------------------------------------------------------------
   LINK A, the headline refinement + invariance: after one emitted step,
     (1) the state local `c` holds exactly the Lean next state, and
     (2) the state relation `mRel` holds again at the new counter —
   so the emitted transition REFINES the Lean transition and PRESERVES the
   relation. (2) carries the saturation MEANING (`c' <= 255`), which is why the
   step composes into a stream fold. This is the transition-system Link A.
   --------------------------------------------------------------------------- *)
Theorem stepBody_refines_step:
  mRel c b s ==>
  ?s'. evaluate (stepBody, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "c") = SOME (ValWord (n2w (mstep c b))) /\
       mRel (mstep c b) b s'
Proof
  strip_tac >> drule evaluate_stepBody >> rw [] >>
  qpat_x_assum `mRel _ _ _`
    (strip_assume_tac o SIMP_RULE std_ss [mRel_def]) >>
  simp [mRel_def, set_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac [mstep_le]
QED

val _ = export_theory ();
