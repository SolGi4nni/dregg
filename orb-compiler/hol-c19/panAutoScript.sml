(* ===========================================================================
   C15 probe — PART 0b: the REUSABLE, PROGRAM-AGNOSTIC automation THEORY.

   These are the generic lemmas the `panLinkA_branch` tactic (panAutoLib) and
   the wrapper/LinkB generator rest on.  None mentions any particular primitive;
   every one is stated over an arbitrary loop-free Pancake body with the
   canonical load_vec/report_vec control-block shape.  Built ONCE, reused for
   every loop-free primitive.

     * signed_lt_n2w64   — Pancake `<` (signed) agrees with nat `<` in range.
     * eval_lt_pinned    — GENERIC guard evaluation: a `Cmp Less` on a pinned
                           local reduces to the boolean `if x < y then 1w else 0w`.
                           This is the program-agnostic replacement for the c2
                           `eval_class_guard`/`eval_cap_guard` hand lemmas — the
                           tactic instantiates THIS instead of per-primitive
                           guard lemmas.
     * Annot_Seq_eval    — the emitted `Seq (Annot ..) X` is evaluation-equal to
                           `X` (unconditional), so the tactic sweeps location
                           Annots away with a plain rewrite.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;

val _ = new_theory "panAuto";

(* On the non-negative signed range the SIGNED word order agrees with nat order.
   (Identical to c2/machineStepLinkA's convention lemma; re-proved here so the
   automation theory is self-contained and carries no machine-step baggage.) *)
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

(* THE generic guard-evaluation lemma.  For a local `v` pinned to `n2w x`, the
   emitted signed `Cmp Less (Var Local v) (Const (n2w y))` evaluates to the
   boolean word.  Side conditions `x,y < 2^63` (as the literal 2^63) discharge
   automatically from any realistic input bound via ARITH.  This is what the
   tactic instantiates in place of bespoke per-primitive guard lemmas. *)
Theorem eval_lt_pinned:
  FLOOKUP (s:(64,'ffi) panSem$state).locals v = SOME (ValWord (n2w x)) /\
  x < 9223372036854775808 /\ y < 9223372036854775808 ==>
  eval s (Cmp Less (Var Local v) (Const (n2w y))) =
    SOME (ValWord (if x < y then 1w else 0w))
Proof
  strip_tac >>
  `(2:num) ** 63 = 9223372036854775808` by EVAL_TAC >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        asmTheory.word_cmp_def] >>
  `((n2w x):word64 < n2w y) = (x < y)`
     by (irule signed_lt_n2w64 >> fs []) >>
  pop_assum (fn th => REWRITE_TAC [th])
QED

(* The emitted location Annots are semantically transparent: a leading
   `Seq (Annot l m)` is evaluation-equal to its tail.  Unconditional, so the
   tactic strips every Annot in the spine with one rewrite. *)
Theorem Annot_Seq_eval:
  evaluate (Seq (Annot l m) X, s) = evaluate (X, s)
Proof
  simp [Once evaluate_def, evaluate_def] >>
  Cases_on `evaluate (X,s)` >> simp [fix_clock_def] >>
  simp [state_component_equality]
QED

(* GENERIC `If (Cmp Less ..) t f` reduction: a signed `<` guard on a pinned
   local selects the arm by the boolean `x < y`.  This is what the tactic
   rewrites every emitted decision node with — the whole guard mechanics packed
   into one rewrite whose side conditions (FLOOKUP + range) discharge from the
   relation + ARITH. *)
Theorem evaluate_If_lt:
  FLOOKUP (s:(64,'ffi) panSem$state).locals v = SOME (ValWord (n2w x)) /\
  x < 9223372036854775808 /\ y < 9223372036854775808 ==>
  evaluate (If (Cmp Less (Var Local v) (Const (n2w y))) t f, s) =
    (if x < y then evaluate (t, s) else evaluate (f, s))
Proof
  strip_tac >>
  drule_all eval_lt_pinned >>
  disch_then (fn th => simp [Once evaluate_def, th]) >>
  Cases_on `x < y` >> simp []
QED

(* GENERIC If reduction keyed on a KNOWN guard value: once the tactic has
   established `eval s g = SOME (ValWord w)` (via eval_lt_pinned), simp solves
   this side condition from the assumption (determining w) and selects the arm.
   Unlike evaluate_If_lt, `w` is determined by the side-condition match, so this
   fires as a conditional rewrite. *)
Theorem evaluate_If_reduce:
  eval (s:(64,'ffi) panSem$state) g = SOME (ValWord w) ==>
  evaluate (If g c1 c2, s) = if w <> 0w then evaluate (c1,s) else evaluate (c2,s)
Proof
  strip_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def] >> rw []
QED

(* The boolean word produced by eval_lt_pinned tests as its own predicate: the
   tactic collapses `evaluate_If_reduce`'s `(if P then 1w else 0w) <> 0w` guard
   back to `P`, so LHS and RHS carry the SAME nest of source-level guards. *)
Theorem cond1w_ne0:
  ((if P then (1w:word64) else 0w) <> 0w) = P
Proof
  rw []
QED

(* GENERIC straight-line leaf: assigning a constant word to an existing local
   writes it, no FFI, no clock.  The tactic reduces every cascade leaf with it. *)
Theorem evaluate_Assign_const:
  FLOOKUP (s:(64,'ffi) panSem$state).locals r = SOME (ValWord r0) ==>
  evaluate (Assign Local r (Const w), s) = (NONE, set_var r (ValWord w) s)
Proof
  strip_tac >>
  simp [Once evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def,
        shape_of_def, set_kvar_def, set_var_def]
QED

val _ = export_theory ();
