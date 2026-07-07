(* ===========================================================================
   C12 probe, PART 2 — LINK A for the boundScan DECISION+DIGEST core, VERBATIM
   from boundScanProg.  This COMPOSES Part 1 (the digest loop, digLoop) with the
   bounds decision and the emitted `Dec acc / Dec i / result := acc` scoping,
   and proves that the WHOLE inner region of `main` — the bounds `If` with the
   real scan `While` inside its else-arm (NOT a `Skip` stub) — writes EXACTLY
   `n2w (c0_encode (boundScan a off len))` into the local «result».

   This strictly supersedes C1 (hol-c1/boundScanLinkAScript.sml), whose Link A
   covered only the bounds `If` with the loop replaced by `Skip`.  Here the loop
   is the genuine emitted `While` and its result flows into «result».

   The `innerCore` term is the exact `If` node lifted from `functions
   boundScanProg` (the `main` body), Annot/Dec/Panop/Op-And all verbatim, and it
   reuses `digLoop` (Part 1) unchanged as the else-arm's loop.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory;
open machineStepLinkATheory;        (* signed_lt_n2w64                          *)
open machineLoopLinkATheory;        (* memRel, memRel_def, Seq_NONE             *)
open boundScanDigestLinkATheory;    (* digLoop, dscan, digInv, digLoop_refines  *)

val _ = new_theory "boundScanCoreLinkA";

(* ---------------------------------------------------------------------------
   The Lean SPEC top level, re-declared in HOL (byte-identical to
   model/BoundScan.lean C0.boundScan/C0.encode and hol-c1's boundScan/c0_encode).
   `dscan` is Part 1's fold, byte-identical to C0.scanFrom.
   --------------------------------------------------------------------------- *)
Definition boundScan_def:
  boundScan a off len =
    if off + len <= LENGTH a then SOME (dscan a off len 0) else NONE
End

Definition c0_encode_def:
  (c0_encode NONE = 4294967295n) /\
  (c0_encode (SOME (k:num)) = k)
End

(* Restoring a Dec-bound local leaves any OTHER local untouched. *)
Theorem FLOOKUP_res_var_neq:
  k <> n ==> FLOOKUP (res_var lc (n, old)) k = FLOOKUP lc k
Proof
  Cases_on `old` >> rw [res_var_def, DOMSUB_FLOOKUP_NEQ, FLOOKUP_UPDATE]
QED

(* Seq with a clock-CONSUMING first component (C4/C6's `Seq_NONE_le`): the scan
   loop spends clock, so the clock-EQUAL `Seq_NONE` cannot sequence it. *)
Theorem Seq_NONE_le:
  !p1 p2 s sa sb.
    evaluate (p1,s) = (NONE,sa) /\ sa.clock <= s.clock /\
    evaluate (p2,sa) = (NONE,sb) ==>
    evaluate (Seq p1 p2, s) = (NONE, sb)
Proof
  rpt strip_tac >> simp [evaluate_def] >>
  `fix_clock s (evaluate (p1,s)) = (NONE, sa)`
     by (`~(s.clock < sa.clock)` by fs [] >>
         simp [fix_clock_def, state_component_equality]) >>
  simp []
QED

(* ---------------------------------------------------------------------------
   The IMPLEMENTATION: the emitted decision+digest `If`, VERBATIM from
   boundScanProg's `main` body (the bounds check with the real scan loop).
   --------------------------------------------------------------------------- *)
Definition innerCore_def:
  innerCore =
    If (Cmp Less (Var Local «alen») (Op Add [Var Local «off»; Var Local «len»]))
       (Seq (Annot «location» «(32:4 32:22)»)
            (Assign Local «result» (Const 0xFFFFFFFFw)))
       (Seq (Annot «location» «(UNKNOWN 40:15)»)
            (Dec «acc» One (Const 0w)
               (Seq (Annot «location» «(UNKNOWN 40:15)»)
                    (Dec «i» One (Const 0w)
                       (Seq
                          (Seq (Annot «location» «(36:10 38:13)») digLoop)
                          (Seq (Annot «location» «(40:4 40:15)»)
                               (Assign Local «result» (Var Local «acc»))))))))
End

(* ---------------------------------------------------------------------------
   The state relation at the point where alen/off/len are in locals, `result`
   is declared, and the arena is in memory (memRel).  Signed-range side
   conditions on the sizes (the bounds test is the SIGNED `Cmp Less`).
   --------------------------------------------------------------------------- *)
Definition coreRel_def:
  coreRel (a:num list) off len (buf:word64) r0
          (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «alen»   = SOME (ValWord (n2w (LENGTH a))) /\
    FLOOKUP s.locals «off»    = SOME (ValWord (n2w off)) /\
    FLOOKUP s.locals «len»    = SOME (ValWord (n2w len)) /\
    FLOOKUP s.locals «buf»    = SOME (ValWord buf) /\
    FLOOKUP s.locals «result» = SOME (ValWord r0) /\
    memRel a buf s /\
    LENGTH a < 2n ** 63 /\ off + len < 2n ** 63 /\ EVERY (\x. x < 256) a
End

(* The bounds guard: real `panSem$eval` = 1w exactly when the Lean spec is
   out-of-bounds (boundScan = NONE).  (C1's `eval_bounds_expr`, re-proved.) *)
Theorem eval_core_guard:
  coreRel a off len buf r0 s ==>
    eval s (Cmp Less (Var Local «alen»)
                     (Op Add [Var Local «off»; Var Local «len»]))
      = SOME (ValWord (if boundScan a off len = NONE then 1w else 0w))
Proof
  strip_tac >> fs [coreRel_def] >>
  `(n2w (LENGTH a):word64 < n2w (off + len)) = (boundScan a off len = NONE)`
     by (`n2w (LENGTH a):word64 < n2w (off + len) <=> LENGTH a < off + len`
            by (irule signed_lt_n2w64 >> fs []) >>
         rw [boundScan_def] >> fs [NOT_LESS_EQUAL]) >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, word_add_n2w,
        asmTheory.word_cmp_def] >>
  fs []
QED

(* ---------------------------------------------------------------------------
   LINK A for the whole decision+digest core: real `panSem$evaluate` of the
   emitted `If` (with the genuine scan loop) writes EXACTLY the Lean spec's
   encoded result word `n2w (c0_encode (boundScan a off len))` into «result».
   --------------------------------------------------------------------------- *)
Theorem evaluate_innerCore:
  coreRel a off len buf r0 s /\ len <= s.clock ==>
  ?s'. evaluate (innerCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «result»
         = SOME (ValWord (n2w (c0_encode (boundScan a off len))))
Proof
  strip_tac >>
  drule eval_core_guard >> strip_tac >>
  Cases_on `boundScan a off len = NONE`
  >- (
    (* OUT of bounds: guard 1w, then-arm writes the sentinel 0xFFFFFFFF. *)
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
    simp [Abbr `sR`, set_var_def, FLOOKUP_UPDATE, c0_encode_def]) >>
  (* IN bounds: guard 0w, else-arm runs the scan loop; result := digest. *)
  `off + len <= LENGTH a` by (Cases_on `off + len <= LENGTH a` >> fs [boundScan_def]) >>
  `evaluate (Annot «location» «(UNKNOWN 40:15)», s) = (NONE, s)` by simp [evaluate_def] >>
  (* two nested Decs: acc:=0 then i:=0 *)
  qabbrev_tac `s1 = s with locals := s.locals |+ («acc», ValWord 0w)` >>
  qabbrev_tac `s2 = s1 with locals := s1.locals |+ («i», ValWord 0w)` >>
  `s1.clock = s.clock /\ s2.clock = s.clock` by simp [Abbr `s1`, Abbr `s2`] >>
  (* disequalities *)
  `«acc» <> «i» /\ «acc» <> «len» /\ «acc» <> «buf» /\ «acc» <> «off» /\
   «acc» <> «result» /\ «i» <> «len» /\ «i» <> «buf» /\ «i» <> «off» /\
   «i» <> «result»` by EVAL_TAC >>
  (* digInv holds at s2 (fresh acc=0, i=0; outer locals + memory preserved) *)
  `digInv a off buf len 0 0 s2`
     by (simp [digInv_def, Abbr `s2`, Abbr `s1`, FLOOKUP_UPDATE] >>
         fs [coreRel_def, memRel_def, FLOOKUP_UPDATE]) >>
  `len <= s2.clock` by fs [] >>
  drule_all digLoop_refines_scanFrom >> strip_tac >>
  (* s' = the loop exit; call it sL.  «acc» = n2w (dscan a off len 0). *)
  qmatch_asmsub_rename_tac `evaluate (digLoop, s2) = (NONE, sL)` >>
  `sL.clock <= s2.clock` by (imp_res_tac evaluate_clock >> fs []) >>
  (* Assign «result» := «acc» at sL.  «result» survived the loop (frame). *)
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
  (* iBody = Seq (Seq Annot digLoop) (Seq Annot (Assign result acc)) at s2 -> sA *)
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
  (* Dec «i» (Const 0w) iBody at s1: run at s2, restore «i» *)
  qabbrev_tac `sI = sA with locals := res_var sA.locals («i», FLOOKUP s1.locals «i»)` >>
  `s1 with locals := s1.locals |+ («i», ValWord 0w) = s2` by simp [Abbr `s2`] >>
  `evaluate (Dec «i» One (Const 0w)
       (Seq (Seq (Annot «location» «(36:10 38:13)») digLoop)
            (Seq (Annot «location» «(40:4 40:15)»)
                 (Assign Local «result» (Var Local «acc»)))), s1) = (NONE, sI)`
     by (simp [Once evaluate_def, eval_def, shape_of_def, Abbr `sI`]) >>
  (* accBody = Seq Annot (Dec i ...) at s1 -> sI *)
  `evaluate (Annot «location» «(UNKNOWN 40:15)», s1) = (NONE, s1)` by simp [evaluate_def] >>
  `evaluate (Seq (Annot «location» «(UNKNOWN 40:15)»)
       (Dec «i» One (Const 0w)
          (Seq (Seq (Annot «location» «(36:10 38:13)») digLoop)
               (Seq (Annot «location» «(40:4 40:15)»)
                    (Assign Local «result» (Var Local «acc»))))), s1) = (NONE, sI)`
     by (irule Seq_NONE_le >> qexists_tac `s1` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE fs [])) >>
  (* Dec «acc» (Const 0w) accBody at s: run at s1, restore «acc» *)
  qabbrev_tac `sAcc = sI with locals := res_var sI.locals («acc», FLOOKUP s.locals «acc»)` >>
  `s with locals := s.locals |+ («acc», ValWord 0w) = s1` by simp [Abbr `s1`] >>
  `evaluate (Dec «acc» One (Const 0w)
       (Seq (Annot «location» «(UNKNOWN 40:15)»)
            (Dec «i» One (Const 0w)
               (Seq (Seq (Annot «location» «(36:10 38:13)») digLoop)
                    (Seq (Annot «location» «(40:4 40:15)»)
                         (Assign Local «result» (Var Local «acc»)))))), s) = (NONE, sAcc)`
     by (simp [Once evaluate_def, eval_def, shape_of_def, Abbr `sAcc`]) >>
  (* else-arm = Seq Annot (Dec acc ...) at s -> sAcc *)
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
  (* «result» survives both Dec restores (result <> i, result <> acc) and
     equals the digest = c0_encode (SOME (dscan a off len 0)). *)
  `«result» <> «i» /\ «result» <> «acc»` by EVAL_TAC >>
  `FLOOKUP sAcc.locals «result» = FLOOKUP sA.locals «result»`
     by (simp [Abbr `sAcc`, Abbr `sI`, FLOOKUP_res_var_neq]) >>
  `FLOOKUP sA.locals «result» = SOME (ValWord (n2w (dscan a off len 0)))`
     by simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  `boundScan a off len = SOME (dscan a off len 0)` by fs [boundScan_def] >>
  simp [c0_encode_def]
QED

val _ = export_theory ();
