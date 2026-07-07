(* ===========================================================================
   C12 probe, PART 1 — LINK A for the boundScan DIGEST scan-`While` loop.

   This discharges the exact item C1-REPORT §4-A-2 named UNCLOSED: the scan
   `While` loop invariant of `boundscan.pnk` — the rolling 24-bit digest
   `acc := (acc*31 + byte) & 0xFFFFFF` folded over the viewed bytes — proved
   against the REAL Pancake source semantics `panSem$evaluate`.

   The loop body / guard here are the EXACT emitted terms extracted from the
   CakeML-verified parser output `boundScanProg` (functions boundScanProg,
   the `main` body's `While`) — Annot location nodes, `Panop Mul`, `Op And`,
   the 3-operand `Op Add` LoadByte address, all verbatim — so this theorem is
   about the actual compiled program's loop, not a hand-simplified twin.

   Reuses the C3/C5/C6 loop machinery verbatim (opened from
   machineLoopLinkATheory / machineStepLinkATheory): `memRel` (the LoadByte
   byte-memory relation), `Seq_NONE`, `w2w_byte`, `signed_lt_n2w64`.  What is
   NEW is the DIGEST invariant (`digInv`) and its fold refinement against the
   Lean spec `scanFrom` (`dscan` here, byte-identical to model/BoundScan.lean
   `C0.scanFrom` and hol-c1's `scanFrom`).
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory;
open machineStepLinkATheory;   (* signed_lt_n2w64                              *)
open machineLoopLinkATheory;   (* memRel, memRel_def, Seq_NONE, w2w_byte       *)

val _ = new_theory "boundScanDigestLinkA";

(* ---------------------------------------------------------------------------
   The Lean SPEC digest, re-declared in HOL (byte-identical to C0.step /
   C0.scanFrom and to hol-c1's step/scanFrom).
   --------------------------------------------------------------------------- *)
Definition dstep_def:
  dstep (acc:num) (b:num) = (acc * 31 + b) MOD 16777216
End

Definition dscan_def:
  (dscan a off 0 acc = acc) /\
  (dscan a off (SUC n) acc = dscan a (off + 1) n (dstep acc (EL off a)))
End

(* dstep lands in the 24-bit range; the invariant carries `acc < 2^24`. *)
Theorem dstep_lt:
  !acc b. dstep acc b < 16777216
Proof
  rw [dstep_def]
QED

(* ---------------------------------------------------------------------------
   The mask lemma: `& 0xFFFFFF` on a 64-bit word is `MOD 2^24` on the nat.
   --------------------------------------------------------------------------- *)
Theorem mask24:
  !x. (n2w x : word64) && 0xFFFFFFw = n2w (x MOD 16777216)
Proof
  strip_tac >>
  `(0xFFFFFFw:word64) = n2w (2 ** 24 - 1)` by EVAL_TAC >>
  `(16777216:num) = 2 ** 24` by EVAL_TAC >>
  asm_rewrite_tac [] >>
  MATCH_ACCEPT_TAC WORD_AND_EXP_SUB1
QED

(* the srw simpset normalises `w && lit` to `lit && w`; the commuted form. *)
Theorem mask24':
  !x. (0xFFFFFFw:word64) && n2w x = n2w (x MOD 16777216)
Proof
  metis_tac [mask24, WORD_AND_COMM]
QED

(* ---------------------------------------------------------------------------
   The IMPLEMENTATION: the emitted digest `While`, VERBATIM from boundScanProg.
   --------------------------------------------------------------------------- *)
Definition digBody_def:
  digBody =
    Seq
      (Seq (Annot «location» «(37:6 37:45)»)
           (Assign Local «acc»
              (Op And
                 [Op Add
                    [Panop Mul [Var Local «acc»; Const 31w];
                     LoadByte
                       (Op Add [Var Local «buf»; Var Local «off»;
                                Var Local «i»])];
                  Const 0xFFFFFFw])))
      (Seq (Annot «location» «(38:6 38:13)»)
           (Assign Local «i» (Op Add [Var Local «i»; Const 1w])))
End

Definition digLoop_def:
  digLoop =
    While (Cmp Less (Var Local «i») (Var Local «len»)) digBody
End

(* ---------------------------------------------------------------------------
   The digest loop invariant.  `a` is the WHOLE arena; the view is `(off,len)`;
   `acc`/`i` are the running digest and index; `buf` is the arena base address
   (`memRel a buf s` reads `EL j a` at `buf + n2w j`).  Side conditions: the
   view lies in-bounds (`off + len <= LENGTH a`), sizes fit the signed range
   (guard is the SIGNED `Cmp Less`), bytes are genuine bytes.
   --------------------------------------------------------------------------- *)
Definition digInv_def:
  digInv (a:num list) (off:num) (buf:word64) (len:num) (acc:num) (i:num)
         (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «acc» = SOME (ValWord (n2w acc)) /\
    FLOOKUP s.locals «i»   = SOME (ValWord (n2w i)) /\
    FLOOKUP s.locals «len» = SOME (ValWord (n2w len)) /\
    FLOOKUP s.locals «buf» = SOME (ValWord buf) /\
    FLOOKUP s.locals «off» = SOME (ValWord (n2w off)) /\
    memRel a buf s /\
    acc < 16777216 /\ i <= len /\ off + len <= LENGTH a /\
    len < 2n ** 63 /\ EVERY (\x. x < 256) a
End

Theorem digInv_clock:
  digInv a off buf len acc i s ==> digInv a off buf len acc i (s with clock := ck)
Proof
  rw [digInv_def, memRel_def]
QED

(* ---------------------------------------------------------------------------
   The loop guard: real `panSem$eval` of `i < len` = 1w exactly in range.
   --------------------------------------------------------------------------- *)
Theorem eval_dig_guard:
  digInv a off buf len acc i s ==>
    eval s (Cmp Less (Var Local «i») (Var Local «len»))
      = SOME (ValWord (if i < len then 1w else 0w))
Proof
  strip_tac >>
  fs [digInv_def] >>
  `i < 2n ** 63` by (irule LESS_EQ_LESS_TRANS >> qexists_tac `len` >> fs []) >>
  `(n2w i:word64 < n2w len) = (i < len)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [eval_def, asmTheory.word_cmp_def]
QED

(* ---------------------------------------------------------------------------
   The per-iteration digest update: real `panSem$eval` of the emitted
   `(acc*31 + byte) & 0xFFFFFF` expression = `n2w (dstep acc (EL (off+i) a))`.
   Combines the memory relation (byte load), the word arithmetic, and `mask24`.
   --------------------------------------------------------------------------- *)
Theorem eval_dig_update:
  digInv a off buf len acc i s /\ i < len ==>
    eval s
      (Op And
         [Op Add
            [Panop Mul [Var Local «acc»; Const 31w];
             LoadByte (Op Add [Var Local «buf»; Var Local «off»;
                               Var Local «i»])];
          Const 0xFFFFFFw])
      = SOME (ValWord (n2w (dstep acc (EL (off + i) a))))
Proof
  strip_tac >>
  `off + i < LENGTH a` by fs [digInv_def] >>
  `EL (off + i) a < 256` by (fs [digInv_def, EVERY_EL]) >>
  `mem_load_byte s.memory s.memaddrs s.be (buf + n2w (off + i))
      = SOME ((n2w (EL (off + i) a)):word8)`
     by (fs [digInv_def, memRel_def]) >>
  `FLOOKUP s.locals «acc» = SOME (ValWord (n2w acc)) /\
   FLOOKUP s.locals «buf» = SOME (ValWord buf) /\
   FLOOKUP s.locals «off» = SOME (ValWord (n2w off)) /\
   FLOOKUP s.locals «i»   = SOME (ValWord (n2w i))` by fs [digInv_def] >>
  (* the 3-operand address folds to buf + n2w (off+i) *)
  `(buf + n2w off + n2w i : word64) = buf + n2w (off + i)`
     by (once_rewrite_tac [GSYM WORD_ADD_ASSOC] >> simp [word_add_n2w]) >>
  (* the byte load *)
  `eval s (LoadByte (Op Add [Var Local «buf»; Var Local «off»;
                             Var Local «i»]))
     = SOME (ValWord ((n2w (EL (off + i) a)):word64))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, WORD_ADD_0,
               w2w_byte] >> fs [w2w_byte]) >>
  (* the multiply, add, and mask *)
  `(31w:word64) = n2w 31` by EVAL_TAC >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, pan_op_def,
        word_mul_n2w, word_add_n2w, WORD_ADD_0] >>
  simp [mask24, mask24', dstep_def]
QED

(* ---------------------------------------------------------------------------
   One loop body iteration: reads the byte, updates «acc» to the next digest,
   advances «i», preserves the clock, and re-establishes `digInv` at
   (dstep acc (EL (off+i) a), i+1).  The Annot location nodes are no-ops
   (`evaluate (Annot _ _,s) = (NONE,s)`), sequenced by `Seq_NONE`.
   --------------------------------------------------------------------------- *)
Theorem evaluate_digBody:
  digInv a off buf len acc i s /\ i < len ==>
    ?s2. evaluate (digBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         digInv a off buf len (dstep acc (EL (off + i) a)) (i + 1) s2 /\
         (!v. v <> «acc» /\ v <> «i» ==>
              FLOOKUP s2.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >>
  drule_all eval_dig_update >> strip_tac >>
  `off + i < LENGTH a` by fs [digInv_def] >>
  `«acc» <> «i» /\ «i» <> «acc»` by EVAL_TAC >>
  `FLOOKUP s.locals «acc» = SOME (ValWord (n2w acc)) /\
   FLOOKUP s.locals «i»   = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals «len» = SOME (ValWord (n2w len)) /\
   FLOOKUP s.locals «buf» = SOME (ValWord buf) /\
   FLOOKUP s.locals «off» = SOME (ValWord (n2w off)) /\
   memRel a buf s /\ len < 2n ** 63 /\ EVERY (\x. x < 256) a`
     by fs [digInv_def] >>
  qabbrev_tac `nacc = dstep acc (EL (off + i) a)` >>
  qabbrev_tac `sA = set_var «acc» (ValWord (n2w nacc)) s` >>
  qabbrev_tac `sB = set_var «i» (ValWord (n2w (i + 1))) sA` >>
  `sA.clock = s.clock` by simp [Abbr `sA`, set_var_def] >>
  `sB.clock = sA.clock` by simp [Abbr `sB`, set_var_def] >>
  (* Annot no-ops preserve state *)
  `evaluate (Annot «location» «(37:6 37:45)», s) = (NONE, s)`
     by simp [evaluate_def] >>
  `evaluate (Annot «location» «(38:6 38:13)», sA) = (NONE, sA)`
     by simp [evaluate_def] >>
  (* Assign «acc» = the digest update *)
  `evaluate (Assign Local «acc»
       (Op And
          [Op Add
             [Panop Mul [Var Local «acc»; Const 31w];
              LoadByte (Op Add [Var Local «buf»; Var Local «off»;
                                Var Local «i»])];
           Const 0xFFFFFFw]), s) = (NONE, sA)`
     by (simp [Once evaluate_def, Abbr `sA`] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  (* Assign «i» = i + 1 *)
  `FLOOKUP sA.locals «i» = SOME (ValWord (n2w i))`
     by simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  `evaluate (Assign Local «i» (Op Add [Var Local «i»; Const 1w]), sA)
     = (NONE, sB)`
     by (simp [Once evaluate_def, eval_def, OPT_MMAP_def,
               wordLangTheory.word_op_def, word_add_n2w, Abbr `sB`] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  (* assemble the Seq (Annot; acc-assign) ; (Annot; i-assign) *)
  `evaluate (Seq (Annot «location» «(37:6 37:45)»)
       (Assign Local «acc»
          (Op And
             [Op Add
                [Panop Mul [Var Local «acc»; Const 31w];
                 LoadByte (Op Add [Var Local «buf»; Var Local «off»;
                                   Var Local «i»])];
              Const 0xFFFFFFw])), s) = (NONE, sA)`
     by (irule Seq_NONE >> qexists_tac `s` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  `evaluate (Seq (Annot «location» «(38:6 38:13)»)
       (Assign Local «i» (Op Add [Var Local «i»; Const 1w])), sA)
     = (NONE, sB)`
     by (irule Seq_NONE >> qexists_tac `sA` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  `evaluate (digBody, s) = (NONE, sB)`
     by (simp [digBody_def] >> irule Seq_NONE >> qexists_tac `sA` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `sB` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp [] >>
  conj_tac >- (
    (* re-establish digInv at (nacc, i+1) *)
    `nacc < 16777216` by (simp [Abbr `nacc`] >> metis_tac [dstep_lt]) >>
    `sB.memory = s.memory /\ sB.memaddrs = s.memaddrs /\ sB.be = s.be`
       by simp [Abbr `sB`, Abbr `sA`, set_var_def] >>
    `memRel a buf sB` by fs [memRel_def] >>
    `i + 1 <= len` by fs [] >>
    simp [digInv_def, Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
    fs [digInv_def]) >>
  (* the locals frame: the body writes only «acc» and «i» *)
  rpt strip_tac >>
  simp [Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE]
QED

(* One emitted `While` iteration: reduce `evaluate (digLoop, s)` to
   `evaluate (digLoop, s2)` at the next (acc,i), spending one clock tick. *)
Theorem digLoop_unfold:
  digInv a off buf len acc i s /\ i < len /\ s.clock <> 0 ==>
  ?s2. evaluate (digLoop, s) = evaluate (digLoop, s2) /\
       digInv a off buf len (dstep acc (EL (off + i) a)) (i + 1) s2 /\
       s2.clock = s.clock - 1 /\
       (!v. v <> «acc» /\ v <> «i» ==> FLOOKUP s2.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >>
  `eval s (Cmp Less (Var Local «i») (Var Local «len»)) = SOME (ValWord 1w)`
     by (drule eval_dig_guard >> fs []) >>
  `digInv a off buf len acc i (dec_clock s)`
     by (simp [dec_clock_def] >> irule digInv_clock >> fs []) >>
  `(dec_clock s).locals = s.locals` by simp [dec_clock_def] >>
  drule_all evaluate_digBody >> strip_tac >>
  qexists_tac `s2` >>
  conj_tac
  >- (CONV_TAC (LAND_CONV
        (ONCE_REWRITE_CONV [digLoop_def] THENC
         ONCE_REWRITE_CONV [evaluate_def])) >>
      simp [GSYM digLoop_def]) >>
  conj_tac >- fs [] >>
  conj_tac >- fs [dec_clock_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp []
QED

(* One `dscan` unfold: peel the first byte off a non-empty view. *)
Theorem dscan_unfold1:
  !a off n acc.
    0 < n ==> dscan a off n acc = dscan a (off + 1) (n - 1) (dstep acc (EL off a))
Proof
  rpt strip_tac >> Cases_on `n` >> fs [dscan_def]
QED

(* ---------------------------------------------------------------------------
   LINK A FOR THE DIGEST LOOP — the loop-invariant induction over the clocked
   `While`.  With enough clock, running `digLoop` from `(acc,i)` terminates and
   leaves «acc» holding EXACTLY the continued Lean fold `dscan a (off+i) (len-i)
   acc`.  Induction on a bound `k` for the remaining iteration count.
   --------------------------------------------------------------------------- *)
Theorem digLoop_fold_bounded:
  !k a off buf len acc i s.
    digInv a off buf len acc i s /\ len - i <= k /\ len - i <= s.clock ==>
    ?s'. evaluate (digLoop, s) = (NONE, s') /\
         FLOOKUP s'.locals «acc»
           = SOME (ValWord (n2w (dscan a (off + i) (len - i) acc))) /\
         (!v. v <> «acc» /\ v <> «i» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  Induct_on `k`
  >- (
    rpt strip_tac >>
    `~(i < len)` by fs [] >>
    `i = len` by fs [digInv_def] >>
    drule eval_dig_guard >> strip_tac >>
    `len - i = 0` by fs [] >>
    qexists_tac `s` >>
    simp [digLoop_def, Once evaluate_def] >>
    fs [digInv_def, dscan_def]) >>
  rpt strip_tac >>
  Cases_on `i < len`
  >- (
    `s.clock <> 0` by fs [] >>
    drule_all digLoop_unfold >> strip_tac >>
    last_x_assum (qspecl_then
       [`a`,`off`,`buf`,`len`,`dstep acc (EL (off + i) a)`,`i + 1`,`s2`] mp_tac) >>
    impl_tac >- fs [] >>
    strip_tac >>
    qexists_tac `s'` >>
    (* the fold unfolds one step: dscan a (off+i) (len-i) acc =
       dscan a (off+(i+1)) (len-(i+1)) (dstep acc (EL (off+i) a)), matching the IH.
       Proved SELF-CONTAINEDLY (the SUC/arith facts stay inside this block) so the
       final `fs` sees only the clean fold equation, not a `len-i = SUC _` rewrite
       that would otherwise fire first and unmatch it. *)
    `dscan a (off + i) (len - i) acc
       = dscan a (off + (i + 1)) (len - (i + 1)) (dstep acc (EL (off + i) a))`
       by (`0 < len - i` by fs [] >>
           `dscan a (off + i) (len - i) acc
              = dscan a (off + i + 1) (len - i - 1) (dstep acc (EL (off + i) a))`
              by (irule dscan_unfold1 >> fs []) >>
           `off + i + 1 = off + (i + 1)` by DECIDE_TAC >>
           `len - i - 1 = len - (i + 1)` by DECIDE_TAC >>
           fs []) >>
    conj_tac >- fs [] >>
    conj_tac >- fs [] >>
    (* frame: compose the unfold frame (s2 vs s) with the IH frame (s' vs s2) *)
    rpt strip_tac >> res_tac >> fs []) >>
  drule eval_dig_guard >> strip_tac >>
  `i = len` by fs [digInv_def] >>
  `len - i = 0` by fs [] >>
  qexists_tac `s` >>
  simp [digLoop_def, Once evaluate_def] >>
  fs [digInv_def, dscan_def]
QED

(* ---------------------------------------------------------------------------
   The headline, from a fresh loop entry (acc=0, i=0): the emitted digest loop
   computes EXACTLY the Lean spec fold `dscan a off len 0` = `scanFrom a off
   len 0`, given clock >= len.  This is the C1 §4-A-2 deferred loop invariant,
   now discharged against real `panSem$evaluate`.
   --------------------------------------------------------------------------- *)
Theorem digLoop_refines_scanFrom:
  digInv a off buf len 0 0 s /\ len <= s.clock ==>
  ?s'. evaluate (digLoop, s) = (NONE, s') /\
       FLOOKUP s'.locals «acc»
         = SOME (ValWord (n2w (dscan a off len 0))) /\
       (!v. v <> «acc» /\ v <> «i» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >>
  `len - 0 <= len` by fs [] >>
  drule digLoop_fold_bounded >>
  disch_then (qspec_then `len` mp_tac) >>
  impl_tac >- fs [] >>
  simp []
QED

val _ = export_theory ();
