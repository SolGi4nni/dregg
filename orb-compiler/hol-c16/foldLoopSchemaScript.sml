(* ===========================================================================
   C16 probe — THE FOLD-LOOP SCHEMA (reusable, program-agnostic).

   The bounded-fold-over-array loop class named in C14 §4.3 / the boundScan
   `digInv` FOLDL schema.  ONE theorem, proven ONCE, captures the loop invariant
   `acc_i = FOLDL accf acc0 (first i bytes)` and the clocked-`While` induction, so
   a NEW fold-loop primitive discharges its whole Link-A loop core from a SINGLE
   per-step obligation `body_step` (one iteration of the emitted body updates the
   accumulator by `accf`) — NOT boundScan's 629-line hand-derivation.

   The accumulator is a machine word (`word64`), so the fold is EXACT with no
   n2w-faithfulness side condition.  Reuses the C5/C6 clocked-loop machinery
   (`memRel`, `w2w_byte`, `fix_clock_id`, `DROP_EL_CONS_local`), re-declared here
   so the schema is self-contained (no c2/c6work theory-hash coupling), and
   `signed_lt_n2w64` from the C15 program-agnostic `panAuto` theory.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory bitTheory wordsTheory wordsLib
     finite_mapTheory;
open panLangTheory panSemTheory;
open panAutoTheory;        (* signed_lt_n2w64 *)

val _ = new_theory "foldLoopSchema";

(* ---- re-declared C5/C6 loop machinery (self-contained) ---- *)
Definition memRel_def:
  memRel (input:num list) (bs:word64) (s:(64,'ffi) panSem$state) <=>
    !j. j < LENGTH input ==>
        mem_load_byte s.memory s.memaddrs s.be (bs + n2w j)
          = SOME ((n2w (EL j input)):word8)
End

Theorem w2w_byte:
  !x. x < 256 ==> (w2w ((n2w x):word8) : word64) = n2w x
Proof
  rw [w2w_def, w2n_n2w] >> `dimword (:8) = 256` by EVAL_TAC >> fs [] >>
  `x MOD 256 = x` by (irule LESS_MOD >> fs []) >> fs []
QED

Theorem DROP_EL_CONS_local:
  !n l. n < LENGTH l ==> DROP n l = EL n l :: DROP (SUC n) l
Proof
  Induct >> Cases_on `l` >> fs []
QED

Theorem fix_clock_id:
  !old res ns. ns.clock <= old.clock ==> fix_clock old (res,ns) = (res,ns)
Proof
  rw [fix_clock_def] >> `~(old.clock < ns.clock)` by fs [] >>
  simp [state_component_equality]
QED

Theorem Seq_NONE:
  !p1 p2 s sa sb.
    evaluate (p1,s) = (NONE,sa) /\ sa.clock = s.clock /\
    evaluate (p2,sa) = (NONE,sb) ==>
    evaluate (Seq p1 p2, s) = (NONE, sb)
Proof
  rpt strip_tac >> simp [evaluate_def] >>
  `fix_clock s (evaluate (p1,s)) = (NONE, sa)`
     by (`~(s.clock < sa.clock)` by fs [] >>
         simp [fix_clock_def, state_component_equality]) >>
  simp []
QED

(* ---- the emitted fold guard: the SIGNED `i < len` Pancake `<` compiles to ---- *)
Definition foldGuard_def:
  foldGuard = Cmp Less (Var Local «i») (Var Local «len»)
End

(* ---- THE SCHEMA INVARIANT: locals pinned, byte memory related; the running
   accumulator is a free word64 (its FOLDL value is derived, not assumed). ---- *)
Definition foldInv_def:
  foldInv (input:num list) (bs:word64) (i:num) (acc:word64)
          (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «i»    = SOME (ValWord (n2w i)) /\
    FLOOKUP s.locals «acc»  = SOME (ValWord acc) /\
    FLOOKUP s.locals «len»  = SOME (ValWord (n2w (LENGTH input))) /\
    FLOOKUP s.locals «base» = SOME (ValWord bs) /\
    (?bb. FLOOKUP s.locals «b» = SOME (ValWord bb)) /\
    memRel input bs s /\ i <= LENGTH input /\ LENGTH input < 2n ** 63 /\
    EVERY (\x. x < 256) input
End

Theorem foldInv_clock:
  foldInv input bs i acc s ==> foldInv input bs i acc (s with clock := ck)
Proof
  rw [foldInv_def, memRel_def]
QED

(* the guard evaluates to 1w exactly while i < len (signed order = nat order) *)
Theorem eval_foldGuard:
  foldInv input bs i acc s ==>
    eval s foldGuard = SOME (ValWord (if i < LENGTH input then 1w else 0w))
Proof
  strip_tac >>
  `FLOOKUP s.locals «i» = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals «len» = SOME (ValWord (n2w (LENGTH input))) /\
   i <= LENGTH input /\ LENGTH input < 2n ** 63` by fs [foldInv_def] >>
  `i < 2n ** 63` by (irule LESS_EQ_LESS_TRANS >> qexists_tac `LENGTH input` >> fs []) >>
  `(n2w i:word64 < n2w (LENGTH input)) = (i < LENGTH input)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [foldGuard_def, eval_def, asmTheory.word_cmp_def]
QED

(* the per-iteration read of the i-th byte (a reusable helper for the fill-in) *)
Theorem eval_foldByte:
  foldInv input bs i acc s /\ i < LENGTH input ==>
    eval s (LoadByte (Op Add [Var Local «base»; Var Local «i»]))
      = SOME (ValWord ((n2w (EL i input)):word64))
Proof
  strip_tac >>
  `EL i input < 256` by (fs [foldInv_def, EVERY_EL]) >>
  `mem_load_byte s.memory s.memaddrs s.be (bs + n2w i)
      = SOME ((n2w (EL i input)):word8)` by (fs [foldInv_def, memRel_def]) >>
  fs [foldInv_def] >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, WORD_ADD_0, w2w_byte]
QED

(* ===========================================================================
   THE SCHEMA — the clocked-`While` fold induction.  From ONE per-step obligation
   (`body_step`: an iteration updates `acc` by `accf acc (n2w byte)` and preserves
   the invariant + clock), the whole bounded loop refines to the FOLDL over the
   remaining bytes.  Program-agnostic in ⟨accf, body⟩.
   =========================================================================== *)
(* ---- ONE loop iteration : the body_step hypothesis, ISOLATED so it does not
   compete with the `foldLoop_bounded` induction hypothesis.  Given the per-step
   obligation, an iteration threads the emitted `While` to the post-body state and
   advances the fold accumulator by `accf acc (n2w byte)`.  The states share ONE
   ffi type variable (`'ffi`) so the instantiated pre/post conditions unify. ---- *)
Theorem foldLoop_iter:
  !accf body input bs.
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (body, s) = (NONE, s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) ==>
    !i acc (s:(64,'ffi) state).
      foldInv input bs i acc s /\ i < LENGTH input /\ s.clock <> 0 ==>
      ?s2. evaluate (While foldGuard body, s) = evaluate (While foldGuard body, s2) /\
           foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2 /\
           s2.clock = s.clock - 1
Proof
  ntac 4 gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `eval s foldGuard = SOME (ValWord 1w)` by (drule eval_foldGuard >> fs []) >>
  `foldInv input bs i acc (dec_clock s)`
     by (simp [dec_clock_def] >> irule foldInv_clock >> fs []) >>
  first_assum (qspecl_then [`i`,`acc`,`dec_clock s`] mp_tac) >>
  impl_tac >- fs [] >> strip_tac >> qexists_tac `s2` >>
  `s2.clock = s.clock - 1` by fs [dec_clock_def] >>
  (* unfold the LEFT While one step; the clean evaluate_def While clause threads
     the body result with no residual fix_clock (s2.clock <= dec_clock s.clock) *)
  `evaluate (While foldGuard body, s) = evaluate (While foldGuard body, s2)`
     by (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >> simp []) >>
  fs []
QED

Theorem foldLoop_bounded:
  !accf body input bs.
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (body, s) = (NONE, s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) ==>
    !k i acc (s:(64,'ffi) state).
      foldInv input bs i acc s /\ LENGTH input - i <= k /\ LENGTH input - i <= s.clock ==>
      ?s'. evaluate (While foldGuard body, s) = (NONE, s') /\
           FLOOKUP s'.locals «acc» =
             SOME (ValWord (FOLDL accf acc (MAP (\c. (n2w c):word64) (DROP i input))))
Proof
  ntac 4 gen_tac >>
  (* keep the per-step obligation as a NAMED hypothesis (`bstep`), OUT of the
     assumption list, so the sole `!i acc s` assumption in the step is the IH *)
  disch_then (fn bstep =>
    Induct_on `k` >| [
      ((* k = 0 : i = LENGTH input, guard false, exit *)
       rpt strip_tac >>
       `i = LENGTH input` by fs [foldInv_def] >>
       `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
       qexists_tac `s` >>
       `evaluate (While foldGuard body, s) = (NONE, s)` by (simp [Once evaluate_def]) >>
       `DROP i input = []` by (`LENGTH input <= i` by fs [] >> simp [DROP_LENGTH_TOO_LONG]) >>
       fs [foldInv_def]),
      ((* SUC k *)
       rpt strip_tac >> Cases_on `i < LENGTH input` >| [
         ((* an iteration runs : discharge it with foldLoop_iter *)
          `s.clock <> 0` by fs [] >>
          mp_tac (MATCH_MP foldLoop_iter bstep) >>
          disch_then (qspecl_then [`i`,`acc`,`s`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >>
          `LENGTH input - (i + 1) <= k` by fs [] >>
          `LENGTH input - (i + 1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`accf acc (n2w (EL i input):word64)`,`s2`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >>
          qexists_tac `s'` >>
          `DROP i input = EL i input :: DROP (SUC i) input`
             by (irule DROP_EL_CONS_local >> fs []) >>
          gvs [ADD1]),
         ((* guard false at s: i = LENGTH input, terminal *)
          `i = LENGTH input` by fs [foldInv_def] >>
          `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
          qexists_tac `s` >>
          `evaluate (While foldGuard body, s) = (NONE, s)` by (simp [Once evaluate_def]) >>
          `DROP i input = []` by (`LENGTH input <= i` by fs [] >> simp [DROP_LENGTH_TOO_LONG]) >>
          fs [foldInv_def])
       ])
    ])
QED

(* ---- THE HEADLINE fill-in point: from a fresh (i=0, acc=init) state with clock
   >= |input|, the emitted fold `While` computes EXACTLY `FOLDL accf init` over the
   whole byte array — the Lean spec of ANY running-accumulator scan. ---- *)
Theorem foldLoop_refines:
  !accf body input bs.
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (body, s) = (NONE, s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) ==>
    !init (s:(64,'ffi) state).
      foldInv input bs 0 init s /\ LENGTH input <= s.clock ==>
      ?s'. evaluate (While foldGuard body, s) = (NONE, s') /\
           FLOOKUP s'.locals «acc» =
             SOME (ValWord (FOLDL accf init (MAP (\c. (n2w c):word64) input)))
Proof
  rpt strip_tac >>
  drule foldLoop_bounded >>
  disch_then (qspecl_then [`LENGTH input`,`0`,`init`,`s`] mp_tac) >>
  impl_tac >- (fs []) >> simp []
QED

(* ===========================================================================
   DEMONSTRATION — a NEW fold-loop primitive (running byte-SUM) closes its whole
   Link-A loop core through the schema with ONE per-step obligation (`sumBody_step`,
   ~8 tactic lines), NOT boundScan's 629-line hand-derivation of a loop invariant.
   The emitted body reads byte[base+i], adds it into `acc`, and advances `i`; the
   accumulator step is `sumAcc a b = a + b`, so the whole loop computes exactly
   `FOLDL sumAcc init (MAP n2w input)` = init + the byte sum.
   =========================================================================== *)
Definition sumAcc_def:
  sumAcc (a:word64) (b:word64) = a + b
End

Definition sumBody_def:
  sumBody =
    Seq (Assign Local «b» (LoadByte (Op Add [Var Local «base»; Var Local «i»])))
   (Seq (Assign Local «acc» (Op Add [Var Local «acc»; Var Local «b»]))
        (Assign Local «i»   (Op Add [Var Local «i»; Const 1w])))
End

(* THE per-step fill-in : one iteration advances the fold by `sumAcc`. *)
Theorem sumBody_step:
  !i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
    ?s2. evaluate (sumBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         foldInv input bs (i+1) (sumAcc acc (n2w (EL i input):word64)) s2
Proof
  rpt strip_tac >>
  `FLOOKUP s.locals «base» = SOME (ValWord bs) /\
   FLOOKUP s.locals «i»    = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals «acc»  = SOME (ValWord acc) /\
   FLOOKUP s.locals «len»  = SOME (ValWord (n2w (LENGTH input)))` by fs [foldInv_def] >>
  `?bb. FLOOKUP s.locals «b» = SOME (ValWord bb)` by fs [foldInv_def] >>
  `eval s (LoadByte (Op Add [Var Local «base»; Var Local «i»])) =
     SOME (ValWord (n2w (EL i input):word64))` by (drule_all eval_foldByte >> simp []) >>
  qexists_tac `set_var «i» (ValWord (n2w i + 1w))
    (set_var «acc» (ValWord (acc + n2w (EL i input)))
    (set_var «b»   (ValWord (n2w (EL i input))) s))` >>
  simp [sumBody_def, evaluate_def, eval_def, is_valid_value_simps, shape_of_def,
        set_var_def, FLOOKUP_UPDATE, wordLangTheory.word_op_def, OPT_MMAP_def] >>
  simp [foldInv_def, sumAcc_def, memRel_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  fs [foldInv_def, memRel_def]
QED

(* THE closed loop core : the emitted byte-sum `While` computes EXACTLY the Lean
   fold `FOLDL sumAcc init` over the whole byte array — derived from the schema by
   discharging its single obligation with `sumBody_step`. *)
Theorem sumLoop_refines:
  !input bs init (s:(64,'ffi) state).
    foldInv input bs 0 init s /\ LENGTH input <= s.clock ==>
    ?s'. evaluate (While foldGuard sumBody, s) = (NONE, s') /\
         FLOOKUP s'.locals «acc» =
           SOME (ValWord (FOLDL sumAcc init (MAP (\c. (n2w c):word64) input)))
Proof
  rpt strip_tac >>
  `!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
     ?s2. evaluate (sumBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
          foldInv input bs (i+1) (sumAcc acc (n2w (EL i input):word64)) s2`
     by (rpt strip_tac >> irule sumBody_step >> fs []) >>
  drule foldLoop_refines >>
  disch_then (qspecl_then [`init`,`s`] mp_tac) >>
  impl_tac >- fs [] >> simp []
QED

val _ = export_theory ();
