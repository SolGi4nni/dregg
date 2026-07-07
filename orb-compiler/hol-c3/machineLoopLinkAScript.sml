(* ===========================================================================
   C3 probe — LINK A for a LOOP: the fold/scan `While` (C1/C2's UNCLOSED item).

   C1 (`boundScanLinkAScript.sml`) and C2 (`machineStepLinkAScript.sml`) each
   closed Link A for a SINGLE transition against the real Pancake source
   semantics `panSem$evaluate`, and each named the same residual UNCLOSED:

     the fold/scan `While` loop + its per-iteration byte-memory `LoadByte`
     relation — a loop-invariant induction over panSem's CLOCKED `While` clause.

   This file DISCHARGES that loop. We build the machine's stream loop as a real
   `panLang$prog` `While` that (i) `LoadByte`s the next input byte, (ii) runs the
   C2 single-step body `stepBody` (opened from `machineStepLinkATheory` and used
   verbatim — this is the composition mechanism the single-step theorem could not
   demonstrate), and (iii) advances the index. We prove, against real
   `panSem$evaluate`, that running the emitted `While` refines the Lean fold
   `FOLDL mstep` over the input byte stream:

       evaluate (machineLoop, s)  ==>  «c» = n2w (FOLDL mstep c0 input)

   The proof is a loop-invariant induction over the clocked `While`. The
   invariant is `loopInv` — the C2 state relation lifted to the loop:
     * `«c»` holds the running fold `n2w (FOLDL mstep 0 (TAKE i input))` (here we
       carry the running accumulator `c` and prove the residual `DROP i input`),
     * `«i»` is the loop index, `«len»` the length, `«base»` the buffer address,
     * `memRel input bs s` — the byte-memory relation: `panSem`'s word-addressed
       byte memory `mem_load_byte s.memory s.memaddrs s.be (bs + n2w j)` yields
       `n2w (EL j input)`, the j-th model byte, for every in-range j. This is the
       LoadByte relation named UNCLOSED in C1 §4-A-3 / C2 §6, here THREADED
       through the loop (the body writes only locals, so the memory relation is
       an invariant preserved across every iteration).

   The single step `stepBody_refines_step` is the loop BODY; this induction is
   what wraps it. The clock accounting is the substance the single-step theorems
   did not have: each `While` iteration consumes exactly one clock (the body has
   no `Tick`/`While`/`Call`, so it preserves clock), so `LENGTH input - i` clock
   suffices — established as a hypothesis and threaded through the induction.

   Faithfulness note carries over verbatim from C1/C2: Pancake `<` is the SIGNED
   `Cmp Less`, so the guard `i < len` needs the non-negative signed-range side
   condition `LENGTH input < 2^63` (hence `i < 2^63`); discharged by the reused
   `signed_lt_n2w64`.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory;
open machineStepLinkATheory;   (* the C2 single-step Link A, reused verbatim *)

val _ = new_theory "machineLoopLinkA";

(* ---------------------------------------------------------------------------
   Small arithmetic/word helpers.
   --------------------------------------------------------------------------- *)

(* A byte loaded from memory (a word8) widened to the 64-bit machine word is the
   same nat, provided it is a genuine byte (< 256). This is the width side of the
   LoadByte relation. *)
Theorem w2w_byte:
  !x. x < 256 ==> (w2w ((n2w x):word8) : word64) = n2w x
Proof
  rw [w2w_def, w2n_n2w] >>
  `dimword (:8) = 256` by EVAL_TAC >>
  fs [] >>
  `x MOD 256 = x` by (irule LESS_MOD >> fs []) >>
  fs []
QED

(* The list-decomposition the induction turns on: at index i < |l| the residual
   suffix uncons-es into the current element and the next suffix. *)
Theorem DROP_EL_CONS_local:
  !n l. n < LENGTH l ==> DROP n l = EL n l :: DROP (SUC n) l
Proof
  Induct >> Cases_on `l` >> fs []
QED

(* fix_clock is the identity on a result whose clock did not exceed the input
   clock (always true for our body — evaluate never raises the clock). Isolating
   this keeps the clocked-While bookkeeping out of the big simps. *)
Theorem fix_clock_id:
  !old res ns. ns.clock <= old.clock ==> fix_clock old (res,ns) = (res,ns)
Proof
  rw [fix_clock_def] >>
  `~(old.clock < ns.clock)` by fs [] >>
  simp [state_component_equality]
QED

(* Sequencing two clock-preserving NONE-returning statements: the panSem `Seq`
   `fix_clock` collapses to the identity, so the two states just chain. This
   isolates the only subtle bit of the body evaluation (the fix_clock inside
   `evaluate (Seq ...)`). *)
Theorem Seq_NONE:
  !p1 p2 s sa sb.
    evaluate (p1,s) = (NONE,sa) /\ sa.clock = s.clock /\
    evaluate (p2,sa) = (NONE,sb) ==>
    evaluate (Seq p1 p2, s) = (NONE, sb)
Proof
  rpt strip_tac >>
  simp [evaluate_def] >>
  `fix_clock s (evaluate (p1,s)) = (NONE, sa)`
     by (`~(s.clock < sa.clock)` by fs [] >>
         simp [fix_clock_def, state_component_equality]) >>
  simp []
QED

(* ---------------------------------------------------------------------------
   The IMPLEMENTATION: the .pnk stream loop, as a real panLang AST.

     while (i < len) {
       b = ldb (base + i);     // LoadByte at the i-th buffer address
       <stepBody>              // the C2 single-step FSM body (verbatim)
       i = i + 1;
     }

   `stepBody` is IMPORTED from machineStepLinkATheory — the exact term whose
   single-step refinement C2 proved. `Cmp Less` = the SIGNED guard Pancake `<`
   compiles to.
   --------------------------------------------------------------------------- *)
Definition loopBody_def:
  loopBody =
    Seq (Assign Local (strlit "b")
           (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")])))
    (Seq stepBody
         (Assign Local (strlit "i")
            (Op Add [Var Local (strlit "i"); Const (1w:word64)])))
End

Definition machineLoop_def:
  machineLoop =
    While (Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len")))
          loopBody
End

(* ---------------------------------------------------------------------------
   The byte-memory relation (the LoadByte relation, C1 §4-A-3 / C2 §6): real
   `panSem` word-addressed byte memory, read at the i-th buffer address, yields
   the i-th model byte. Stated at `mem_load_byte` — the endianness/packing that
   POPULATES the memory is the FFI's job and stays outside the theorem.
   --------------------------------------------------------------------------- *)
Definition memRel_def:
  memRel (input:num list) (bs:word64) (s:(64,'ffi) panSem$state) <=>
    !j. j < LENGTH input ==>
        mem_load_byte s.memory s.memaddrs s.be (bs + n2w j)
          = SOME ((n2w (EL j input)):word8)
End

(* ---------------------------------------------------------------------------
   The loop invariant: the C2 state relation lifted to the loop. Carries the
   running accumulator `c` at `«c»`, the index `i` at `«i»`, the length and base,
   a declared byte slot `«b»`, the byte-memory relation, and the signed-range +
   byte-range side conditions the guards and step need.
   --------------------------------------------------------------------------- *)
Definition loopInv_def:
  loopInv (input:num list) (bs:word64) (c:num) (i:num)
          (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "c")    = SOME (ValWord (n2w c)) /\
    FLOOKUP s.locals (strlit "i")    = SOME (ValWord (n2w i)) /\
    FLOOKUP s.locals (strlit "len")  = SOME (ValWord (n2w (LENGTH input))) /\
    FLOOKUP s.locals (strlit "base") = SOME (ValWord bs) /\
    (?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)) /\
    memRel input bs s /\
    c <= 255 /\ i <= LENGTH input /\ LENGTH input < 2n ** 63 /\
    EVERY (\x. x < 256) input
End

(* The invariant depends only on locals/memory, not the clock, so lowering the
   clock (what the `While` does each iteration) preserves it. *)
Theorem loopInv_clock:
  loopInv input bs c i s ==> loopInv input bs c i (s with clock := ck)
Proof
  rw [loopInv_def, memRel_def]
QED

(* ---------------------------------------------------------------------------
   The loop guard: real `panSem$eval` of `i < len` = 1w EXACTLY when the index is
   still in range. Reuses `signed_lt_n2w64` (the guard is the SIGNED `Cmp Less`).
   --------------------------------------------------------------------------- *)
Theorem eval_loop_guard:
  loopInv input bs c i s ==>
    eval s (Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len")))
      = SOME (ValWord (if i < LENGTH input then 1w else 0w))
Proof
  strip_tac >>
  fs [loopInv_def] >>
  `i < 2n ** 63` by (irule LESS_EQ_LESS_TRANS >> qexists_tac `LENGTH input` >> fs []) >>
  `(n2w i:word64 < n2w (LENGTH input)) = (i < LENGTH input)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [eval_def, asmTheory.word_cmp_def]
QED

(* ---------------------------------------------------------------------------
   The per-iteration byte read: real `panSem$eval` of the `LoadByte (base + i)`
   returns the i-th model byte, via `memRel` + the width lemma `w2w_byte`.
   --------------------------------------------------------------------------- *)
Theorem eval_loadbyte:
  loopInv input bs c i s /\ i < LENGTH input ==>
    eval s (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")]))
      = SOME (ValWord ((n2w (EL i input)):word64))
Proof
  strip_tac >>
  `EL i input < 256` by (fs [loopInv_def, EVERY_EL]) >>
  `mem_load_byte s.memory s.memaddrs s.be (bs + n2w i)
      = SOME ((n2w (EL i input)):word8)`
     by (fs [loopInv_def, memRel_def]) >>
  fs [loopInv_def] >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, WORD_ADD_0,
        w2w_byte]
QED

(* ---------------------------------------------------------------------------
   The loop BODY, one iteration: real `panSem$evaluate` of `loopBody` reads the
   i-th byte into `«b»`, runs the C2 single step (writing `n2w (mstep c byte)`
   into `«c»` via `evaluate_stepBody`), advances `«i»`, preserves the clock, and
   RE-ESTABLISHES the invariant at `(mstep c byte, i+1)`. This is where the C2
   single-step theorem is COMPOSED: `stepBody`'s refinement is used verbatim as
   the body's middle statement, and the memory relation is threaded (the body
   writes only locals, so `memRel` survives).
   --------------------------------------------------------------------------- *)
Theorem evaluate_loopBody:
  loopInv input bs c i s /\ i < LENGTH input ==>
    ?s2. evaluate (loopBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         loopInv input bs (mstep c (EL i input)) (i + 1) s2
Proof
  strip_tac >>
  `EL i input < 256` by (fs [loopInv_def, EVERY_EL]) >>
  drule_all eval_loadbyte >> strip_tac >>
  (* string-key disequalities used by the FLOOKUP_UPDATE reductions *)
  `strlit "c" <> strlit "i" /\ strlit "c" <> strlit "b" /\
   strlit "i" <> strlit "b" /\ strlit "i" <> strlit "c" /\
   strlit "b" <> strlit "c" /\ strlit "b" <> strlit "i" /\
   strlit "len" <> strlit "b" /\ strlit "len" <> strlit "c" /\
   strlit "len" <> strlit "i" /\ strlit "base" <> strlit "b" /\
   strlit "base" <> strlit "c" /\ strlit "base" <> strlit "i"` by EVAL_TAC >>
  (* pull the loopInv fields out without dropping the folded relation *)
  `FLOOKUP s.locals (strlit "c") = SOME (ValWord (n2w c)) /\
   FLOOKUP s.locals (strlit "i") = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals (strlit "len") = SOME (ValWord (n2w (LENGTH input))) /\
   FLOOKUP s.locals (strlit "base") = SOME (ValWord bs) /\
   (?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)) /\
   c <= 255 /\ memRel input bs s /\ LENGTH input < 2n ** 63 /\
   EVERY (\x. x < 256) input` by fs [loopInv_def] >>
  qabbrev_tac `bv = (n2w (EL i input)):word64` >>
  qabbrev_tac `sA = set_var (strlit "b") (ValWord bv) s` >>
  qabbrev_tac `sB = set_var (strlit "c")
                      (ValWord (n2w (mstep c (EL i input)))) sA` >>
  qabbrev_tac `sC = set_var (strlit "i") (ValWord (n2w (i + 1))) sB` >>
  (* clocks as SEPARATE, chained assumptions (each ACCEPT-able) *)
  `sA.clock = s.clock` by simp [Abbr `sA`, set_var_def] >>
  `sB.clock = sA.clock` by simp [Abbr `sB`, set_var_def] >>
  `sC.clock = sB.clock` by simp [Abbr `sC`, set_var_def] >>
  `sC.clock = s.clock` by simp [] >>
  (* step 1: Assign «b» = the loaded byte *)
  `evaluate (Assign Local (strlit "b")
       (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")])), s)
     = (NONE, sA)`
     by (simp [Once evaluate_def, Abbr `sA`] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  (* step 2: the C2 single step, COMPOSED verbatim. Prove the folded equation
     inside the `by` so the unfolded `drule` fact does NOT leak into context
     (two equations with the same LHS make `fs`/`simp` loop). *)
  `mRel c (EL i input) sA`
     by (simp [mRel_def, Abbr `sA`, set_var_def, FLOOKUP_UPDATE, Abbr `bv`]) >>
  `evaluate (stepBody, sA) = (NONE, sB)`
     by (drule evaluate_stepBody >> simp [Abbr `sB`]) >>
  (* step 3: Assign «i» = i + 1 *)
  `FLOOKUP sB.locals (strlit "i") = SOME (ValWord (n2w i))`
     by simp [Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  `evaluate (Assign Local (strlit "i")
       (Op Add [Var Local (strlit "i"); Const (1w:word64)]), sB)
     = (NONE, sC)`
     by (simp [Once evaluate_def, eval_def, OPT_MMAP_def,
               wordLangTheory.word_op_def, word_add_n2w, Abbr `sC`] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  (* assemble the two Seqs: every hypothesis of Seq_NONE is now a standalone
     assumption, so discharge by exact ACCEPT (no rewriting, no loop). *)
  `evaluate (Seq stepBody
       (Assign Local (strlit "i")
          (Op Add [Var Local (strlit "i"); Const (1w:word64)])), sA)
     = (NONE, sC)`
     by (irule Seq_NONE >> qexists_tac `sB` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `evaluate (loopBody, s) = (NONE, sC)`
     by (simp [loopBody_def] >> irule Seq_NONE >> qexists_tac `sA` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `sC` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  (* re-establish the invariant at (mstep c (EL i input), i+1) *)
  `mstep c (EL i input) <= 255` by (irule mstep_le >> fs []) >>
  `sC.memory = s.memory /\ sC.memaddrs = s.memaddrs /\ sC.be = s.be`
     by simp [Abbr `sC`, Abbr `sB`, Abbr `sA`, set_var_def] >>
  `memRel input bs sC` by fs [memRel_def] >>
  `i + 1 <= LENGTH input` by fs [] >>
  simp [loopInv_def, Abbr `sC`, Abbr `sB`, Abbr `sA`, set_var_def,
        FLOOKUP_UPDATE, Abbr `bv`] >>
  fs []
QED

(* One iteration of the emitted `While`: when the guard is live and clock > 0,
   `evaluate (machineLoop, s)` reduces to `evaluate (machineLoop, s2)` for a state
   s2 that satisfies the invariant at the NEXT accumulator/index and has spent
   exactly one clock tick. This packages the clocked-`While` `fix_clock`/dec_clock
   bookkeeping so the induction proper is clean. *)
Theorem machineLoop_unfold:
  loopInv input bs c i s /\ i < LENGTH input /\ s.clock <> 0 ==>
  ?s2. evaluate (machineLoop, s) = evaluate (machineLoop, s2) /\
       loopInv input bs (mstep c (EL i input)) (i + 1) s2 /\
       s2.clock = s.clock - 1
Proof
  strip_tac >>
  (* establish the guard FIRST, while `loopInv .. s` is the only loopInv in
     scope, so `drule eval_loop_guard` cannot pick a wrong-state instance *)
  `eval s (Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len")))
     = SOME (ValWord 1w)` by (drule eval_loop_guard >> fs []) >>
  `loopInv input bs c i (dec_clock s)`
     by (simp [dec_clock_def] >> irule loopInv_clock >> fs []) >>
  drule_all evaluate_loopBody >> strip_tac >>
  qexists_tac `s2` >>
  conj_tac
  >- (
      (* unfold the LEFT machineLoop only (one While step); keep the right side
         `evaluate (machineLoop, s2)` folded, then fold the reduced left back.
         The clean `evaluate_def` While clause has no residual `fix_clock`, so the
         body result threads directly (s1 = s2 via the loopBody equation). *)
      CONV_TAC (LAND_CONV
        (ONCE_REWRITE_CONV [machineLoop_def] THENC
         ONCE_REWRITE_CONV [evaluate_def])) >>
      simp [GSYM machineLoop_def]) >>
  conj_tac >- fs [] >>
  fs [dec_clock_def]
QED

(* ---------------------------------------------------------------------------
   LINK A FOR THE LOOP — the loop-invariant induction over the clocked `While`.

   With clock >= (number of remaining iterations), running the emitted `While`
   from an invariant state at (accumulator c, index i) TERMINATES (no TimeOut)
   and leaves `«c»` holding EXACTLY the Lean fold `n2w (FOLDL mstep c (DROP i
   input))` — the model's `run` continued from (c,i). Induction on a bound `k`
   for the remaining count; the clock threads down one per iteration because the
   body consumes none (packaged in `machineLoop_unfold`).
   --------------------------------------------------------------------------- *)
Theorem machineLoop_fold_bounded:
  !k input bs c i s.
    loopInv input bs c i s /\ LENGTH input - i <= k /\
    LENGTH input - i <= s.clock ==>
    ?s'. evaluate (machineLoop, s) = (NONE, s') /\
         FLOOKUP s'.locals (strlit "c")
           = SOME (ValWord (n2w (FOLDL mstep c (DROP i input))))
Proof
  Induct_on `k`
  >- (
    (* k = 0: no iterations remain, i.e. i >= LENGTH input. Guard false, exit. *)
    rpt strip_tac >>
    `~(i < LENGTH input)` by fs [] >>
    drule eval_loop_guard >> strip_tac >>
    `DROP i input = []` by (irule DROP_LENGTH_TOO_LONG >> fs []) >>
    simp [machineLoop_def, Once evaluate_def] >>
    fs [loopInv_def]) >>
  (* k -> SUC k *)
  rpt strip_tac >>
  Cases_on `i < LENGTH input`
  >- (
    (* an iteration runs: step once, then recurse via the IH *)
    `s.clock <> 0` by fs [] >>
    drule_all machineLoop_unfold >> strip_tac >>
    last_x_assum (qspecl_then
       [`input`,`bs`,`mstep c (EL i input)`,`i + 1`,`s2`] mp_tac) >>
    impl_tac >- fs [] >>
    strip_tac >>
    qexists_tac `s'` >>
    (* fold: FOLDL mstep c (DROP i input) = FOLDL mstep (mstep c (EL i input))
       (DROP (i+1) input); normalise SUC i -> i+1 so it meets the IH's index *)
    `DROP i input = EL i input :: DROP (i + 1) input`
       by (`DROP i input = EL i input :: DROP (SUC i) input`
             by (irule DROP_EL_CONS_local >> fs []) >>
           fs [arithmeticTheory.ADD1]) >>
    `FOLDL mstep c (DROP i input)
       = FOLDL mstep (mstep c (EL i input)) (DROP (i + 1) input)`
       by asm_simp_tac (srw_ss()) [FOLDL] >>
    fs []) >>
  (* no iteration: i >= LENGTH input, guard false, exit (same as base) *)
  drule eval_loop_guard >> strip_tac >>
  `DROP i input = []` by (irule DROP_LENGTH_TOO_LONG >> fs []) >>
  simp [machineLoop_def, Once evaluate_def] >>
  fs [loopInv_def]
QED

(* ---------------------------------------------------------------------------
   The headline, specialized to a whole run from index 0 with accumulator 0:
   the emitted `While` computes EXACTLY the Lean fold over the entire input
   stream, given clock >= |input|. `FOLDL mstep 0 input` is the HOL twin of the
   Lean model's `C2.run input`.
   --------------------------------------------------------------------------- *)
Theorem machineLoop_refines_run:
  loopInv input bs 0 0 s /\ LENGTH input <= s.clock ==>
  ?s'. evaluate (machineLoop, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "c")
         = SOME (ValWord (n2w (FOLDL mstep 0 input)))
Proof
  strip_tac >>
  `LENGTH input - 0 <= LENGTH input` by fs [] >>
  drule machineLoop_fold_bounded >>
  disch_then (qspec_then `LENGTH input` mp_tac) >>
  impl_tac >- fs [] >>
  simp []
QED

val _ = export_theory ();
