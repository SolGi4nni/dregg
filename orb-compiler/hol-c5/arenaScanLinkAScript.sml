(* ===========================================================================
   C5 probe — LINK A for a REAL ENGINE PRIMITIVE: the Arena request-line
   find-first-SP scan (the hot path of Arena/Parse.lean `parseRequestLine`).

   parseRequestLine (Arena/Parse.lean) splits "method SP target SP HTTP/x" by
   scanning the request line for the first space (SP = 32), via
   `findByteIdx SP line = line.findIdx? (· == 32)`. THAT find-first-delimiter
   scan is the parser hot path this probe emits and preservation-proves.

   Unlike C2/C3's toy counter FSM, this is a REAL engine component:
     * the loop BRANCHES in its body (on SP: record; else: advance) — not a
       uniform fold;
     * it EARLY-EXITS the moment the delimiter is seen (a compound guard
       `i < len && found == 0`) — the first genuinely non-total scan;
     * the result is an OFFSET, exactly the `i₁` parseRequestLine records.

   The emitted `.pnk` guard `i < len && found == 0` is transcribed to the AST
   the Pancake front-end (panPtreeConversion) actually produces for `&&`:
     Op And [ Cmp NotEqual (Const 0w) (Cmp Less  «i»   «len») ;
              Cmp NotEqual (Const 0w) (Cmp Equal «found» (Const 0w)) ]
   (`e1 && e2` ==> `Op And [Cmp NotEqual 0w e1; Cmp NotEqual 0w e2]`).

   We prove, against real `panSem$evaluate`, that running the emitted `While`
   refines the Lean spec `scanSp` (the HOL twin of `findByteIdx SP`):
       evaluate (scanLoop, s)  ==>  «found»/«i» witness  scanSp input.

   The skeleton is C3's loop-invariant induction over the clocked `While`,
   REUSED VERBATIM: `memRel` (the byte-memory LoadByte relation), `w2w_byte`,
   `fix_clock_id`, `Seq_NONE` (all opened from machineLoopLinkATheory), and
   `signed_lt_n2w64` (from machineStepLinkATheory). What is NEW is the branching
   body and the two-mode exit (found the delimiter / ran off the end).
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory;
open machineStepLinkATheory;   (* signed_lt_n2w64                              *)
open machineLoopLinkATheory;   (* memRel, w2w_byte, fix_clock_id, Seq_NONE     *)

val _ = new_theory "arenaScanLinkA";

(* ---------------------------------------------------------------------------
   The Lean SPEC, re-declared in HOL. Byte-identical to
   `findByteIdx SP = List.findIdx? (· == 32)`: the index of the first SP (32),
   or NONE if the line has no space.
   --------------------------------------------------------------------------- *)
Definition scanSp_def:
  (scanSp [] = NONE) /\
  (scanSp (b::bs) =
     if b = 32n then SOME (0:num)
     else case scanSp bs of NONE => NONE | SOME j => SOME (SUC j))
End

(* The delimiter offset a `complete` scan carries, characterised: an SP at j
   with no SP before it IS the first-SP index. *)
Theorem scanSp_found:
  !input j.
    j < LENGTH input /\ EL j input = 32 /\
    EVERY (\b. b <> 32) (TAKE j input) ==>
    scanSp input = SOME j
Proof
  Induct_on `input` >> rw [] >>
  Cases_on `j` >> fs [scanSp_def] >>
  res_tac >> fs []
QED

(* A line with no SP scans to NONE. *)
Theorem scanSp_none:
  !input. EVERY (\b. b <> 32) input ==> scanSp input = NONE
Proof
  Induct >> rw [scanSp_def]
QED

(* A small list fact the advancing branch needs: extending the scanned prefix
   by the current (non-SP) byte. *)
Theorem TAKE_SUC_SNOC:
  !n l. n < LENGTH l ==> TAKE (n + 1) l = TAKE n l ++ [EL n l]
Proof
  Induct >> Cases_on `l` >> rw [] >> fs [ADD1]
QED

(* ---------------------------------------------------------------------------
   The IMPLEMENTATION: the .pnk scan loop, as a real panLang AST.

     found = 0; i = 0;
     while (i < len && found == 0) {
       b = ld8 (buf + i);
       if (b == 32) { found = 1; }     // record: SP at offset i
       else { i = i + 1; }             // advance
     }
     // found ? SP at «i» : «i» == len (no SP)

   `scanGuard` is the EXACT AST panPtreeConversion emits for `&&` (each conjunct
   normalised through `Cmp NotEqual (Const 0w) _`).
   --------------------------------------------------------------------------- *)
Definition scanGuard_def:
  scanGuard =
    Op And
      [ Cmp NotEqual (Const (0w:word64))
          (Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len"))) ;
        Cmp NotEqual (Const (0w:word64))
          (Cmp Equal (Var Local (strlit "found")) (Const (0w:word64))) ]
End

Definition scanBody_def:
  scanBody =
    Seq (Assign Local (strlit "b")
           (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")])))
        (If (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
            (Assign Local (strlit "found") (Const (1w:word64)))
            (Assign Local (strlit "i")
               (Op Add [Var Local (strlit "i"); Const (1w:word64)])))
End

Definition scanLoop_def:
  scanLoop = While scanGuard scanBody
End

(* ---------------------------------------------------------------------------
   The loop invariant. Reuses C3's `memRel` (the LoadByte byte-memory relation)
   verbatim. Carries the scan-specific semantic facts: the scanned prefix has no
   SP, and if `found = 1` then the current index really is an SP.
   --------------------------------------------------------------------------- *)
Definition scanInv_def:
  scanInv (input:num list) (bs:word64) (i:num) (found:num)
          (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "i")     = SOME (ValWord (n2w i)) /\
    FLOOKUP s.locals (strlit "found") = SOME (ValWord (n2w found)) /\
    FLOOKUP s.locals (strlit "len")   = SOME (ValWord (n2w (LENGTH input))) /\
    FLOOKUP s.locals (strlit "base")  = SOME (ValWord bs) /\
    (?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)) /\
    memRel input bs s /\
    i <= LENGTH input /\ LENGTH input < 2n ** 63 /\ EVERY (\x. x < 256) input /\
    (found = 0 \/ found = 1) /\
    EVERY (\b. b <> 32) (TAKE i input) /\
    (found = 1 ==> i < LENGTH input /\ EL i input = 32)
End

(* The invariant is clock-independent (depends only on locals/memory), so the
   `While`'s per-iteration clock decrement preserves it. *)
Theorem scanInv_clock:
  scanInv input bs i found s ==> scanInv input bs i found (s with clock := ck)
Proof
  rw [scanInv_def, memRel_def]
QED

(* ---------------------------------------------------------------------------
   The per-iteration byte read (mirrors C3's `eval_loadbyte`, for `scanInv`):
   real `panSem$eval` of `ld8 (base + i)` returns the i-th model byte via
   `memRel` + `w2w_byte`.
   --------------------------------------------------------------------------- *)
Theorem eval_scan_loadbyte:
  scanInv input bs i found s /\ i < LENGTH input ==>
    eval s (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")]))
      = SOME (ValWord ((n2w (EL i input)):word64))
Proof
  strip_tac >>
  `EL i input < 256` by (fs [scanInv_def, EVERY_EL]) >>
  `mem_load_byte s.memory s.memaddrs s.be (bs + n2w i)
      = SOME ((n2w (EL i input)):word8)` by (fs [scanInv_def, memRel_def]) >>
  fs [scanInv_def] >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, WORD_ADD_0, w2w_byte]
QED

(* ---------------------------------------------------------------------------
   The compound guard evaluates to 1w EXACTLY when the loop should keep scanning
   (`i < len` AND not-yet-found). The `&&` desugaring's `Cmp NotEqual (Const 0w)`
   wrappers are idempotent on the {0w,1w} comparison results; the `Op And` is the
   logical and.
   --------------------------------------------------------------------------- *)
Theorem eval_scanGuard:
  scanInv input bs i found s ==>
    eval s scanGuard
      = SOME (ValWord (if (i < LENGTH input /\ found = 0) then 1w else 0w))
Proof
  strip_tac >>
  `FLOOKUP s.locals (strlit "i") = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals (strlit "found") = SOME (ValWord (n2w found)) /\
   FLOOKUP s.locals (strlit "len") = SOME (ValWord (n2w (LENGTH input))) /\
   i <= LENGTH input /\ LENGTH input < 2n ** 63 /\ (found = 0 \/ found = 1)`
     by fs [scanInv_def] >>
  `i < 2n ** 63` by (irule LESS_EQ_LESS_TRANS >> qexists_tac `LENGTH input` >> fs []) >>
  `(n2w i:word64 < n2w (LENGTH input)) = (i < LENGTH input)`
     by (irule signed_lt_n2w64 >> fs []) >>
  `eval s (Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len")))
     = SOME (ValWord (if i < LENGTH input then 1w else 0w))`
     by simp [eval_def, asmTheory.word_cmp_def] >>
  `(n2w found = 0w:word64) = (found = 0)` by (rw [] >> EVAL_TAC) >>
  `eval s (Cmp Equal (Var Local (strlit "found")) (Const (0w:word64)))
     = SOME (ValWord (if found = 0 then 1w else 0w))`
     by simp [eval_def, asmTheory.word_cmp_def] >>
  `eval s (Cmp NotEqual (Const (0w:word64))
             (Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len"))))
     = SOME (ValWord (if i < LENGTH input then 1w else 0w))`
     by (Cases_on `i < LENGTH input` >> simp [eval_def, asmTheory.word_cmp_def]) >>
  `eval s (Cmp NotEqual (Const (0w:word64))
             (Cmp Equal (Var Local (strlit "found")) (Const (0w:word64))))
     = SOME (ValWord (if found = 0 then 1w else 0w))`
     by (Cases_on `found = 0` >> simp [eval_def, asmTheory.word_cmp_def]) >>
  simp [scanGuard_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def] >>
  rw [] >> fs [] >> EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   The current byte equals SP (32): real `panSem$eval` of `b == 32` = 1w EXACTLY
   when the loaded byte is the delimiter.
   --------------------------------------------------------------------------- *)
Theorem eval_isSp:
  FLOOKUP s.locals (strlit "b") = SOME (ValWord (n2w (EL i input))) /\
  EL i input < 256 ==>
  eval s (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
    = SOME (ValWord (if EL i input = 32 then 1w else 0w))
Proof
  strip_tac >>
  `(n2w (EL i input) = (32w:word64)) = (EL i input = 32)`
     by (`EL i input < dimword (:64)` by
           (`(256:num) < dimword (:64)` by EVAL_TAC >> fs []) >>
         `(32:num) < dimword (:64)` by EVAL_TAC >>
         simp [n2w_11] >> fs [LESS_MOD]) >>
  simp [eval_def, asmTheory.word_cmp_def]
QED

(* ---------------------------------------------------------------------------
   ONE ITERATION of the body: real `panSem$evaluate` of `scanBody` reads the
   i-th byte, then BRANCHES — on SP it records (found := 1, i held); otherwise it
   advances (i := i+1) — preserving the clock and RE-ESTABLISHING the invariant
   at the branch-appropriate (i, found). This is where the C3 reusables
   (`memRel`, `Seq_NONE`) compose with the parser's branching structure.
   --------------------------------------------------------------------------- *)
Theorem evaluate_scanBody:
  scanInv input bs i found s /\ i < LENGTH input /\ found = 0 ==>
    ?s2. evaluate (scanBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         ((EL i input = 32  /\ scanInv input bs i (1:num) s2) \/
          (EL i input <> 32 /\ scanInv input bs (i + 1) 0 s2))
Proof
  strip_tac >>
  `EL i input < 256` by (fs [scanInv_def, EVERY_EL]) >>
  drule_all eval_scan_loadbyte >> strip_tac >>
  (* string-key disequalities for the FLOOKUP_UPDATE reductions *)
  `strlit "b" <> strlit "found" /\ strlit "b" <> strlit "i" /\
   strlit "b" <> strlit "len" /\ strlit "b" <> strlit "base" /\
   strlit "found" <> strlit "i" /\ strlit "found" <> strlit "len" /\
   strlit "found" <> strlit "base" /\ strlit "found" <> strlit "b" /\
   strlit "i" <> strlit "found" /\ strlit "i" <> strlit "len" /\
   strlit "i" <> strlit "base" /\ strlit "i" <> strlit "b"` by EVAL_TAC >>
  `FLOOKUP s.locals (strlit "i") = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals (strlit "found") = SOME (ValWord (n2w found)) /\
   FLOOKUP s.locals (strlit "len") = SOME (ValWord (n2w (LENGTH input))) /\
   FLOOKUP s.locals (strlit "base") = SOME (ValWord bs) /\
   (?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)) /\
   memRel input bs s /\ i <= LENGTH input /\ LENGTH input < 2n ** 63 /\
   EVERY (\x. x < 256) input /\ EVERY (\b. b <> 32) (TAKE i input)`
     by fs [scanInv_def] >>
  qabbrev_tac `bv = (n2w (EL i input)):word64` >>
  qabbrev_tac `sA = set_var (strlit "b") (ValWord bv) s` >>
  `sA.clock = s.clock` by simp [Abbr `sA`, set_var_def] >>
  `sA.memory = s.memory /\ sA.memaddrs = s.memaddrs /\ sA.be = s.be`
     by simp [Abbr `sA`, set_var_def] >>
  (* step 1: Assign «b» = the loaded byte *)
  `evaluate (Assign Local (strlit "b")
       (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")])), s)
     = (NONE, sA)`
     by (simp [Once evaluate_def, Abbr `sA`] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  (* the branch guard `b == 32` *)
  `FLOOKUP sA.locals (strlit "b") = SOME (ValWord bv)`
     by simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  `eval sA (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
     = SOME (ValWord (if EL i input = 32 then 1w else 0w))`
     by (irule eval_isSp >> fs [Abbr `bv`]) >>
  `memRel input bs sA` by fs [memRel_def] >>
  `(1w:word64) <> 0w` by EVAL_TAC >>
  Cases_on `EL i input = 32`
  >- (
    (* SP found: If-then arm, `Assign «found» 1` *)
    `eval sA (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
       = SOME (ValWord 1w)` by fs [] >>
    qabbrev_tac `sB = set_var (strlit "found") (ValWord (1w:word64)) sA` >>
    `evaluate (If (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
                  (Assign Local (strlit "found") (Const (1w:word64)))
                  (Assign Local (strlit "i")
                     (Op Add [Var Local (strlit "i"); Const (1w:word64)])), sA)
       = (NONE, sB)`
       by (simp [Once evaluate_def] >>
           simp [Once evaluate_def, eval_def, Abbr `sB`, Abbr `sA`, set_var_def,
                 FLOOKUP_UPDATE, is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
    `evaluate (scanBody, s) = (NONE, sB)`
       by (simp [scanBody_def] >> irule Seq_NONE >> qexists_tac `sA` >>
           rpt conj_tac >> first_assum ACCEPT_TAC) >>
    qexists_tac `sB` >>
    `sB.clock = s.clock` by simp [Abbr `sB`, set_var_def] >>
    `sB.memory = s.memory /\ sB.memaddrs = s.memaddrs /\ sB.be = s.be`
       by simp [Abbr `sB`, Abbr `sA`, set_var_def] >>
    `memRel input bs sB` by fs [memRel_def] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    disj1_tac >> conj_tac >- fs [] >>
    simp [scanInv_def, Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
    fs []) >>
  (* SP not found: If-else arm, `Assign «i» (i+1)` *)
  `eval sA (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
     = SOME (ValWord 0w)` by fs [] >>
  `FLOOKUP sA.locals (strlit "i") = SOME (ValWord (n2w i))`
     by simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  qabbrev_tac `sB = set_var (strlit "i") (ValWord (n2w (i + 1))) sA` >>
  `evaluate (If (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
                (Assign Local (strlit "found") (Const (1w:word64)))
                (Assign Local (strlit "i")
                   (Op Add [Var Local (strlit "i"); Const (1w:word64)])), sA)
     = (NONE, sB)`
     by (simp [Once evaluate_def] >>
         simp [Once evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
               word_add_n2w, Abbr `sB`, is_valid_value_def, lookup_kvar_def,
               shape_of_def]) >>
  `evaluate (scanBody, s) = (NONE, sB)`
     by (simp [scanBody_def] >> irule Seq_NONE >> qexists_tac `sA` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `sB` >>
  `sB.clock = s.clock` by simp [Abbr `sB`, set_var_def] >>
  `sB.memory = s.memory /\ sB.memaddrs = s.memaddrs /\ sB.be = s.be`
     by simp [Abbr `sB`, Abbr `sA`, set_var_def] >>
  `memRel input bs sB` by fs [memRel_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj2_tac >> conj_tac >- fs [] >>
  (* the scanned prefix extends by the non-SP byte: TAKE (i+1) = TAKE i ++ [EL i] *)
  `TAKE (i + 1) input = TAKE i input ++ [EL i input]`
     by (irule TAKE_SUC_SNOC >> fs []) >>
  `i + 1 <= LENGTH input` by fs [] >>
  simp [scanInv_def, Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  fs []
QED

(* One emitted `While` iteration: guard live + clock > 0 reduces
   `evaluate (scanLoop, s)` to `evaluate (scanLoop, s2)` with the branch-updated
   invariant and one clock tick spent. Packages the clocked-`While`
   `fix_clock`/`dec_clock` bookkeeping (C3's `machineLoop_unfold` shape). *)
Theorem scanLoop_unfold:
  scanInv input bs i found s /\ i < LENGTH input /\ found = 0 /\ s.clock <> 0 ==>
  ?s2. evaluate (scanLoop, s) = evaluate (scanLoop, s2) /\
       s2.clock = s.clock - 1 /\
       ((EL i input = 32  /\ scanInv input bs i (1:num) s2) \/
        (EL i input <> 32 /\ scanInv input bs (i + 1) 0 s2))
Proof
  strip_tac >>
  `eval s scanGuard = SOME (ValWord 1w)`
     by (drule eval_scanGuard >> fs []) >>
  `scanInv input bs i found (dec_clock s)`
     by (simp [dec_clock_def] >> irule scanInv_clock >> fs []) >>
  `i < LENGTH input /\ found = 0` by fs [] >>
  drule_all evaluate_scanBody >> strip_tac >>
  qexists_tac `s2` >>
  `evaluate (scanLoop, s) = evaluate (scanLoop, s2)`
     by (CONV_TAC (LAND_CONV
           (ONCE_REWRITE_CONV [scanLoop_def] THENC
            ONCE_REWRITE_CONV [evaluate_def])) >>
         simp [GSYM scanLoop_def]) >>
  `s2.clock = s.clock - 1` by fs [dec_clock_def] >>
  fs []
QED

(* ---------------------------------------------------------------------------
   LINK A FOR THE SCAN — the loop-invariant induction over the clocked `While`.

   From an invariant state at (index i, found), with clock >= remaining bytes,
   the emitted scan `While` TERMINATES (no TimeOut) and leaves «i»/«found»
   witnessing the scan outcome: either `found = 1` at the first-SP offset, or
   `found = 0` with `i = LENGTH input` (no SP in the whole line). Induction on a
   bound `k` for the remaining count; the clock threads down one per iteration
   (C3's `machineLoop_fold_bounded` skeleton, with the branching/early-exit).
   --------------------------------------------------------------------------- *)
Theorem scanLoop_scan_bounded:
  !k input bs i found s.
    scanInv input bs i found s /\ LENGTH input - i <= k /\
    LENGTH input - i <= s.clock ==>
    ?s' j f. evaluate (scanLoop, s) = (NONE, s') /\
             FLOOKUP s'.locals (strlit "i")     = SOME (ValWord (n2w j)) /\
             FLOOKUP s'.locals (strlit "found") = SOME (ValWord (n2w f)) /\
             (f = 0 \/ f = 1) /\
             EVERY (\b. b <> 32) (TAKE j input) /\
             (f = 1 ==> j < LENGTH input /\ EL j input = 32) /\
             (f = 0 ==> j = LENGTH input)
Proof
  Induct_on `k`
  >- (
    (* k = 0: no iterations remain (i >= LENGTH input, so i = LENGTH input).
       The guard is false; exit with (j = i = len, f = found = 0). *)
    rpt strip_tac >>
    `i = LENGTH input` by fs [scanInv_def] >>
    `found = 0` by (fs [scanInv_def] >> Cases_on `found = 1` >> fs []) >>
    `eval s scanGuard = SOME (ValWord 0w)` by (drule eval_scanGuard >> fs []) >>
    qexists_tac `s` >> qexists_tac `i` >> qexists_tac `found` >>
    `evaluate (scanLoop, s) = (NONE, s)`
       by (simp [scanLoop_def, Once evaluate_def]) >>
    fs [scanInv_def]) >>
  (* k -> SUC k *)
  rpt strip_tac >>
  Cases_on `i < LENGTH input /\ found = 0`
  >- (
    (* an iteration runs. Split the guard conjunction WITHOUT substituting
       `found := 0` in the goal (that would break `drule`'s match of the
       theorem's `found = 0` conjunct). *)
    `i < LENGTH input /\ found = 0` by fs [] >>
    `s.clock <> 0` by fs [] >>
    drule_all scanLoop_unfold >> strip_tac
    >- (
      (* SP found this iteration: found := 1, guard now false, exit at s2 *)
      `eval s2 scanGuard = SOME (ValWord 0w)`
         by (drule eval_scanGuard >> fs []) >>
      `evaluate (scanLoop, s2) = (NONE, s2)`
         by (simp [scanLoop_def, Once evaluate_def]) >>
      qexists_tac `s2` >> qexists_tac `i` >> qexists_tac `1` >>
      fs [scanInv_def]) >>
    (* advanced: recurse via the IH at (i+1, 0) *)
    last_x_assum (qspecl_then [`input`,`bs`,`i + 1`,`0`,`s2`] mp_tac) >>
    impl_tac >- fs [] >>
    strip_tac >>
    qexists_tac `s'` >> qexists_tac `j` >> qexists_tac `f` >> fs []) >>
  (* no iteration: guard false at s. Either found = 1 (SP already at i) or
     i = LENGTH input (ran off the end); both are terminal. *)
  `eval s scanGuard = SOME (ValWord 0w)` by (drule eval_scanGuard >> fs []) >>
  `evaluate (scanLoop, s) = (NONE, s)`
     by (simp [scanLoop_def, Once evaluate_def]) >>
  qexists_tac `s` >> qexists_tac `i` >> qexists_tac `found` >>
  fs [scanInv_def] >>
  Cases_on `found = 1` >> fs [] >>
  `i = LENGTH input` by fs [] >> fs []
QED

(* ---------------------------------------------------------------------------
   THE HEADLINE — Link A for the request-line SP scan, from a fresh (i=0,
   found=0) state with clock >= |input|: the emitted `While` computes EXACTLY the
   Lean spec `scanSp input` (the HOL twin of `findByteIdx SP` — parseRequestLine's
   first split point). On `SOME j`, «found»=1 and «i»=j (the offset); on `NONE`,
   «found»=0 and «i»=|input| (no space in the line).
   --------------------------------------------------------------------------- *)
Theorem scanLoop_refines_findSp:
  scanInv input bs 0 0 s /\ LENGTH input <= s.clock ==>
  ?s'. evaluate (scanLoop, s) = (NONE, s') /\
       (case scanSp input of
          NONE   => FLOOKUP s'.locals (strlit "found") = SOME (ValWord 0w) /\
                    FLOOKUP s'.locals (strlit "i") = SOME (ValWord (n2w (LENGTH input)))
        | SOME j => FLOOKUP s'.locals (strlit "found") = SOME (ValWord 1w) /\
                    FLOOKUP s'.locals (strlit "i") = SOME (ValWord (n2w j)))
Proof
  strip_tac >>
  qspecl_then [`LENGTH input`,`input`,`bs`,`0`,`0`,`s`] mp_tac scanLoop_scan_bounded >>
  impl_tac >- (simp [] >> fs []) >>
  (* `strip_tac` case-splits the `f = 0 \/ f = 1` disjunction into two subgoals;
     the TRYs pick the right `scanSp` characterisation in each. *)
  strip_tac >>
  qexists_tac `s'` >>
  TRY (`scanSp input = SOME j` by (irule scanSp_found >> fs [])) >>
  TRY (`scanSp input = NONE` by
         (irule scanSp_none >>
          `j = LENGTH input` by fs [] >>
          `TAKE j input = input` by simp [TAKE_LENGTH_ID] >>
          fs [])) >>
  simp [] >> fs []
QED

val _ = export_theory ();
