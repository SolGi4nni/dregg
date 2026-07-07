(* ===========================================================================
   C6 probe — LINK A for a REAL, COMPOSED PARSER FUNCTION: the Arena
   `parseRequestLine` method|target split, built by COMPOSING TWO instances of
   the C5 request-line SP scan (`scanLoop_refines_findSp`).

   parseRequestLine (Arena/Parse.lean) is:
       i1 <- findByteIdx SP line               (* first  SP: method length   *)
       rest1 = line.drop (i1+1)
       i2 <- findByteIdx SP rest1              (* second SP: target length   *)
       rest2 = rest1.drop (i2+1)
       if (findByteIdx SP rest2).isSome  then none   (* no third SP          *)
       else if i1 = 0                    then none   (* non-empty method     *)
       else if !startsWithHttpSlash rest2 then none  (* version starts HTTP/ *)
       else { method  = (off,           i1)
              target  = (off+i1+1,       i2)
              version = (off+i1+1+i2+1,   |rest2|) }

   C5 emitted + Link-A-proved ONE find-first-SP scan (`scanLoop`) and proved it
   computes exactly `scanSp = findByteIdx SP` (`scanLoop_refines_findSp`). C6
   COMPOSES two of those scans, at shifted offsets, into the whole method|target
   parse:

       twoScan = Seq scanLoop (Seq setup2 scanLoop)

   `setup2` saves the first scan's result (`i1`), then reshapes the loop locals
   so the SECOND `scanLoop` is a fresh instance over `rest1 = DROP (i1+1) line`
   at base `buf + (i1+1)` and length `|line| - (i1+1)`.  The proof composes the
   C5 scan theorem TWICE (`scanLoop_refines_findSp` for the scanSp witness) and a
   framing induction `scanLoop_run` (clock lower/upper bound + locals frame + the
   exit invariant) that lets the two instances connect — the assembly mechanism
   for building a bigger emitted function out of preservation-proven components.

   We prove, against real `panSem$evaluate`, that whenever the Lean
   `parseRequestLine off line` returns SOME spans, the emitted `twoScan` computes
   the method length `i1` into local «i1» and the target length `i2` into local
   «i», with the offsets matching the Lean spans (`off`, `off+i1+1`).  The
   version span and the three residual checks (no-third-SP, i1<>0, HTTP/) are the
   mechanical remainder (the compiled binary in `pnk/parseline.pnk` does compute
   them and agrees with the real Lean parser on the vectors — Kernel 2).

   The C5 pieces (scanLoop, scanInv, scanSp, scanLoop_unfold, scanLoop_refines_findSp,
   scanSp_found, scanSp_none, evaluate_scanBody, eval_scanGuard) and C3's `memRel`
   are OPENED AND REUSED.  What is NEW is: the framing induction `scanLoop_run`
   (adds clock bounds + a locals frame to C5's `scanLoop_scan_bounded`), the
   `setup2` reshaping, the `memRel_DROP` shift lemma, and the two-scan composition.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory bitTheory wordsTheory wordsLib
     finite_mapTheory;
open panLangTheory panSemTheory;
open machineStepLinkATheory;   (* signed_lt_n2w64                              *)
open machineLoopLinkATheory;   (* memRel, memRel_def, Seq_NONE, fix_clock_id   *)
open arenaScanLinkATheory;     (* scanSp, scanLoop, scanInv, the C5 theorems   *)

val _ = new_theory "arenaParseLineLinkA";

(* ---------------------------------------------------------------------------
   Small word/list plumbing.
   --------------------------------------------------------------------------- *)

Theorem n2w_sub_le:
  !a b. b <= a ==> (n2w a - n2w b : word64) = n2w (a - b)
Proof
  metis_tac [n2w_sub]
QED

(* Same fact, but stated in the NORMAL form the word simplifier produces:
   `panSem$eval` of `Op Sub [x; y]` reduces to `x + -1w * y`, and the srw
   simpset rewrites every `a - b` to `a + -1w * b`, so `n2w_sub_le` (phrased with
   `-`) no longer matches.  This variant's LHS is already in the `+ -1w *` form. *)
Theorem n2w_sub_norm:
  !a b. b <= a ==> (n2w a + -1w * n2w b = n2w (a - b) : word64)
Proof
  rpt strip_tac >>
  once_rewrite_tac [GSYM wordsTheory.WORD_NEG_MUL] >>
  once_rewrite_tac [GSYM wordsTheory.word_sub_def] >>
  irule n2w_sub_le >> fs []
QED

(* n2w is injective on the values below 2^63 the parser works with (both lengths
   and offsets are < |line| < 2^63 < dimword(:64)). *)
Theorem n2w_inj_lt:
  !a b. a < 2n ** 63 /\ b < 2n ** 63 /\ (n2w a : word64) = n2w b ==> a = b
Proof
  rw [] >>
  `a < dimword (:64) /\ b < dimword (:64)`
     by (`dimword (:64) = 2 ** 64` by EVAL_TAC >> fs []) >>
  `a MOD dimword (:64) = a` by (irule LESS_MOD >> fs []) >>
  `b MOD dimword (:64) = b` by (irule LESS_MOD >> fs []) >>
  fs [n2w_11]
QED

(* memRel shifts under DROP: reading `DROP n line` from base `bs + n` is the same
   byte memory as reading `line` from `bs`. This is what lets the SECOND scan be a
   fresh scan over `rest1` at a shifted base. *)
Theorem memRel_DROP:
  !n line bs s. n <= LENGTH line /\ memRel line bs s ==>
    memRel (DROP n line) (bs + n2w n) s
Proof
  rw [memRel_def, LENGTH_DROP] >>
  `j + n < LENGTH line` by DECIDE_TAC >>
  `EL j (DROP n line) = EL (j + n) line` by simp [EL_DROP] >>
  `(bs + n2w j + n2w n : word64) = bs + n2w (j + n)`
     by (once_rewrite_tac [GSYM WORD_ADD_ASSOC] >> simp [word_add_n2w]) >>
  first_x_assum (qspec_then `j + n` mp_tac) >> simp []
QED

(* ---------------------------------------------------------------------------
   The Lean SPEC, re-declared in HOL: the whole `parseRequestLine`, byte-identical
   to Arena/Parse.lean (findByteIdx SP = scanSp; startsWithHttpSlash = httpSlash;
   the three spans as (off,len) pairs).
   --------------------------------------------------------------------------- *)

Definition httpSlash_def:
  (httpSlash (h::a::b::c::d::rest) =
     (h = 72n /\ a = 84n /\ b = 84n /\ c = 80n /\ d = 47n)) /\
  (httpSlash _ = F)
End

Definition parseReqLine_def:
  parseReqLine off line =
    case scanSp line of
      NONE => NONE
    | SOME i1 =>
      case scanSp (DROP (i1 + 1) line) of
        NONE => NONE
      | SOME i2 =>
        (let rest2 = DROP (i2 + 1) (DROP (i1 + 1) line) in
         if IS_SOME (scanSp rest2) then NONE
         else if i1 = 0 then NONE
         else if ~httpSlash rest2 then NONE
         else SOME ((off, i1),
                    (off + i1 + 1, i2),
                    (off + i1 + 1 + i2 + 1, LENGTH rest2)))
End

(* A found SP index is within the line. *)
Theorem scanSp_lt:
  !l j. scanSp l = SOME j ==> j < LENGTH l
Proof
  Induct_on `l` >> rw [scanSp_def] >>
  Cases_on `scanSp l` >> gvs [] >> res_tac >> fs []
QED

(* In the SOME case, the two scans succeed and the method/target spans are exactly
   (off, i1) and (off+i1+1, i2). *)
Theorem parseReqLine_SOME:
  parseReqLine off line = SOME ((mOff,mLen),(tOff,tLen),(vOff,vLen)) ==>
    scanSp line = SOME mLen /\ mOff = off /\
    scanSp (DROP (mLen + 1) line) = SOME tLen /\ tOff = off + mLen + 1
Proof
  simp [parseReqLine_def] >>
  Cases_on `scanSp line` >> gvs [] >>
  Cases_on `scanSp (DROP (x + 1) line)` >> gvs [] >>
  rpt IF_CASES_TAC >> rpt strip_tac >> gvs []
QED
val _ = (print "CKPT_DONE: parseReqLine_SOME\n"; TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   Seq composition with a clock-CONSUMING first component (C4's `Seq_NONE_le`,
   re-proved here — the loop spends clock, so C5/C3's clock-equal `Seq_NONE` does
   not sequence a loop with what follows it).
   --------------------------------------------------------------------------- *)
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
val _ = (print "CKPT_DONE: Seq_NONE_le\n"; TextIO.flushOut TextIO.stdOut);

(* The two save-slots «i1»/«found1» that `setup2` writes between the scans must
   survive both loops. `keepSaved a b` says a and b agree on exactly those two
   locals. Kept OPAQUE (its `_def` is unfolded only where needed) so the framing
   induction never carries a universally-quantified `FLOOKUP` rewrite. *)
Definition keepSaved_def:
  keepSaved (a:(64,'ffi) panSem$state) (b:(64,'ffi) panSem$state) <=>
    FLOOKUP a.locals (strlit "i1") = FLOOKUP b.locals (strlit "i1") /\
    FLOOKUP a.locals (strlit "found1") = FLOOKUP b.locals (strlit "found1")
End

Theorem keepSaved_trans:
  keepSaved a b /\ keepSaved b c ==> keepSaved a c
Proof
  rw [keepSaved_def]
QED

(* Writing any local other than the two save-slots preserves `keepSaved`. *)
Theorem keepSaved_set_var:
  k <> strlit "i1" /\ k <> strlit "found1" ==>
  keepSaved (set_var k v s0) s0
Proof
  rw [keepSaved_def, set_var_def, FLOOKUP_UPDATE]
QED

(* The MEMORY/loop-scalar frame the second scan needs preserved: the byte memory
   (memory/memaddrs/be — so `memRel` transfers) and the two loop locals «len»/«base».
   Kept OPAQUE exactly like `keepSaved`: carrying these as RAW state-field/`FLOOKUP`
   equalities through the framing induction blows the simplifier up (it accumulates
   and re-normalises big panSem-state equalities); a folded predicate threaded by
   `memFrame_trans` (never expanded inside the induction) does not.  `_def` is
   unfolded only once, non-inductively, in `scanLoop_run`. *)
Definition memFrame_def:
  memFrame (a:(64,'ffi) panSem$state) (b:(64,'ffi) panSem$state) <=>
    a.memory = b.memory /\ a.memaddrs = b.memaddrs /\ a.be = b.be /\
    FLOOKUP a.locals (strlit "len")  = FLOOKUP b.locals (strlit "len") /\
    FLOOKUP a.locals (strlit "base") = FLOOKUP b.locals (strlit "base")
End

Theorem memFrame_refl:
  memFrame a a
Proof
  rw [memFrame_def]
QED

Theorem memFrame_trans:
  memFrame a b /\ memFrame b c ==> memFrame a c
Proof
  rw [memFrame_def]
QED

(* Accessor for `scanInv`'s scalar facts, WITHOUT exposing the `memRel` quantifier.
   `scanLoop_run` uses this instead of `fs [scanInv_def]` so its induction never
   unfolds `memRel` (which otherwise blows the simplifier up over the whole
   panSem state). *)
Theorem scanInv_flookup:
  scanInv input bs i found s ==>
    FLOOKUP s.locals (strlit "found") = SOME (ValWord (n2w found)) /\
    FLOOKUP s.locals (strlit "i")     = SOME (ValWord (n2w i)) /\
    FLOOKUP s.locals (strlit "len")   = SOME (ValWord (n2w (LENGTH input))) /\
    FLOOKUP s.locals (strlit "base")  = SOME (ValWord bs) /\
    i <= LENGTH input /\ (found = 0 \/ found = 1) /\
    (found = 1 ==> i < LENGTH input /\ EL i input = 32)
Proof
  rw [scanInv_def]
QED

(* «b» (the scratch byte local) exists.  A dedicated accessor so the frame
   induction can obtain it WITHOUT `fs [scanInv_def]` — unfolding `scanInv` in the
   induction context reintroduces `memRel`'s `!j` byte-quantifier over the whole
   panSem state into the simplifier, which is exactly the blowup this probe fights.
   The single unfold happens here, in isolation, over a variable state. *)
Theorem scanInv_b_exists:
  scanInv input bs i found s ==>
    ?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)
Proof
  rw [scanInv_def]
QED

(* ---------------------------------------------------------------------------
   `scanBody` (C5) with a LOCALS FRAME: one body iteration only ever touches the
   locals «b», «found», «i» — every other local is preserved. This is exactly the
   fact that lets the FIRST scan's saved result (below, in «i1»/«found1») survive
   the loop. Proven by extending C5's `evaluate_scanBody` with the frame conjunct.
   --------------------------------------------------------------------------- *)
Theorem scanBody_step:
  scanInv input bs i found s /\ i < LENGTH input /\ found = 0 ==>
    ?s2. evaluate (scanBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         memFrame s2 s /\
         keepSaved s2 s /\
         ((EL i input = 32  /\ scanInv input bs i (1:num) s2) \/
          (EL i input <> 32 /\ scanInv input bs (i + 1) 0 s2))
Proof
  strip_tac >>
  `EL i input < 256` by (fs [scanInv_def, EVERY_EL]) >>
  drule_all eval_scan_loadbyte >> strip_tac >>
  `strlit "b" <> strlit "found" /\ strlit "b" <> strlit "i" /\
   strlit "found" <> strlit "i"` by EVAL_TAC >>
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
  `evaluate (Assign Local (strlit "b")
       (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")])), s)
     = (NONE, sA)`
     by (simp [Once evaluate_def, Abbr `sA`] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  `FLOOKUP sA.locals (strlit "b") = SOME (ValWord bv)`
     by simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  `eval sA (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
     = SOME (ValWord (if EL i input = 32 then 1w else 0w))`
     by (irule eval_isSp >> fs [Abbr `bv`]) >>
  `memRel input bs sA` by fs [memRel_def] >>
  `(1w:word64) <> 0w` by EVAL_TAC >>
  Cases_on `EL i input = 32`
  >- (
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
    `FLOOKUP sB.locals (strlit "len") = FLOOKUP s.locals (strlit "len") /\
     FLOOKUP sB.locals (strlit "base") = FLOOKUP s.locals (strlit "base")`
       by simp [Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
    `memFrame sB s` by (rw [memFrame_def] >> fs []) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac
    >- (`keepSaved sB sA`
          by (simp [Abbr `sB`, keepSaved_def, set_var_def, FLOOKUP_UPDATE] >> EVAL_TAC) >>
        `keepSaved sA s`
          by (simp [Abbr `sA`, keepSaved_def, set_var_def, FLOOKUP_UPDATE] >> EVAL_TAC) >>
        fs [keepSaved_def]) >>
    disj1_tac >> conj_tac >- fs [] >>
    simp [scanInv_def, Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >> fs []) >>
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
  `FLOOKUP sB.locals (strlit "len") = FLOOKUP s.locals (strlit "len") /\
   FLOOKUP sB.locals (strlit "base") = FLOOKUP s.locals (strlit "base")`
     by simp [Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  `memFrame sB s` by (rw [memFrame_def] >> fs []) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (`keepSaved sB sA`
        by (simp [Abbr `sB`, keepSaved_def, set_var_def, FLOOKUP_UPDATE] >> EVAL_TAC) >>
      `keepSaved sA s`
        by (simp [Abbr `sA`, keepSaved_def, set_var_def, FLOOKUP_UPDATE] >> EVAL_TAC) >>
      fs [keepSaved_def]) >>
  disj2_tac >> conj_tac >- fs [] >>
  `TAKE (i + 1) input = TAKE i input ++ [EL i input]`
     by (irule TAKE_SUC_SNOC >> fs []) >>
  `i + 1 <= LENGTH input` by fs [] >>
  simp [scanInv_def, Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >> fs []
QED
val _ = (print "CKPT_DONE: scanBody_step\n"; TextIO.flushOut TextIO.stdOut);

(* One emitted `While` iteration, exposing the locals frame (C5's `scanLoop_unfold`
   built on `scanBody_step` instead of `evaluate_scanBody`). *)
Theorem scanLoop_step:
  scanInv input bs i found s /\ i < LENGTH input /\ found = 0 /\ s.clock <> 0 ==>
  ?s2. evaluate (scanLoop, s) = evaluate (scanLoop, s2) /\
       s2.clock = s.clock - 1 /\
       memFrame s2 s /\
       keepSaved s2 s /\
       ((EL i input = 32  /\ scanInv input bs i (1:num) s2) \/
        (EL i input <> 32 /\ scanInv input bs (i + 1) 0 s2))
Proof
  strip_tac >>
  `eval s scanGuard = SOME (ValWord 1w)` by (drule eval_scanGuard >> fs []) >>
  `scanInv input bs i found (dec_clock s)`
     by (simp [dec_clock_def] >> irule scanInv_clock >> fs []) >>
  `i < LENGTH input /\ found = 0` by fs [] >>
  drule_all scanBody_step >> strip_tac >>
  qexists_tac `s2` >>
  `evaluate (scanLoop, s) = evaluate (scanLoop, s2)`
     by (CONV_TAC (LAND_CONV
           (ONCE_REWRITE_CONV [scanLoop_def] THENC
            ONCE_REWRITE_CONV [evaluate_def])) >>
         simp [GSYM scanLoop_def]) >>
  `s2.clock = s.clock - 1` by fs [dec_clock_def] >>
  `memFrame s2 s` by (fs [memFrame_def, dec_clock_def]) >>
  `keepSaved s2 s` by fs [keepSaved_def, dec_clock_def] >>
  fs []
QED
val _ = (print "CKPT_DONE: scanLoop_step\n"; TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   THE LEAN FRAME INDUCTION.  This is the induction over the clocked `While`, and
   the fix for the C6 simplifier blowup: its CONCLUSION carries ONLY

     * `s'.memory = s.memory` (+ `.memaddrs`/`.be`) — NOT `memRel` (whose `!j`
       byte-quantifier over the whole panSem state was what blew the simplifier up
       to ~23 GB when threaded through the induction hypothesis);
     * the two scalar loop-frame locals «len»/«base» (unchanged by the body);
     * «b» exists; the clock lower/upper bounds; and `keepSaved` (the «i1»/«found1»
       save-slots).

   `memRel` for the exit state is then reconstructed ONCE, non-inductively, in
   `scanLoop_run` below, from `memRel input bs s` plus this memory equality — so the
   quantifier never rides the induction.  The scan witness (the offset «i»/«found»
   and the prefix facts) comes from C5's `scanLoop_scan_bounded` (which already
   avoids `memRel` in its conclusion).
   --------------------------------------------------------------------------- *)
Theorem scanLoop_frame:
  !k input bs i found s.
    scanInv input bs i found s /\ LENGTH input - i <= k /\
    LENGTH input - i <= s.clock ==>
    ?s'. evaluate (scanLoop, s) = (NONE, s') /\
         memFrame s' s /\
         (?bb. FLOOKUP s'.locals (strlit "b") = SOME (ValWord bb)) /\
         s.clock - (LENGTH input - i) <= s'.clock /\
         s'.clock <= s.clock /\
         keepSaved s' s
Proof
  Induct_on `k`
  >- (
    rpt strip_tac >>
    imp_res_tac scanInv_flookup >>
    `i = LENGTH input` by fs [] >>
    `found = 0` by (Cases_on `found = 1` >> fs []) >>
    `eval s scanGuard = SOME (ValWord 0w)` by (drule eval_scanGuard >> fs []) >>
    qexists_tac `s` >>
    `evaluate (scanLoop, s) = (NONE, s)`
       by (simp [scanLoop_def, Once evaluate_def] >> fs []) >>
    `keepSaved s s` by rw [keepSaved_def] >>
    `memFrame s s` by simp [memFrame_refl] >>
    `?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)`
       by (drule scanInv_b_exists >> disch_then ACCEPT_TAC) >>
    rpt conj_tac >> fs []) >>
  rpt strip_tac >>
  Cases_on `i < LENGTH input /\ found = 0`
  >- (
    `i < LENGTH input /\ found = 0` by fs [] >>
    `s.clock <> 0` by fs [] >>
    drule_all scanLoop_step >> strip_tac
    >- (
      (* SP found this iteration: found := 1, guard now false, exit at s2.
         The IH is not needed here — drop it before any simp/fs. *)
      qpat_x_assum `!input bs i found s. _` kall_tac >>
      `eval s2 scanGuard = SOME (ValWord 0w)` by (drule eval_scanGuard >> fs []) >>
      `evaluate (scanLoop, s2) = (NONE, s2)`
         by (simp [scanLoop_def, Once evaluate_def] >> fs []) >>
      qexists_tac `s2` >>
      `evaluate (scanLoop, s) = (NONE, s2)` by fs [] >>
      `s.clock - (LENGTH input - i) <= s2.clock` by fs [] >>
      `s2.clock <= s.clock` by fs [] >>
      `?bb. FLOOKUP s2.locals (strlit "b") = SOME (ValWord bb)`
         by (qpat_x_assum `scanInv _ _ _ _ s2`
               (mp_tac o MATCH_MP scanInv_b_exists) >> disch_then ACCEPT_TAC) >>
      rpt conj_tac >> fs []) >>
    (* advanced: recurse via IH at (i+1, 0).  The frame is carried as the OPAQUE
       predicates `memFrame`/`keepSaved` (never unfolded here), threaded by their
       transitivity lemmas — so the induction never accumulates raw panSem-state
       field/`FLOOKUP` equalities (which made a bare `fs []` blow the simplifier up
       to tens of GB). *)
    (* Establish the IH's two arithmetic preconditions SELF-CONTAINEDLY (pull only
       the facts each needs, drop the rest) so the IH application discharges them by
       direct assumption — never a full-context `fs` whose nested nat-subtractions
       blow the arithmetic decision procedure up. *)
    `LENGTH input - (i + 1) <= k`
       by (qpat_assum `LENGTH input - i <= SUC k` mp_tac >>
           rpt (pop_assum kall_tac) >> fs []) >>
    `LENGTH input - (i + 1) <= s2.clock`
       by (qpat_assum `LENGTH input - i <= s.clock` mp_tac >>
           qpat_assum `s2.clock = _` mp_tac >>
           rpt (pop_assum kall_tac) >> fs []) >>
    last_x_assum (qspecl_then [`input`,`bs`,`i + 1`,`0`,`s2`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >>
    qexists_tac `s'` >>
    (* every conjunct is proved OPAQUELY (memFrame/keepSaved via transitivity) or
       SELF-CONTAINEDLY (the clock inequalities pull only the facts they need and
       drop the rest) — so NO tactic ever runs a full-context `fs` over the doubled
       hypothesis set, whose nested nat-subtraction clock bounds otherwise make the
       arithmetic decision procedure blow up. *)
    `memFrame s' s`
       by (irule memFrame_trans >> qexists_tac `s2` >> conj_tac >>
           first_assum ACCEPT_TAC) >>
    `keepSaved s' s`
       by (irule keepSaved_trans >> qexists_tac `s2` >> conj_tac >>
           first_assum ACCEPT_TAC) >>
    `evaluate (scanLoop, s) = (NONE, s')` by (ASM_REWRITE_TAC []) >>
    `?bb. FLOOKUP s'.locals (strlit "b") = SOME (ValWord bb)`
       by (qpat_assum `FLOOKUP s'.locals (strlit "b") = _` mp_tac >>
           rpt (pop_assum kall_tac) >> metis_tac []) >>
    `LENGTH input - i = (LENGTH input - (i + 1)) + 1`
       by (qpat_assum `i < LENGTH input /\ found = 0` mp_tac >>
           rpt (pop_assum kall_tac) >> strip_tac >> DECIDE_TAC) >>
    `s.clock - (LENGTH input - i) <= s'.clock`
       by (qpat_assum `s2.clock - _ <= s'.clock` mp_tac >>
           qpat_assum `s2.clock = _` mp_tac >>
           qpat_assum `LENGTH input - i = _` mp_tac >>
           rpt (pop_assum kall_tac) >> rpt strip_tac >> DECIDE_TAC) >>
    `s'.clock <= s.clock`
       by (qpat_assum `s'.clock <= s2.clock` mp_tac >>
           qpat_assum `s2.clock = _` mp_tac >>
           rpt (pop_assum kall_tac) >> rpt strip_tac >> DECIDE_TAC) >>
    conj_tac >- (first_assum ACCEPT_TAC) >>
    conj_tac >- (first_assum ACCEPT_TAC) >>
    conj_tac >- (qpat_assum `FLOOKUP s'.locals (strlit "b") = _` mp_tac >>
                 rpt (pop_assum kall_tac) >> metis_tac []) >>
    conj_tac >- (first_assum ACCEPT_TAC) >>
    conj_tac >- (first_assum ACCEPT_TAC) >>
    first_assum ACCEPT_TAC) >>
  (* no iteration: guard false at s. Either found = 1 or i = LENGTH input.
     The outer Cases_on has put ~(i < LENGTH input /\ found = 0) in context.
     The IH is not needed here — drop it before any simp/fs. *)
  qpat_x_assum `!input bs i found s. _` kall_tac >>
  `eval s scanGuard = SOME (ValWord 0w)` by (drule eval_scanGuard >> fs []) >>
  `evaluate (scanLoop, s) = (NONE, s)`
     by (simp [scanLoop_def, Once evaluate_def] >> fs []) >>
  qexists_tac `s` >>
  imp_res_tac scanInv_flookup >>
  `keepSaved s s` by rw [keepSaved_def] >>
  `memFrame s s` by simp [memFrame_refl] >>
  `?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)`
     by (drule scanInv_b_exists >> disch_then ACCEPT_TAC) >>
  rpt conj_tac >> fs []
QED
val _ = (print "CKPT_DONE: scanLoop_frame\n"; TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   `scanLoop_run` — the exit summary the composition consumes, RECONSTRUCTED
   non-inductively.  Statement identical to C6's original framing lemma (exit
   `scanInv` + clock bounds + locals frame), but PROVED by combining, over the
   SAME exit state:
     * `scanLoop_frame`         — the memory equality + scalar frame + clocks;
     * `scanLoop_scan_bounded`  — the scan witness (offset «i»/«found») and the
                                  prefix facts (both `memRel`-free, from C5).
   `memRel` for the exit state is rebuilt from `memRel input bs s` + the memory
   equality — so the byte-quantifier is reintroduced exactly once, at the top
   level, never inside an induction.
   --------------------------------------------------------------------------- *)
Theorem scanLoop_run:
  !k input bs i found s.
    scanInv input bs i found s /\ LENGTH input - i <= k /\
    LENGTH input - i <= s.clock ==>
    ?s' j f. evaluate (scanLoop, s) = (NONE, s') /\
             scanInv input bs j f s' /\
             (f = 1 ==> j < LENGTH input /\ EL j input = 32) /\
             (f = 0 ==> j = LENGTH input) /\
             FLOOKUP s'.locals (strlit "found") = SOME (ValWord (n2w f)) /\
             FLOOKUP s'.locals (strlit "i") = SOME (ValWord (n2w j)) /\
             s.clock - (LENGTH input - i) <= s'.clock /\
             s'.clock <= s.clock /\
             keepSaved s' s
Proof
  rpt strip_tac >>
  (* scalar facts about the START state (used to rebuild memRel for the exit) *)
  `FLOOKUP s.locals (strlit "len")  = SOME (ValWord (n2w (LENGTH input))) /\
   FLOOKUP s.locals (strlit "base") = SOME (ValWord bs) /\
   memRel input bs s /\ LENGTH input < 2n ** 63 /\ EVERY (\x. x < 256) input`
     by fs [scanInv_def] >>
  (* the scan witness + prefix facts (memRel-free, C5) — fixes the exit state s' *)
  drule_all scanLoop_scan_bounded >> strip_tac >>
  map_every qexists_tac [`s'`,`j`,`f`] >>
  (* the memory/scalar frame over the SAME exit state s' (unify by determinism) *)
  drule_all scanLoop_frame >> strip_tac >>
  gvs [] >>
  (* unfold the (opaque) frame ONCE, non-inductively, into its field equalities *)
  `s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
   FLOOKUP s'.locals (strlit "len")  = FLOOKUP s.locals (strlit "len") /\
   FLOOKUP s'.locals (strlit "base") = FLOOKUP s.locals (strlit "base")`
     by fs [memFrame_def] >>
  (* rebuild the exit invariant, non-inductively *)
  `FLOOKUP s'.locals (strlit "len")  = SOME (ValWord (n2w (LENGTH input)))` by fs [] >>
  `FLOOKUP s'.locals (strlit "base") = SOME (ValWord bs)` by fs [] >>
  `memRel input bs s'` by fs [memRel_def] >>
  (* close the whole remaining goal (scanInv rebuilt + witness/clock/keepSaved).
     `f` has been substituted to its concrete value (0 or 1) by `gvs`, so we do NOT
     name it; `simp [scanInv_def]` unfolds the exit invariant and `fs`/`metis`
     discharge every conjunct from the assembled facts (metis handles the «b»
     existential from its stripped witness). *)
  simp [scanInv_def] >> fs [] >> metis_tac []
QED
val _ = (print "CKPT_DONE: scanLoop_run\n"; TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   The emitted program: TWO C5 scans composed by a reshaping block.
   --------------------------------------------------------------------------- *)

(* setup2: save the first scan result, reshape locals for a fresh scan over
   rest1 = DROP (i1+1) line at base buf + (i1+1), length |line| - (i1+1). *)
Definition setup2_def:
  setup2 =
    Seq (Assign Local (strlit "i1") (Var Local (strlit "i")))
   (Seq (Assign Local (strlit "found1") (Var Local (strlit "found")))
   (Seq (Assign Local (strlit "base")
           (Op Add [Var Local (strlit "base");
                    Op Add [Var Local (strlit "i"); Const (1w:word64)]]))
   (Seq (Assign Local (strlit "len")
           (Op Sub [Var Local (strlit "len");
                    Op Add [Var Local (strlit "i"); Const (1w:word64)]]))
   (Seq (Assign Local (strlit "i") (Const (0w:word64)))
        (Assign Local (strlit "found") (Const (0w:word64)))))))
End

Definition twoScan_def:
  twoScan = Seq scanLoop (Seq setup2 scanLoop)
End

(* The loaded precondition — the C4-style whole-program frame's postcondition:
   the request line is in the buffer, len/base set, the loop locals fresh, and
   the two save-slots «i1»/«found1» pre-declared (Dec'd) so `setup2` may write
   them. Directly gives C5's `scanInv line buf 0 0`. *)
Definition loadedReq_def:
  loadedReq (line:num list) (buf:word64) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "i")     = SOME (ValWord 0w) /\
    FLOOKUP s.locals (strlit "found") = SOME (ValWord 0w) /\
    FLOOKUP s.locals (strlit "len")   = SOME (ValWord (n2w (LENGTH line))) /\
    FLOOKUP s.locals (strlit "base")  = SOME (ValWord buf) /\
    (?bb. FLOOKUP s.locals (strlit "b")  = SOME (ValWord bb)) /\
    (?v1. FLOOKUP s.locals (strlit "i1") = SOME (ValWord v1)) /\
    (?v2. FLOOKUP s.locals (strlit "found1") = SOME (ValWord v2)) /\
    memRel line buf s /\
    LENGTH line < 2n ** 63 /\ EVERY (\x. x < 256) line
End

Theorem loadedReq_scanInv:
  loadedReq line buf s ==> scanInv line buf 0 0 s
Proof
  rw [loadedReq_def, scanInv_def] >> fs []
QED
val _ = (print "CKPT_DONE: loadedReq_scanInv\n"; TextIO.flushOut TextIO.stdOut);

(* The reshaping block, evaluated: from the first scan's exit (an SP found at
   offset i1), `setup2` saves i1 into «i1», leaves «found1» = 1, and re-establishes
   C5's `scanInv` for a FRESH scan over rest1 at the shifted base — the key
   compositional step. *)
Theorem evaluate_setup2:
  scanInv line buf i1 1 s1 /\
  (?v1. FLOOKUP s1.locals (strlit "i1") = SOME (ValWord v1)) /\
  (?v2. FLOOKUP s1.locals (strlit "found1") = SOME (ValWord v2)) ==>
  ?s2s. evaluate (setup2, s1) = (NONE, s2s) /\ s2s.clock = s1.clock /\
        FLOOKUP s2s.locals (strlit "i1") = SOME (ValWord (n2w i1)) /\
        FLOOKUP s2s.locals (strlit "found1") = SOME (ValWord 1w) /\
        scanInv (DROP (i1 + 1) line) (buf + n2w (i1 + 1)) 0 0 s2s
Proof
  strip_tac >>
  `i1 < LENGTH line /\ EL i1 line = 32` by fs [scanInv_def] >>
  `FLOOKUP s1.locals (strlit "i")     = SOME (ValWord (n2w i1)) /\
   FLOOKUP s1.locals (strlit "found") = SOME (ValWord (n2w 1)) /\
   FLOOKUP s1.locals (strlit "len")   = SOME (ValWord (n2w (LENGTH line))) /\
   FLOOKUP s1.locals (strlit "base")  = SOME (ValWord buf) /\
   (?bb. FLOOKUP s1.locals (strlit "b") = SOME (ValWord bb)) /\
   memRel line buf s1 /\ LENGTH line < 2n ** 63 /\ EVERY (\x. x < 256) line`
     by fs [scanInv_def] >>
  (* key disequalities on the string locals *)
  `strlit "i1" <> strlit "found" /\ strlit "i1" <> strlit "i" /\
   strlit "i1" <> strlit "len" /\ strlit "i1" <> strlit "base" /\
   strlit "i1" <> strlit "b" /\ strlit "i1" <> strlit "found1" /\
   strlit "found1" <> strlit "found" /\ strlit "found1" <> strlit "i" /\
   strlit "found1" <> strlit "len" /\ strlit "found1" <> strlit "base" /\
   strlit "found1" <> strlit "b" /\
   strlit "base" <> strlit "i" /\ strlit "base" <> strlit "len" /\
   strlit "base" <> strlit "found" /\ strlit "base" <> strlit "b" /\
   strlit "len" <> strlit "i" /\ strlit "len" <> strlit "found" /\
   strlit "len" <> strlit "b" /\ strlit "len" <> strlit "base" /\
   strlit "i" <> strlit "found" /\ strlit "i" <> strlit "b" /\
   strlit "found" <> strlit "b"` by EVAL_TAC >>
  (* the six intermediate states *)
  qabbrev_tac `t1 = set_var (strlit "i1") (ValWord (n2w i1)) s1` >>
  qabbrev_tac `t2 = set_var (strlit "found1") (ValWord (n2w 1)) t1` >>
  qabbrev_tac `t3 = set_var (strlit "base") (ValWord (buf + n2w (i1 + 1))) t2` >>
  qabbrev_tac `t4 = set_var (strlit "len")
                      (ValWord (n2w (LENGTH line - (i1 + 1)))) t3` >>
  qabbrev_tac `t5 = set_var (strlit "i") (ValWord (0w:word64)) t4` >>
  qabbrev_tac `t6 = set_var (strlit "found") (ValWord (0w:word64)) t5` >>
  (* A1 *)
  `evaluate (Assign Local (strlit "i1") (Var Local (strlit "i")), s1) = (NONE, t1)`
     by (simp [Once evaluate_def, eval_def, Abbr `t1`, is_valid_value_def,
               lookup_kvar_def, shape_of_def]) >>
  (* A2 *)
  `FLOOKUP t1.locals (strlit "found") = SOME (ValWord (n2w 1)) /\
   (?w. FLOOKUP t1.locals (strlit "found1") = SOME (ValWord w))`
     by simp [Abbr `t1`, set_var_def, FLOOKUP_UPDATE] >>
  `evaluate (Assign Local (strlit "found1") (Var Local (strlit "found")), t1)
     = (NONE, t2)`
     by (simp [Once evaluate_def, eval_def, Abbr `t2`, is_valid_value_def,
               lookup_kvar_def, shape_of_def] >> fs []) >>
  (* A3 : base := base + (i + 1) *)
  `FLOOKUP t2.locals (strlit "base") = SOME (ValWord buf) /\
   FLOOKUP t2.locals (strlit "i") = SOME (ValWord (n2w i1))`
     by simp [Abbr `t2`, Abbr `t1`, set_var_def, FLOOKUP_UPDATE] >>
  `(n2w i1 + 1w : word64) = n2w (i1 + 1)` by simp [word_add_n2w] >>
  `evaluate (Assign Local (strlit "base")
       (Op Add [Var Local (strlit "base");
                Op Add [Var Local (strlit "i"); Const (1w:word64)]]), t2)
     = (NONE, t3)`
     by (simp [Once evaluate_def, eval_def, OPT_MMAP_def,
               wordLangTheory.word_op_def, WORD_ADD_0, Abbr `t3`,
               is_valid_value_def, lookup_kvar_def, shape_of_def] >>
         fs [WORD_ADD_ASSOC]) >>
  (* A4 : len := len - (i + 1) *)
  `FLOOKUP t3.locals (strlit "len") = SOME (ValWord (n2w (LENGTH line))) /\
   FLOOKUP t3.locals (strlit "i") = SOME (ValWord (n2w i1))`
     by simp [Abbr `t3`, Abbr `t2`, Abbr `t1`, set_var_def, FLOOKUP_UPDATE] >>
  `i1 + 1 <= LENGTH line` by DECIDE_TAC >>
  `(n2w (LENGTH line) - n2w (i1 + 1) : word64) = n2w (LENGTH line - (i1 + 1))`
     by fs [n2w_sub_le] >>
  `eval t3 (Op Sub [Var Local (strlit "len");
                    Op Add [Var Local (strlit "i"); Const (1w:word64)]])
     = SOME (ValWord (n2w (LENGTH line - (i1 + 1))))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, WORD_ADD_0,
               word_add_n2w] >> fs [word_add_n2w, n2w_sub_norm]) >>
  `evaluate (Assign Local (strlit "len")
       (Op Sub [Var Local (strlit "len");
                Op Add [Var Local (strlit "i"); Const (1w:word64)]]), t3)
     = (NONE, t4)`
     by (simp [Once evaluate_def, Abbr `t4`,
               is_valid_value_def, lookup_kvar_def, shape_of_def] >> fs []) >>
  (* A5 : i := 0 *)
  `?w. FLOOKUP t4.locals (strlit "i") = SOME (ValWord w)`
     by simp [Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`, set_var_def, FLOOKUP_UPDATE] >>
  `evaluate (Assign Local (strlit "i") (Const (0w:word64)), t4) = (NONE, t5)`
     by (simp [Once evaluate_def, eval_def, Abbr `t5`, is_valid_value_def,
               lookup_kvar_def, shape_of_def] >> fs []) >>
  (* A6 : found := 0 *)
  `?w. FLOOKUP t5.locals (strlit "found") = SOME (ValWord w)`
     by simp [Abbr `t5`, Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`, set_var_def,
              FLOOKUP_UPDATE] >>
  `evaluate (Assign Local (strlit "found") (Const (0w:word64)), t5) = (NONE, t6)`
     by (simp [Once evaluate_def, eval_def, Abbr `t6`, is_valid_value_def,
               lookup_kvar_def, shape_of_def] >> fs []) >>
  (* clocks all preserved *)
  `t1.clock = s1.clock /\ t2.clock = s1.clock /\ t3.clock = s1.clock /\
   t4.clock = s1.clock /\ t5.clock = s1.clock /\ t6.clock = s1.clock`
     by simp [Abbr `t6`, Abbr `t5`, Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`,
              set_var_def] >>
  (* assemble the six Assigns via Seq_NONE (clock equal throughout) *)
  `evaluate (setup2, s1) = (NONE, t6)`
     by (simp [setup2_def] >>
         irule Seq_NONE >> qexists_tac `t1` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         irule Seq_NONE >> qexists_tac `t2` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         irule Seq_NONE >> qexists_tac `t3` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         irule Seq_NONE >> qexists_tac `t4` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         irule Seq_NONE >> qexists_tac `t5` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         fs []) >>
  qexists_tac `t6` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- fs [] >>
  (* «i1» = n2w i1 (set by A1, untouched after) *)
  `FLOOKUP t6.locals (strlit "i1") = SOME (ValWord (n2w i1))`
     by simp [Abbr `t6`, Abbr `t5`, Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`,
              set_var_def, FLOOKUP_UPDATE] >>
  `FLOOKUP t6.locals (strlit "found1") = SOME (ValWord (n2w 1))`
     by simp [Abbr `t6`, Abbr `t5`, Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`,
              set_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (fs [] >> simp []) >>
  (* the fresh scanInv over rest1 at the shifted base *)
  `memRel line buf t6`
     by (fs [memRel_def, Abbr `t6`, Abbr `t5`, Abbr `t4`, Abbr `t3`, Abbr `t2`,
             Abbr `t1`, set_var_def]) >>
  `memRel (DROP (i1 + 1) line) (buf + n2w (i1 + 1)) t6`
     by (irule memRel_DROP >> fs []) >>
  `EVERY (\x. x < 256) (DROP (i1 + 1) line)`
     by (irule EVERY_DROP >> fs []) >>
  simp [scanInv_def] >>
  `FLOOKUP t6.locals (strlit "i") = SOME (ValWord 0w) /\
   FLOOKUP t6.locals (strlit "found") = SOME (ValWord 0w) /\
   FLOOKUP t6.locals (strlit "len") =
     SOME (ValWord (n2w (LENGTH (DROP (i1 + 1) line)))) /\
   FLOOKUP t6.locals (strlit "base") = SOME (ValWord (buf + n2w (i1 + 1))) /\
   (?bb. FLOOKUP t6.locals (strlit "b") = SOME (ValWord bb))`
     by (simp [Abbr `t6`, Abbr `t5`, Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`,
               set_var_def, FLOOKUP_UPDATE, LENGTH_DROP] >> fs []) >>
  simp [LENGTH_DROP] >> fs []
QED
val _ = (print "CKPT_DONE: evaluate_setup2\n"; TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   THE COMPOSITION — Link A for the method|target split, by composing TWO C5
   scans. Whenever the Lean `parseRequestLine off line` returns SOME spans, the
   emitted `twoScan` runs to completion and computes the method length into «i1»
   and the target length into «i», with the offsets exactly the Lean spans.
   --------------------------------------------------------------------------- *)
Theorem twoScan_refines_parseReqLine:
  loadedReq line buf s /\ 2 * LENGTH line <= s.clock /\
  parseReqLine off line = SOME ((mOff,mLen),(tOff,tLen),(vOff,vLen)) ==>
  ?s'. evaluate (twoScan, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "found1") = SOME (ValWord 1w) /\
       FLOOKUP s'.locals (strlit "found")  = SOME (ValWord 1w) /\
       FLOOKUP s'.locals (strlit "i1") = SOME (ValWord (n2w mLen)) /\
       FLOOKUP s'.locals (strlit "i")  = SOME (ValWord (n2w tLen)) /\
       mOff = off /\ tOff = off + mLen + 1
Proof
  strip_tac >>
  drule parseReqLine_SOME >> strip_tac >>
  (* names: i1 = mLen (method length), i2 = tLen (target length) *)
  qabbrev_tac `i1 = mLen` >> qabbrev_tac `i2 = tLen` >>
  `scanSp line = SOME i1` by fs [Abbr `i1`] >>
  `scanSp (DROP (i1 + 1) line) = SOME i2` by fs [Abbr `i1`, Abbr `i2`] >>
  (* --- SCAN 1 : loadedReq -> scanInv line buf 0 0, run via scanLoop_run --- *)
  `scanInv line buf 0 0 s` by (irule loadedReq_scanInv >> fs []) >>
  `LENGTH line <= s.clock` by fs [] >>
  qspecl_then [`LENGTH line`,`line`,`buf`,`0`,`0`,`s`] mp_tac scanLoop_run >>
  impl_tac >- fs [] >> strip_tac >>
  (* the first scan's result offset is i1 (via the C5 refinement theorem) *)
  `?s1'. evaluate (scanLoop, s) = (NONE, s1') /\
         FLOOKUP s1'.locals (strlit "found") = SOME (ValWord 1w) /\
         FLOOKUP s1'.locals (strlit "i") = SOME (ValWord (n2w i1))`
     by (drule_all scanLoop_refines_findSp >> strip_tac >> gvs []) >>
  (* determinism: s1' = s' from scanLoop_run *)
  `s1' = s'` by fs [] >>
  gvs [] >>
  (* from scanLoop_run: found-witness f = 1, j = i1; so scanInv line buf i1 1 s' *)
  `f = 0 \/ f = 1` by fs [scanInv_def] >>
  `f = 1` by (Cases_on `f = 0` >> gvs []) >>
  gvs [] >>
  (* `gvs` has already rewritten the exit «i» value to `j`; recover `j = i1` from
     the scan spec: scanInv (found = 1) gives the SP facts at `j`, so `scanSp line
     = SOME j`, which with `scanSp line = SOME i1` forces `j = i1`. *)
  `j < LENGTH line /\ EL j line = 32 /\ EVERY (\b. b <> 32) (TAKE j line)`
     by fs [scanInv_def] >>
  `scanSp line = SOME j` by (irule scanSp_found >> fs []) >>
  `j = i1` by fs [] >>
  gvs [] >>
  `scanInv line buf i1 1 s'` by fs [] >>
  (* «i1»/«found1» survived scan 1 via the locals frame *)
  (* --- SETUP 2 : reshape for the fresh scan over rest1.  Apply `evaluate_setup2`
     by matching its (existential) conclusion, so its existential FLOOKUP
     preconditions are proved as GOALS (from loadedReq + keepSaved) rather than
     unified against already-stripped hypotheses. *)
  `?s2s. evaluate (setup2, s') = (NONE, s2s) /\ s2s.clock = s'.clock /\
         FLOOKUP s2s.locals (strlit "i1") = SOME (ValWord (n2w i1)) /\
         FLOOKUP s2s.locals (strlit "found1") = SOME (ValWord 1w) /\
         scanInv (DROP (i1 + 1) line) (buf + n2w (i1 + 1)) 0 0 s2s`
     by (irule evaluate_setup2 >> fs [loadedReq_def, keepSaved_def]) >>
  (* --- SCAN 2 : run scanLoop over rest1, get target length i2 --- *)
  qabbrev_tac `rest1 = DROP (i1 + 1) line` >>
  `LENGTH rest1 <= s2s.clock`
     by (`s2s.clock = s'.clock` by fs [] >>
         `LENGTH line <= s'.clock` by fs [] >>
         `LENGTH rest1 <= LENGTH line` by simp [Abbr `rest1`, LENGTH_DROP] >>
         fs []) >>
  qspecl_then [`LENGTH rest1`,`rest1`,`buf + n2w (i1 + 1)`,`0`,`0`,`s2s`]
     mp_tac scanLoop_run >>
  impl_tac >- fs [] >> strip_tac >>
  `?s2'. evaluate (scanLoop, s2s) = (NONE, s2') /\
         FLOOKUP s2'.locals (strlit "found") = SOME (ValWord 1w) /\
         FLOOKUP s2'.locals (strlit "i") = SOME (ValWord (n2w i2))`
     by (drule_all scanLoop_refines_findSp >> strip_tac >> gvs []) >>
  (* determinism: s2' = the scanLoop_run result state (call it s'') *)
  `s2' = s''` by fs [] >>
  gvs [] >>
  (* recover `j = i2` for the SECOND scan, exactly as for the first: found = 1, so
     scanInv gives the SP facts at `j`, hence `scanSp rest1 = SOME j`, and with
     `scanSp rest1 = SOME i2` we get `j = i2`. *)
  `f = 0 \/ f = 1` by fs [scanInv_def] >>
  `f = 1` by (Cases_on `f = 0` >> gvs []) >>
  gvs [] >>
  `j < LENGTH rest1 /\ EL j rest1 = 32 /\ EVERY (\b. b <> 32) (TAKE j rest1)`
     by fs [scanInv_def] >>
  `scanSp rest1 = SOME j` by (irule scanSp_found >> fs []) >>
  `j = i2` by fs [] >>
  gvs [] >>
  (* «i1»/«found1» survive scan 2 via the frame (untouched by the loop) *)
  `FLOOKUP s''.locals (strlit "i1") = SOME (ValWord (n2w i1)) /\
   FLOOKUP s''.locals (strlit "found1") = SOME (ValWord 1w)`
     by fs [keepSaved_def] >>
  (* --- COMPOSE the three phases into twoScan --- *)
  `evaluate (twoScan, s) = (NONE, s'')`
     by (simp [twoScan_def] >>
         irule Seq_NONE_le >> qexists_tac `s'` >> conj_tac >- fs [] >>
         conj_tac >- fs [] >>
         irule Seq_NONE_le >> qexists_tac `s2s` >>
         conj_tac >- fs [] >> conj_tac >- fs [] >> fs []) >>
  qexists_tac `s''` >>
  fs []
QED
val _ = (print "CKPT_DONE: twoScan_refines_parseReqLine\n"; TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   The failure path: when the request line has NO first space, the emitted first
   scan leaves «found» = 0 — the emitted program signals `parseRequestLine = none`
   exactly where the Lean parser does. (Composes the NONE case of the C5 scan.)
   --------------------------------------------------------------------------- *)
Theorem twoScan_firstNoSp:
  loadedReq line buf s /\ LENGTH line <= s.clock /\ scanSp line = NONE ==>
  ?s1. evaluate (scanLoop, s) = (NONE, s1) /\
       FLOOKUP s1.locals (strlit "found") = SOME (ValWord 0w)
Proof
  strip_tac >>
  `scanInv line buf 0 0 s` by (irule loadedReq_scanInv >> fs []) >>
  drule_all scanLoop_refines_findSp >> strip_tac >> gvs []
QED
val _ = (print "CKPT_DONE: twoScan_firstNoSp\n"; TextIO.flushOut TextIO.stdOut);

val _ = export_theory ();
