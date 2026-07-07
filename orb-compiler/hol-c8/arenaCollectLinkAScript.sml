(* ===========================================================================
   C8 probe — LINK A for the REAL VARIABLE-LENGTH COLLECTOR: a single scan-push
   loop that READS the input byte-by-byte and PUSHES a DATA-DEPENDENT number of
   records to a bump-allocated arena, the pushed content DERIVED FROM THE DATA
   (the offset at which each delimiter occurs), proven against real `panSem`.

   C7 proved two allocation bites: `writeSpans` (FIXED count, the real parser's
   three spans) and `fillLoop` (GENERAL N, but SCHEMATIC content record k = k, a
   pure counter — it never reads the input).  The residual C7 named verbatim was
   the fully-real collector: "collectSp: scan the input and PUSH each delimiter
   offset — variable count from the DATA, not a counter", which "additionally
   READS the input every iteration", its soundness "exactly the separation lemma
   memRel_store_disjoint threaded through the combined scan-read + bump-push
   induction".  THIS THEORY assembles exactly that.

   The emitted loop is
       i = 0; bp = out;
       while (i < len) {
         b = ld8 (base + i);
         if (b == 32) { st bp, i;  bp = bp + 8; }   // PUSH the delimiter offset
         i = i + 1;
       }
   Its arena ends ENCODING exactly `collectSp input` = the list of offsets of the
   delimiter bytes, IN ORDER — a data-dependent COUNT and data-derived CONTENT.

   The proof threads BOTH relations through ONE induction:
     * `memRel input bs`  — the input byte-read relation (C3), preserved across
       every bump-push because the arena write is DISJOINT from the input buffer
       (`memRel_store_disjoint`, C7, discharged by a separation precondition), and
     * `wordsEncoded (collectFrom 0 (TAKE i input))` — the arena layout relation,
       which each PUSH extends by one record (`wordsEncoded_snoc`, the data-driven
       generalisation of C7's schematic `wordsEncoded_extend`).

   Reuses verbatim: `memRel`, `w2w_byte`, `Seq_NONE`, `fix_clock_id` (C3);
   `signed_lt_n2w64` (C2); `TAKE_SUC_SNOC` (C5); `wordsEncoded`, `slot8_neq`,
   `eval_storeVar`, `eval_assign_addC`, `memRel_store_disjoint` (C7).  What is NEW
   is the SCAN-READ + CONDITIONAL BUMP-PUSH body and the combined induction with
   both relations live at once.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory bitTheory wordsTheory wordsLib
     finite_mapTheory combinTheory;
open panLangTheory panSemTheory;
open machineStepLinkATheory;      (* signed_lt_n2w64                             *)
open machineLoopLinkATheory;      (* memRel, w2w_byte, Seq_NONE, fix_clock_id    *)
open arenaScanLinkATheory;        (* TAKE_SUC_SNOC                               *)
open arenaAllocLinkATheory;       (* wordsEncoded, slot8_neq, eval_storeVar,
                                     eval_assign_addC, memRel_store_disjoint      *)

val _ = new_theory "arenaCollectLinkA";

fun ck s = (print ("\nCKPT_DONE: " ^ s ^ "\n"); TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   THE LEAN/HOL SPEC.  `collectFrom off input` scans `input` and emits, IN ORDER,
   the offset `off + position` of every delimiter byte (SP = 32).  The RESULT is a
   `List num` whose LENGTH is data-dependent (the number of delimiters) and whose
   CONTENT is data-derived (the offsets where the input holds a delimiter).
   `collectSp input = collectFrom 0 input`.
   --------------------------------------------------------------------------- *)
Definition collectFrom_def:
  (collectFrom (off:num) [] = []) /\
  (collectFrom (off:num) (b::bs) =
     if b = 32n then off :: collectFrom (off + 1) bs
     else collectFrom (off + 1) bs)
End

Definition collectSp_def:
  collectSp input = collectFrom 0 input
End

(* collectFrom distributes over append, its offset shifting by the prefix length —
   the fact that turns the loop's one-byte extension into a list SNOC. *)
Theorem collectFrom_append:
  !(off:num) xs ys.
    collectFrom off (xs ++ ys) =
    collectFrom off xs ++ collectFrom (off + LENGTH xs) ys
Proof
  Induct_on `xs` >> rw [collectFrom_def] >> fs [ADD1, ADD_CLAUSES]
QED
val _ = ck "collectFrom_append";

(* The collected list is no longer than the input scanned. *)
Theorem collectFrom_length_le:
  !(off:num) xs. LENGTH (collectFrom off xs) <= LENGTH xs
Proof
  Induct_on `xs` >> rw [collectFrom_def] >>
  `LENGTH (collectFrom (off + 1) xs) <= LENGTH xs` by fs [] >> fs []
QED
val _ = ck "collectFrom_length_le";

(* One scan step, DELIMITER HIT: the prefix collection gains the offset i. *)
Theorem collect_step_hit:
  i < LENGTH input /\ EL i input = 32 ==>
  collectFrom 0 (TAKE (i + 1) input) = collectFrom 0 (TAKE i input) ++ [i]
Proof
  strip_tac >>
  `TAKE (i + 1) input = TAKE i input ++ [EL i input]` by (irule TAKE_SUC_SNOC >> fs []) >>
  `LENGTH (TAKE i input) = i` by simp [LENGTH_TAKE] >>
  simp [collectFrom_append, collectFrom_def]
QED
val _ = ck "collect_step_hit";

(* One scan step, DELIMITER MISS: the prefix collection is unchanged. *)
Theorem collect_step_miss:
  i < LENGTH input /\ EL i input <> 32 ==>
  collectFrom 0 (TAKE (i + 1) input) = collectFrom 0 (TAKE i input)
Proof
  strip_tac >>
  `TAKE (i + 1) input = TAKE i input ++ [EL i input]` by (irule TAKE_SUC_SNOC >> fs []) >>
  `LENGTH (TAKE i input) = i` by simp [LENGTH_TAKE] >>
  simp [collectFrom_append, collectFrom_def]
QED
val _ = ck "collect_step_miss";

(* ---------------------------------------------------------------------------
   THE LAYOUT-PRESERVATION lemma for a DATA-DRIVEN push.  Writing value `v` at the
   next bump slot (offset 8*LENGTH xs) extends the encoded list by one record —
   the earlier records survive (distinct, lower slots), the new record is written.
   This is C7's `wordsEncoded_extend` GENERALISED off the schematic `record k = k`
   to an arbitrary pushed value `v` at the end of `xs` (the real collector content).
   --------------------------------------------------------------------------- *)
Theorem wordsEncoded_snoc:
  wordsEncoded xs outB s /\ 8 * LENGTH xs < dimword (:64) /\
  s2.memory = ((outB + n2w (8 * LENGTH xs)) =+ Word (n2w v)) s.memory ==>
  wordsEncoded (xs ++ [v]) outB s2
Proof
  rw [wordsEncoded_def] >>
  `k < LENGTH xs \/ k = LENGTH xs` by (fs [] >> DECIDE_TAC)
  >- (
    `8 * k < dimword (:64)` by (irule LESS_TRANS >> qexists_tac `8 * LENGTH xs` >> fs []) >>
    `outB + n2w (8 * k) <> outB + n2w (8 * LENGTH xs)` by (irule slot8_neq >> fs []) >>
    `s.memory (outB + n2w (8 * k)) = Word (n2w (EL k xs))` by fs [wordsEncoded_def] >>
    simp [APPLY_UPDATE_THM, EL_APPEND1]) >>
  simp [APPLY_UPDATE_THM, EL_APPEND2]
QED
val _ = ck "wordsEncoded_snoc";

(* ---------------------------------------------------------------------------
   THE EMITTED COLLECTOR (real panLang AST, the transcription of collect.pnk).
     collectGuard : i < len
     collectBody  : b = ld8(base+i); if (b==32) { st bp,i; bp = bp+8; } i = i+1;
   --------------------------------------------------------------------------- *)
Definition collectGuard_def:
  collectGuard = Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len"))
End

Definition collectBody_def:
  collectBody =
    Seq (Assign Local (strlit "b")
           (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")])))
   (Seq (If (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
            (Seq (Store (Var Local (strlit "bp")) (Var Local (strlit "i")))
                 (Assign Local (strlit "bp")
                    (Op Add [Var Local (strlit "bp"); Const (8w:word64)])))
            Skip)
        (Assign Local (strlit "i")
           (Op Add [Var Local (strlit "i"); Const (1w:word64)])))
End

Definition collectLoop_def:
  collectLoop = While collectGuard collectBody
End

(* ---------------------------------------------------------------------------
   THE INVARIANT.  Carries: the scan index i; the emitted scalars; the bump
   pointer bp = out + 8*(number pushed so far) = out + 8*LENGTH(prefix collect);
   the input READ relation `memRel`; arena availability; the SEPARATION
   precondition (every arena slot is byte-disjoint from every input byte — the
   hypothesis `memRel_store_disjoint` consumes); and the arena LAYOUT relation
   `wordsEncoded (collectFrom 0 (TAKE i input))` — the arena holds exactly the
   offsets collected from the first i bytes.  BOTH relations live at once.
   --------------------------------------------------------------------------- *)
Definition colInv_def:
  colInv (input:num list) (bs:word64) (outB:word64) (i:num)
         (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "i")    = SOME (ValWord (n2w i)) /\
    FLOOKUP s.locals (strlit "len")  = SOME (ValWord (n2w (LENGTH input))) /\
    FLOOKUP s.locals (strlit "base") = SOME (ValWord bs) /\
    FLOOKUP s.locals (strlit "bp")   =
       SOME (ValWord (outB + n2w (8 * LENGTH (collectFrom 0 (TAKE i input))))) /\
    (?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)) /\
    memRel input bs s /\
    i <= LENGTH input /\ LENGTH input < 2n ** 63 /\ 8 * LENGTH input < dimword (:64) /\
    EVERY (\x. x < 256) input /\
    (!j. j < LENGTH input ==> (outB + n2w (8 * j)) IN s.memaddrs) /\
    (!m j. m < LENGTH input /\ j < LENGTH input ==>
             outB + n2w (8 * m) <> byte_align (bs + n2w j)) /\
    wordsEncoded (collectFrom 0 (TAKE i input)) outB s
End

(* The invariant depends only on locals/memory, so the While's clock tick keeps it. *)
Theorem colInv_clock:
  colInv input bs outB i s ==> colInv input bs outB i (s with clock := ck)
Proof
  rw [colInv_def, memRel_def, wordsEncoded_def]
QED
val _ = ck "colInv_clock";

(* The compound guard `i < len` evaluates to keep-going iff i < |input|. *)
Theorem eval_collectGuard:
  colInv input bs outB i s ==>
    eval s collectGuard = SOME (ValWord (if i < LENGTH input then 1w else 0w))
Proof
  strip_tac >>
  `FLOOKUP s.locals (strlit "i") = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals (strlit "len") = SOME (ValWord (n2w (LENGTH input))) /\
   i <= LENGTH input /\ LENGTH input < 2n ** 63` by fs [colInv_def] >>
  `i < 2n ** 63` by (irule LESS_EQ_LESS_TRANS >> qexists_tac `LENGTH input` >> fs []) >>
  `(n2w i:word64 < n2w (LENGTH input)) = (i < LENGTH input)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [collectGuard_def, eval_def, asmTheory.word_cmp_def]
QED
val _ = ck "eval_collectGuard";

(* The i-th input byte read, via the input relation `memRel` + the byte-widening
   `w2w_byte` (the scan-read half of each iteration). *)
Theorem eval_col_loadbyte:
  FLOOKUP s.locals (strlit "base") = SOME (ValWord bs) /\
  FLOOKUP s.locals (strlit "i") = SOME (ValWord (n2w i)) /\
  memRel input bs s /\ i < LENGTH input /\ EL i input < 256 ==>
  eval s (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")]))
    = SOME (ValWord ((n2w (EL i input)):word64))
Proof
  strip_tac >>
  `mem_load_byte s.memory s.memaddrs s.be (bs + n2w i) = SOME ((n2w (EL i input)):word8)`
     by fs [memRel_def] >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, WORD_ADD_0, w2w_byte]
QED
val _ = ck "eval_col_loadbyte";

(* ---------------------------------------------------------------------------
   ONE ITERATION of the collector body — the crux.  Reads the i-th byte, then
   BRANCHES: on a delimiter it PUSHES the offset i to the arena and advances the
   bump pointer; otherwise it does nothing.  Either way it advances i, PRESERVES
   `memRel` (the push is byte-disjoint from the input, `memRel_store_disjoint`),
   and RE-ESTABLISHES the layout relation at i+1 (a HIT extends it by one record
   via `wordsEncoded_snoc`; a MISS leaves it, matching `collect_step_miss`).
   --------------------------------------------------------------------------- *)
Theorem collectBody_step:
  colInv input bs outB i s /\ i < LENGTH input ==>
    ?s2. evaluate (collectBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         colInv input bs outB (i + 1) s2
Proof
  strip_tac >>
  `EL i input < 256` by (fs [colInv_def, EVERY_EL]) >>
  qabbrev_tac `coli = collectFrom 0 (TAKE i input)` >>
  qabbrev_tac `k = LENGTH coli` >>
  `FLOOKUP s.locals (strlit "i") = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals (strlit "len") = SOME (ValWord (n2w (LENGTH input))) /\
   FLOOKUP s.locals (strlit "base") = SOME (ValWord bs) /\
   FLOOKUP s.locals (strlit "bp") = SOME (ValWord (outB + n2w (8 * k))) /\
   (?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)) /\
   memRel input bs s /\ i <= LENGTH input /\ LENGTH input < 2n ** 63 /\
   8 * LENGTH input < dimword (:64) /\ EVERY (\x. x < 256) input /\
   (!j. j < LENGTH input ==> (outB + n2w (8 * j)) IN s.memaddrs) /\
   (!m j. m < LENGTH input /\ j < LENGTH input ==>
            outB + n2w (8 * m) <> byte_align (bs + n2w j)) /\
   wordsEncoded coli outB s`
     by fs [colInv_def, Abbr `coli`, Abbr `k`] >>
  (* the bump slot in use is within the arena and the word range *)
  `k <= i`
     by (`LENGTH (collectFrom 0 (TAKE i input)) <= LENGTH (TAKE i input)`
            by metis_tac [collectFrom_length_le] >>
         `LENGTH (TAKE i input) = i` by simp [LENGTH_TAKE] >>
         fs [Abbr `k`, Abbr `coli`]) >>
  `k < LENGTH input` by fs [] >>
  `8 * k < dimword (:64)`
     by (irule LESS_EQ_LESS_TRANS >> qexists_tac `8 * LENGTH input` >> fs []) >>
  (* read the i-th byte *)
  `eval s (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")]))
     = SOME (ValWord ((n2w (EL i input)):word64))`
     by (irule eval_col_loadbyte >> fs []) >>
  (* string-key disequalities for the FLOOKUP_UPDATE reductions *)
  `strlit "b" <> strlit "i" /\ strlit "b" <> strlit "len" /\ strlit "b" <> strlit "base" /\
   strlit "b" <> strlit "bp" /\ strlit "i" <> strlit "b" /\ strlit "i" <> strlit "len" /\
   strlit "i" <> strlit "base" /\ strlit "i" <> strlit "bp" /\
   strlit "bp" <> strlit "b" /\ strlit "bp" <> strlit "i" /\ strlit "bp" <> strlit "len" /\
   strlit "bp" <> strlit "base"` by EVAL_TAC >>
  qabbrev_tac `bv = (n2w (EL i input)):word64` >>
  qabbrev_tac `sA = set_var (strlit "b") (ValWord bv) s` >>
  `sA.clock = s.clock /\ sA.memory = s.memory /\ sA.memaddrs = s.memaddrs /\ sA.be = s.be`
     by simp [Abbr `sA`, set_var_def] >>
  `evaluate (Assign Local (strlit "b")
       (LoadByte (Op Add [Var Local (strlit "base"); Var Local (strlit "i")])), s)
     = (NONE, sA)`
     by (simp [Once evaluate_def, Abbr `sA`] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  `FLOOKUP sA.locals (strlit "b") = SOME (ValWord bv) /\
   FLOOKUP sA.locals (strlit "i") = SOME (ValWord (n2w i)) /\
   FLOOKUP sA.locals (strlit "bp") = SOME (ValWord (outB + n2w (8 * k))) /\
   FLOOKUP sA.locals (strlit "len") = SOME (ValWord (n2w (LENGTH input))) /\
   FLOOKUP sA.locals (strlit "base") = SOME (ValWord bs)`
     by simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  `memRel input bs sA` by fs [memRel_def, Abbr `sA`, set_var_def] >>
  `wordsEncoded coli outB sA` by fs [wordsEncoded_def, Abbr `sA`, set_var_def] >>
  (* the delimiter test *)
  `(n2w (EL i input) = (32w:word64)) = (EL i input = 32)`
     by (`EL i input < dimword (:64)` by (`(256:num) < dimword (:64)` by EVAL_TAC >> fs []) >>
         `(32:num) < dimword (:64)` by EVAL_TAC >> simp [n2w_11] >> fs [LESS_MOD]) >>
  `eval sA (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
     = SOME (ValWord (if EL i input = 32 then 1w else 0w))`
     by simp [eval_def, asmTheory.word_cmp_def, Abbr `bv`] >>
  `(1w:word64) <> 0w` by EVAL_TAC >>
  Cases_on `EL i input = 32`
  >- (
    (* ===== DELIMITER HIT: push offset i, advance bp ===== *)
    `eval sA (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64))) = SOME (ValWord 1w)`
       by fs [] >>
    (* the push: Store i at bp = out + 8k *)
    `(outB + n2w (8 * k)) IN sA.memaddrs`
       by (`sA.memaddrs = s.memaddrs` by simp [Abbr `sA`, set_var_def] >> fs []) >>
    `evaluate (Store (Var Local (strlit "bp")) (Var Local (strlit "i")), sA)
       = (NONE, sA with memory := ((outB + n2w (8 * k)) =+ Word (n2w i)) sA.memory)`
       by (irule eval_storeVar >> fs []) >>
    qabbrev_tac `sS = sA with memory := ((outB + n2w (8 * k)) =+ Word (n2w i)) sA.memory` >>
    `sS.clock = s.clock /\ sS.memaddrs = s.memaddrs /\ sS.be = s.be /\
     sS.memory = ((outB + n2w (8 * k)) =+ Word (n2w i)) s.memory`
       by simp [Abbr `sS`, Abbr `sA`, set_var_def] >>
    `FLOOKUP sS.locals (strlit "bp") = SOME (ValWord (outB + n2w (8 * k)))`
       by simp [Abbr `sS`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
    (* the bump advance: bp := bp + 8 *)
    `evaluate (Assign Local (strlit "bp")
         (Op Add [Var Local (strlit "bp"); Const (8w:word64)]), sS)
       = (NONE, set_var (strlit "bp") (ValWord (8w + (outB + n2w (8 * k)))) sS)`
       by (irule eval_assign_addC >> first_assum ACCEPT_TAC) >>
    qabbrev_tac `sB = set_var (strlit "bp") (ValWord (8w + (outB + n2w (8 * k)))) sS` >>
    `evaluate (Seq (Store (Var Local (strlit "bp")) (Var Local (strlit "i")))
                   (Assign Local (strlit "bp")
                      (Op Add [Var Local (strlit "bp"); Const (8w:word64)])), sA)
       = (NONE, sB)`
       by (irule Seq_NONE >> qexists_tac `sS` >> rpt conj_tac >>
           TRY (first_assum ACCEPT_TAC) >> simp [Abbr `sS`, Abbr `sA`, set_var_def]) >>
    (* the If takes the then-branch *)
    `evaluate (If (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
                  (Seq (Store (Var Local (strlit "bp")) (Var Local (strlit "i")))
                       (Assign Local (strlit "bp")
                          (Op Add [Var Local (strlit "bp"); Const (8w:word64)])))
                  Skip, sA)
       = (NONE, sB)`
       by (simp [Once evaluate_def] >> fs []) >>
    (* i := i + 1 *)
    `FLOOKUP sB.locals (strlit "i") = SOME (ValWord (n2w i))`
       by simp [Abbr `sB`, Abbr `sS`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
    `evaluate (Assign Local (strlit "i")
         (Op Add [Var Local (strlit "i"); Const (1w:word64)]), sB)
       = (NONE, set_var (strlit "i") (ValWord (1w + n2w i)) sB)`
       by (irule eval_assign_addC >> first_assum ACCEPT_TAC) >>
    qabbrev_tac `sC = set_var (strlit "i") (ValWord (1w + n2w i)) sB` >>
    `evaluate (Seq (If (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
                  (Seq (Store (Var Local (strlit "bp")) (Var Local (strlit "i")))
                       (Assign Local (strlit "bp")
                          (Op Add [Var Local (strlit "bp"); Const (8w:word64)])))
                  Skip)
                (Assign Local (strlit "i")
                   (Op Add [Var Local (strlit "i"); Const (1w:word64)])), sA)
       = (NONE, sC)`
       by (irule Seq_NONE >> qexists_tac `sB` >> rpt conj_tac >>
           TRY (first_assum ACCEPT_TAC) >>
           simp [Abbr `sB`, Abbr `sS`, Abbr `sA`, set_var_def]) >>
    `evaluate (collectBody, s) = (NONE, sC)`
       by (simp [collectBody_def] >> irule Seq_NONE >> qexists_tac `sA` >> rpt conj_tac >>
           TRY (first_assum ACCEPT_TAC) >> simp [Abbr `sA`, set_var_def]) >>
    qexists_tac `sC` >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- simp [Abbr `sC`, Abbr `sB`, Abbr `sS`, Abbr `sA`, set_var_def] >>
    (* address / count normalisations (explicit REWRITE, never a word-arith simp) *)
    `(8w + (outB + n2w (8 * k)) : word64) = outB + n2w (8 * (k + 1))`
       by (`8w + outB = outB + 8w : word64` by metis_tac [WORD_ADD_COMM] >>
           `8w + (outB + n2w (8 * k)) = outB + (8w + n2w (8 * k)) : word64`
              by (REWRITE_TAC [WORD_ADD_ASSOC] >> asm_rewrite_tac []) >>
           `8w + n2w (8 * k) = n2w (8 * (k + 1)) : word64`
              by (REWRITE_TAC [word_add_n2w] >> AP_TERM_TAC >> DECIDE_TAC) >>
           asm_rewrite_tac []) >>
    `(1w + n2w i : word64) = n2w (i + 1)`
       by (REWRITE_TAC [word_add_n2w] >> AP_TERM_TAC >> DECIDE_TAC) >>
    (* the prefix collection gains the offset i (HIT) *)
    `collectFrom 0 (TAKE (i + 1) input) = coli ++ [i]`
       by (`collectFrom 0 (TAKE (i + 1) input) = collectFrom 0 (TAKE i input) ++ [i]`
              by (irule collect_step_hit >> fs []) >>
           fs [Abbr `coli`]) >>
    `LENGTH coli = k` by fs [Abbr `k`] >>
    (* sC memory/memaddrs/locals in normalised form *)
    `sC.memory = ((outB + n2w (8 * k)) =+ Word (n2w i)) s.memory /\
     sC.memaddrs = s.memaddrs /\ sC.be = s.be`
       by simp [Abbr `sC`, Abbr `sB`, Abbr `sS`, Abbr `sA`, set_var_def] >>
    `FLOOKUP sC.locals (strlit "i") = SOME (ValWord (n2w (i + 1)))`
       by (simp [Abbr `sC`, set_var_def, FLOOKUP_UPDATE] >>
           qpat_x_assum `1w + n2w i = _` (fn th => rewrite_tac [th])) >>
    `FLOOKUP sC.locals (strlit "bp") =
        SOME (ValWord (outB + n2w (8 * LENGTH (collectFrom 0 (TAKE (i + 1) input)))))`
       by (simp [Abbr `sC`, Abbr `sB`, set_var_def, FLOOKUP_UPDATE] >>
           `LENGTH (collectFrom 0 (TAKE (i + 1) input)) = k + 1` by fs [] >>
           asm_rewrite_tac [] >>
           qpat_x_assum `8w + (outB + n2w (8 * k)) = _` (fn th => rewrite_tac [th])) >>
    `FLOOKUP sC.locals (strlit "len") = SOME (ValWord (n2w (LENGTH input))) /\
     FLOOKUP sC.locals (strlit "base") = SOME (ValWord bs) /\
     (?bb. FLOOKUP sC.locals (strlit "b") = SOME (ValWord bb))`
       by (simp [Abbr `sC`, Abbr `sB`, Abbr `sS`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
           metis_tac []) >>
    (* memRel preserved: the push is byte-disjoint from the input *)
    `!j. j < LENGTH input ==> outB + n2w (8 * k) <> byte_align (bs + n2w j)`
       by (rpt strip_tac >> first_x_assum (qspecl_then [`k`, `j`] mp_tac) >> simp []) >>
    `memRel input bs (s with memory := ((outB + n2w (8 * k)) =+ Word (n2w i)) s.memory)`
       by (irule memRel_store_disjoint >> fs []) >>
    `memRel input bs sC` by fs [memRel_def] >>
    (* the layout relation at i+1 via the data-driven push extension *)
    `wordsEncoded (coli ++ [i]) outB sC`
       by (`8 * LENGTH coli < dimword (:64)` by fs [] >>
           `sC.memory = ((outB + n2w (8 * LENGTH coli)) =+ Word (n2w i)) s.memory`
              by fs [] >>
           metis_tac [wordsEncoded_snoc]) >>
    `wordsEncoded (collectFrom 0 (TAKE (i + 1) input)) outB sC` by fs [] >>
    (* arena availability + separation transfer (memaddrs unchanged) *)
    `!j. j < LENGTH input ==> (outB + n2w (8 * j)) IN sC.memaddrs`
       by (rw [] >> `(outB + n2w (8 * j)) IN s.memaddrs` by fs [] >>
           qpat_x_assum `sC.memaddrs = s.memaddrs` (fn th => fs [th])) >>
    `i + 1 <= LENGTH input` by fs [] >>
    simp [colInv_def] >> fs []) >>
  (* ===== DELIMITER MISS: no push, just advance i ===== *)
  `eval sA (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64))) = SOME (ValWord 0w)`
     by fs [] >>
  `evaluate (If (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
                (Seq (Store (Var Local (strlit "bp")) (Var Local (strlit "i")))
                     (Assign Local (strlit "bp")
                        (Op Add [Var Local (strlit "bp"); Const (8w:word64)])))
                Skip, sA)
     = (NONE, sA)`
     by (simp [Once evaluate_def] >> fs [] >> simp [evaluate_def]) >>
  `evaluate (Assign Local (strlit "i")
       (Op Add [Var Local (strlit "i"); Const (1w:word64)]), sA)
     = (NONE, set_var (strlit "i") (ValWord (1w + n2w i)) sA)`
     by (irule eval_assign_addC >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `sC = set_var (strlit "i") (ValWord (1w + n2w i)) sA` >>
  `evaluate (Seq (If (Cmp Equal (Var Local (strlit "b")) (Const (32w:word64)))
                (Seq (Store (Var Local (strlit "bp")) (Var Local (strlit "i")))
                     (Assign Local (strlit "bp")
                        (Op Add [Var Local (strlit "bp"); Const (8w:word64)])))
                Skip)
              (Assign Local (strlit "i")
                 (Op Add [Var Local (strlit "i"); Const (1w:word64)])), sA)
     = (NONE, sC)`
     by (irule Seq_NONE >> qexists_tac `sA` >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC) >> simp [Abbr `sA`, set_var_def]) >>
  `evaluate (collectBody, s) = (NONE, sC)`
     by (simp [collectBody_def] >> irule Seq_NONE >> qexists_tac `sA` >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC) >> simp [Abbr `sA`, set_var_def]) >>
  qexists_tac `sC` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp [Abbr `sC`, Abbr `sA`, set_var_def] >>
  `(1w + n2w i : word64) = n2w (i + 1)`
     by (REWRITE_TAC [word_add_n2w] >> AP_TERM_TAC >> DECIDE_TAC) >>
  (* the prefix collection is unchanged (MISS) *)
  `collectFrom 0 (TAKE (i + 1) input) = coli`
     by (`collectFrom 0 (TAKE (i + 1) input) = collectFrom 0 (TAKE i input)`
            by (irule collect_step_miss >> fs []) >>
         fs [Abbr `coli`]) >>
  `sC.memory = s.memory /\ sC.memaddrs = s.memaddrs`
     by simp [Abbr `sC`, Abbr `sA`, set_var_def] >>
  `FLOOKUP sC.locals (strlit "i") = SOME (ValWord (n2w (i + 1)))`
     by (simp [Abbr `sC`, set_var_def, FLOOKUP_UPDATE] >>
         qpat_x_assum `1w + n2w i = _` (fn th => rewrite_tac [th])) >>
  `FLOOKUP sC.locals (strlit "bp") =
      SOME (ValWord (outB + n2w (8 * LENGTH (collectFrom 0 (TAKE (i + 1) input)))))`
     by (simp [Abbr `sC`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
         `LENGTH (collectFrom 0 (TAKE (i + 1) input)) = k` by fs [Abbr `k`] >>
         asm_rewrite_tac []) >>
  `FLOOKUP sC.locals (strlit "len") = SOME (ValWord (n2w (LENGTH input))) /\
   FLOOKUP sC.locals (strlit "base") = SOME (ValWord bs) /\
   (?bb. FLOOKUP sC.locals (strlit "b") = SOME (ValWord bb))`
     by (simp [Abbr `sC`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >> metis_tac []) >>
  `memRel input bs sC` by fs [memRel_def, Abbr `sC`, Abbr `sA`, set_var_def] >>
  `wordsEncoded (collectFrom 0 (TAKE (i + 1) input)) outB sC`
     by (`wordsEncoded coli outB sC` by fs [wordsEncoded_def, Abbr `sC`, Abbr `sA`, set_var_def] >>
         fs []) >>
  `!j. j < LENGTH input ==> (outB + n2w (8 * j)) IN sC.memaddrs`
     by (rw [] >> `(outB + n2w (8 * j)) IN s.memaddrs` by fs [] >>
         qpat_x_assum `sC.memaddrs = s.memaddrs` (fn th => fs [th])) >>
  `i + 1 <= LENGTH input` by fs [] >>
  simp [colInv_def] >> fs []
QED
val _ = ck "collectBody_step";

(* One emitted `While` iteration: guard live + clock > 0 reduces the loop at s to
   the loop at the branch-updated s2, one clock tick spent. *)
Theorem collectLoop_unfold:
  colInv input bs outB i s /\ i < LENGTH input /\ s.clock <> 0 ==>
  ?s2. evaluate (collectLoop, s) = evaluate (collectLoop, s2) /\
       s2.clock = s.clock - 1 /\ colInv input bs outB (i + 1) s2
Proof
  strip_tac >>
  `eval s collectGuard = SOME (ValWord 1w)` by (drule eval_collectGuard >> fs []) >>
  `colInv input bs outB i (dec_clock s)`
     by (simp [dec_clock_def] >> irule colInv_clock >> fs []) >>
  `?s2. evaluate (collectBody, dec_clock s) = (NONE, s2) /\
        s2.clock = (dec_clock s).clock /\ colInv input bs outB (i + 1) s2`
     by (irule collectBody_step >> fs []) >>
  qexists_tac `s2` >>
  `s2.clock <= (dec_clock s).clock` by fs [] >>
  `evaluate (collectLoop, s) = evaluate (collectLoop, s2)`
     by (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [collectLoop_def] THENC
                              ONCE_REWRITE_CONV [evaluate_def])) >>
         simp [GSYM collectLoop_def, fix_clock_id] >> fs [fix_clock_id]) >>
  `s2.clock = s.clock - 1` by fs [dec_clock_def] >> fs []
QED
val _ = ck "collectLoop_unfold";

(* ---------------------------------------------------------------------------
   LINK A FOR THE COLLECTOR — the combined scan-read + bump-push induction over
   the clocked `While`.  From an invariant state at index i with clock >= the
   remaining bytes, the emitted loop TERMINATES (no TimeOut) and the arena ENCODES
   `collectFrom 0 input` — the full data-dependent list of delimiter offsets — with
   the bump pointer at out + 8*LENGTH(that list) (the allocation consumed).
   --------------------------------------------------------------------------- *)
Theorem collectLoop_run:
  !m input bs outB i s.
    colInv input bs outB i s /\ LENGTH input - i <= m /\ LENGTH input - i <= s.clock ==>
    ?s'. evaluate (collectLoop, s) = (NONE, s') /\
         wordsEncoded (collectFrom 0 input) outB s' /\
         FLOOKUP s'.locals (strlit "bp") =
            SOME (ValWord (outB + n2w (8 * LENGTH (collectFrom 0 input))))
Proof
  Induct_on `m`
  >- (
    rpt strip_tac >>
    `i = LENGTH input` by fs [colInv_def] >>
    `eval s collectGuard = SOME (ValWord 0w)` by (drule eval_collectGuard >> fs []) >>
    qexists_tac `s` >>
    `evaluate (collectLoop, s) = (NONE, s)` by (simp [collectLoop_def, Once evaluate_def]) >>
    `TAKE i input = input` by (rw [] >> simp [TAKE_LENGTH_ID]) >>
    `wordsEncoded (collectFrom 0 input) outB s /\
     FLOOKUP s.locals (strlit "bp") =
        SOME (ValWord (outB + n2w (8 * LENGTH (collectFrom 0 input))))`
       by (fs [colInv_def]) >>
    fs []) >>
  rpt strip_tac >>
  Cases_on `i < LENGTH input`
  >- (
    `s.clock <> 0` by fs [] >>
    drule_all collectLoop_unfold >> strip_tac >>
    last_x_assum (qspecl_then [`input`, `bs`, `outB`, `i + 1`, `s2`] mp_tac) >>
    impl_tac >- fs [] >>
    strip_tac >> qexists_tac `s'` >> fs []) >>
  `i = LENGTH input` by fs [colInv_def] >>
  `eval s collectGuard = SOME (ValWord 0w)` by (drule eval_collectGuard >> fs []) >>
  qexists_tac `s` >>
  `evaluate (collectLoop, s) = (NONE, s)` by (simp [collectLoop_def, Once evaluate_def]) >>
  `TAKE i input = input` by (rw [] >> simp [TAKE_LENGTH_ID]) >>
  `wordsEncoded (collectFrom 0 input) outB s /\
   FLOOKUP s.locals (strlit "bp") =
      SOME (ValWord (outB + n2w (8 * LENGTH (collectFrom 0 input))))`
     by (fs [colInv_def]) >>
  fs []
QED
val _ = ck "collectLoop_run";

(* ---------------------------------------------------------------------------
   THE HEADLINE — Link A for the REAL VARIABLE-LENGTH COLLECTOR.  From a fresh
   (i=0, bp=out) state with clock >= |input| and the separation precondition, the
   emitted `While` builds, in the arena, EXACTLY the Lean spec `collectSp input`
   (the ordered list of delimiter offsets — data-dependent COUNT and data-derived
   CONTENT), with the bump pointer advanced to out + 8*LENGTH(collectSp input).
   --------------------------------------------------------------------------- *)
Theorem collectLoop_refines_collectSp:
  FLOOKUP s.locals (strlit "i")    = SOME (ValWord 0w) /\
  FLOOKUP s.locals (strlit "len")  = SOME (ValWord (n2w (LENGTH input))) /\
  FLOOKUP s.locals (strlit "base") = SOME (ValWord bs) /\
  FLOOKUP s.locals (strlit "bp")   = SOME (ValWord outB) /\
  (?bb. FLOOKUP s.locals (strlit "b") = SOME (ValWord bb)) /\
  memRel input bs s /\ LENGTH input < 2n ** 63 /\ 8 * LENGTH input < dimword (:64) /\
  EVERY (\x. x < 256) input /\
  (!j. j < LENGTH input ==> (outB + n2w (8 * j)) IN s.memaddrs) /\
  (!m j. m < LENGTH input /\ j < LENGTH input ==>
           outB + n2w (8 * m) <> byte_align (bs + n2w j)) /\
  LENGTH input <= s.clock ==>
  ?s'. evaluate (collectLoop, s) = (NONE, s') /\
       wordsEncoded (collectSp input) outB s' /\
       FLOOKUP s'.locals (strlit "bp") =
          SOME (ValWord (outB + n2w (8 * LENGTH (collectSp input))))
Proof
  strip_tac >>
  `colInv input bs outB 0 s`
     by (simp [colInv_def, wordsEncoded_def, collectFrom_def] >> fs []) >>
  qspecl_then [`LENGTH input`, `input`, `bs`, `outB`, `0`, `s`] mp_tac collectLoop_run >>
  impl_tac >- fs [] >>
  strip_tac >> qexists_tac `s'` >> fs [collectSp_def]
QED
val _ = ck "collectLoop_refines_collectSp";

val _ = export_theory ();
