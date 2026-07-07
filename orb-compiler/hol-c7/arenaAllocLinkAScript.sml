(* ===========================================================================
   C7 probe — LINK A for the FIRST ALLOCATING, MEMORY-BUILDING engine emission:
   a bump-allocated ARRAY OF SPAN RECORDS written into Pancake memory, with a
   proven MEMORY-LAYOUT relation tying the flat bytes to the Lean spec's output
   `List Span`.

   Everything C0-C6 emitted was a first-order byte-SCAN over a flat immutable
   buffer: it READ bytes (LoadByte) and left its answer in LOCALS (or, in C4, a
   single result word). NOTHING built a data structure in memory. The adversarial
   critic named exactly that gap: "lists -> a verified allocator/GC" is the
   load-bearing RESEARCH item.

   C7 takes the first real bite. The output of `parseRequestLine` is a STRUCTURE:
   three spans, each an (offset,length) pair — a `List Span`. C7 EMITS a component
   that ALLOCATES a region at a bump pointer and WRITES those span records into it,
   and PROVES against real `panSem$evaluate` that the flat memory the emitted
   program produces ENCODES the Lean `parseReqLine` output list.

   The NEW machinery, none of which existed in C0-C6:
     * `spansEncoded` — the datatype-to-flat-memory LAYOUT RELATION: a Lean
       `List (num # num)` is represented at base `outB` iff, for each k, the k-th
       16-byte record at `outB + 16*k` holds the offset word (at +0) and the
       length word (at +8). This is the encoding the critic said does not exist.
     * `writeSpans` — the emitted allocating program: six `Store`s into the arena
       at a bump pointer that advances by the record-field size, leaving the
       advanced bump pointer (out + 48 = out + recordSize*count) in «bp».
     * `writeSpans_encodes` / `writeSpans_refines_parseReqLine` — LINK A: running
       the emitted writer builds, in the arena, EXACTLY the `List Span` the Lean
       parser returns.
     * `memRel_store_disjoint` — the SEPARATION lemma (the verified memory story):
       an output-arena write at an address disjoint from the input buffer
       preserves the input byte-relation `memRel`.  This is what makes an
       allocator that writes-while-it-reads sound, and it is the seam a general-N
       collect loop rides.

   Reuses verbatim: `memRel` (C3), the `parseReqLine` spec + `parseReqLine_SOME`
   (C6), `Seq_NONE` (C3).  What is NEW is memory-BUILDING: Store into a bump
   region + the layout relation + separation.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory bitTheory wordsTheory wordsLib
     finite_mapTheory combinTheory;
open panLangTheory panSemTheory;
open machineStepLinkATheory;
open machineLoopLinkATheory;      (* memRel, memRel_def, Seq_NONE                *)
open arenaScanLinkATheory;        (* scanSp, scanLoop, scanInv                   *)
open arenaParseLineLinkATheory;   (* parseReqLine, parseReqLine_SOME             *)

val _ = new_theory "arenaAllocLinkA";

fun ck s = (print ("\nCKPT_DONE: " ^ s ^ "\n"); TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   THE MEMORY-LAYOUT RELATION.  A Lean `List Span` (list of (offset,length)
   pairs) is REPRESENTED at flat base `outB` iff each 16-byte record encodes the
   corresponding span: offset word at `outB + 16*k`, length word at `outB + 16*k+8`.
   The panSem memory is `word -> word_lab`; a full-word Store lands a `Word w` at
   its (word-aligned) address, so the relation reads the raw memory function —
   exactly the shape C4 read its single result word back through.
   --------------------------------------------------------------------------- *)
Definition spansEncoded_def:
  spansEncoded (spans:(num # num) list) (outB:word64)
               (s:(64,'ffi) panSem$state) <=>
    !k. k < LENGTH spans ==>
        s.memory (outB + n2w (16 * k))     = Word (n2w (FST (EL k spans))) /\
        s.memory (outB + n2w (16 * k + 8)) = Word (n2w (SND (EL k spans)))
End

(* The Lean spec's structured output, as the flat list the arena must hold. *)
Definition spanListOf_def:
  (spanListOf (SOME ((mOff,mLen),(tOff,tLen),(vOff,vLen))) =
     [(mOff,mLen); (tOff,tLen); (vOff,vLen)]) /\
  (spanListOf NONE = [])
End

(* ---------------------------------------------------------------------------
   THE EMITTED ALLOCATING PROGRAM.  A bump-allocated arena at base «out»: six
   full-word Stores lay down three (offset,length) records; «bp» ends at
   out + 48 = out + recordSize*count (the advanced bump pointer — the allocator
   consumed 48 bytes).  Record 0 field 0 is at the arena base `out` itself; every
   later field is `out + const`.
   --------------------------------------------------------------------------- *)
Definition writeSpans_def:
  writeSpans =
    Seq (Store (Var Local (strlit "out"))
               (Var Local (strlit "mOff")))
   (Seq (Store (Op Add [Var Local (strlit "out"); Const (8w:word64)])
               (Var Local (strlit "mLen")))
   (Seq (Store (Op Add [Var Local (strlit "out"); Const (16w:word64)])
               (Var Local (strlit "tOff")))
   (Seq (Store (Op Add [Var Local (strlit "out"); Const (24w:word64)])
               (Var Local (strlit "tLen")))
   (Seq (Store (Op Add [Var Local (strlit "out"); Const (32w:word64)])
               (Var Local (strlit "vOff")))
   (Seq (Store (Op Add [Var Local (strlit "out"); Const (40w:word64)])
               (Var Local (strlit "vLen")))
        (Assign Local (strlit "bp")
           (Op Add [Var Local (strlit "out"); Const (48w:word64)])))))))
End

(* The arena availability precondition: the six record slots are writable. *)
Definition arena6_def:
  arena6 (outB:word64) (s:(64,'ffi) panSem$state) <=>
    outB IN s.memaddrs /\ (outB + 8w) IN s.memaddrs /\
    (outB + 16w) IN s.memaddrs /\ (outB + 24w) IN s.memaddrs /\
    (outB + 32w) IN s.memaddrs /\ (outB + 40w) IN s.memaddrs
End

(* One record-field write at the arena base: `Store (Var out) (Var fnm)` lands
   `Word w` at `outB`. *)
Theorem eval_storeBase:
  FLOOKUP s.locals (strlit "out") = SOME (ValWord outB) /\
  FLOOKUP s.locals fnm = SOME (ValWord w) /\
  outB IN s.memaddrs ==>
  evaluate (Store (Var Local (strlit "out")) (Var Local fnm), s)
    = (NONE, s with memory := (outB =+ Word w) s.memory)
Proof
  strip_tac >>
  simp [evaluate_def, eval_def, flatten_def, mem_stores_def, mem_store_def]
QED

(* One record-field write at offset `c`: `Store (out + c) (Var fnm)` lands
   `Word w` at `outB + c`. *)
Theorem eval_storeC:
  FLOOKUP s.locals (strlit "out") = SOME (ValWord outB) /\
  FLOOKUP s.locals fnm = SOME (ValWord w) /\
  (outB + c) IN s.memaddrs ==>
  evaluate (Store (Op Add [Var Local (strlit "out"); Const c])
                  (Var Local fnm), s)
    = (NONE, s with memory := ((outB + c) =+ Word w) s.memory)
Proof
  strip_tac >>
  simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        WORD_ADD_0, flatten_def, mem_stores_def, mem_store_def] >>
  `c + outB = outB + c` by simp [WORD_ADD_COMM] >> fs []
QED

(* Pairwise distinctness of the six record-slot addresses (word arithmetic,
   discharged by the bit-blaster). *)
Theorem arena_addrs_neq:
  ((outB:word64) <> outB + 8w) /\ (outB <> outB + 16w) /\ (outB <> outB + 24w) /\
  (outB <> outB + 32w) /\ (outB <> outB + 40w) /\
  (outB + 8w  <> outB) /\ (outB + 16w <> outB) /\ (outB + 24w <> outB) /\
  (outB + 32w <> outB) /\ (outB + 40w <> outB) /\
  (outB + 8w  <> outB + 16w) /\ (outB + 8w  <> outB + 24w) /\
  (outB + 8w  <> outB + 32w) /\ (outB + 8w  <> outB + 40w) /\
  (outB + 16w <> outB + 8w)  /\ (outB + 16w <> outB + 24w) /\
  (outB + 16w <> outB + 32w) /\ (outB + 16w <> outB + 40w) /\
  (outB + 24w <> outB + 8w)  /\ (outB + 24w <> outB + 16w) /\
  (outB + 24w <> outB + 32w) /\ (outB + 24w <> outB + 40w) /\
  (outB + 32w <> outB + 8w)  /\ (outB + 32w <> outB + 16w) /\
  (outB + 32w <> outB + 24w) /\ (outB + 32w <> outB + 40w) /\
  (outB + 40w <> outB + 8w)  /\ (outB + 40w <> outB + 16w) /\
  (outB + 40w <> outB + 24w) /\ (outB + 40w <> outB + 32w)
Proof
  rpt conj_tac >> blastLib.BBLAST_TAC
QED

(* ---------------------------------------------------------------------------
   LINK A (fixed count) — the emitted allocating writer BUILDS the three-span
   structure in the arena.  From a state holding the six span fields (as the
   parser leaves them) and an available arena, `writeSpans` runs to completion
   (NONE — no Error, no TimeOut), the arena memory ENCODES the list
   `[(mOff,mLen);(tOff,tLen);(vOff,vLen)]` (the layout relation `spansEncoded`),
   and the bump pointer «bp» is advanced to out + 48 (= recordSize*count).
   --------------------------------------------------------------------------- *)
Theorem writeSpans_encodes:
  FLOOKUP s.locals (strlit "out")  = SOME (ValWord outB) /\
  FLOOKUP s.locals (strlit "mOff") = SOME (ValWord (n2w mOff)) /\
  FLOOKUP s.locals (strlit "mLen") = SOME (ValWord (n2w mLen)) /\
  FLOOKUP s.locals (strlit "tOff") = SOME (ValWord (n2w tOff)) /\
  FLOOKUP s.locals (strlit "tLen") = SOME (ValWord (n2w tLen)) /\
  FLOOKUP s.locals (strlit "vOff") = SOME (ValWord (n2w vOff)) /\
  FLOOKUP s.locals (strlit "vLen") = SOME (ValWord (n2w vLen)) /\
  (?bpv. FLOOKUP s.locals (strlit "bp") = SOME (ValWord bpv)) /\
  arena6 outB s ==>
  ?s'. evaluate (writeSpans, s) = (NONE, s') /\
       spansEncoded [(mOff,mLen); (tOff,tLen); (vOff,vLen)] outB s' /\
       FLOOKUP s'.locals (strlit "bp") = SOME (ValWord (outB + 48w))
Proof
  strip_tac >>
  fs [arena6_def] >>
  `strlit "bp" <> strlit "out"` by EVAL_TAC >>
  qabbrev_tac `t1 = s  with memory := (outB          =+ Word (n2w mOff)) s.memory` >>
  qabbrev_tac `t2 = t1 with memory := ((outB + 8w)  =+ Word (n2w mLen)) t1.memory` >>
  qabbrev_tac `t3 = t2 with memory := ((outB + 16w) =+ Word (n2w tOff)) t2.memory` >>
  qabbrev_tac `t4 = t3 with memory := ((outB + 24w) =+ Word (n2w tLen)) t3.memory` >>
  qabbrev_tac `t5 = t4 with memory := ((outB + 32w) =+ Word (n2w vOff)) t4.memory` >>
  qabbrev_tac `t6 = t5 with memory := ((outB + 40w) =+ Word (n2w vLen)) t5.memory` >>
  `t1.locals = s.locals /\ t2.locals = s.locals /\ t3.locals = s.locals /\
   t4.locals = s.locals /\ t5.locals = s.locals /\ t6.locals = s.locals`
     by simp [Abbr `t1`, Abbr `t2`, Abbr `t3`, Abbr `t4`, Abbr `t5`, Abbr `t6`] >>
  `t1.memaddrs = s.memaddrs /\ t2.memaddrs = s.memaddrs /\ t3.memaddrs = s.memaddrs /\
   t4.memaddrs = s.memaddrs /\ t5.memaddrs = s.memaddrs /\ t6.memaddrs = s.memaddrs`
     by simp [Abbr `t1`, Abbr `t2`, Abbr `t3`, Abbr `t4`, Abbr `t5`, Abbr `t6`] >>
  `t1.clock = s.clock /\ t2.clock = s.clock /\ t3.clock = s.clock /\
   t4.clock = s.clock /\ t5.clock = s.clock /\ t6.clock = s.clock`
     by simp [Abbr `t1`, Abbr `t2`, Abbr `t3`, Abbr `t4`, Abbr `t5`, Abbr `t6`] >>
  (* the six stores, each unfold-target then apply the store lemma *)
  `evaluate (Store (Var Local (strlit "out")) (Var Local (strlit "mOff")), s)
     = (NONE, t1)`
     by (simp [Abbr `t1`] >> irule eval_storeBase >> fs []) >>
  `evaluate (Store (Op Add [Var Local (strlit "out"); Const (8w:word64)])
                   (Var Local (strlit "mLen")), t1) = (NONE, t2)`
     by (simp [Abbr `t2`] >> irule eval_storeC >> fs []) >>
  `evaluate (Store (Op Add [Var Local (strlit "out"); Const (16w:word64)])
                   (Var Local (strlit "tOff")), t2) = (NONE, t3)`
     by (simp [Abbr `t3`] >> irule eval_storeC >> fs []) >>
  `evaluate (Store (Op Add [Var Local (strlit "out"); Const (24w:word64)])
                   (Var Local (strlit "tLen")), t3) = (NONE, t4)`
     by (simp [Abbr `t4`] >> irule eval_storeC >> fs []) >>
  `evaluate (Store (Op Add [Var Local (strlit "out"); Const (32w:word64)])
                   (Var Local (strlit "vOff")), t4) = (NONE, t5)`
     by (simp [Abbr `t5`] >> irule eval_storeC >> fs []) >>
  `evaluate (Store (Op Add [Var Local (strlit "out"); Const (40w:word64)])
                   (Var Local (strlit "vLen")), t5) = (NONE, t6)`
     by (simp [Abbr `t6`] >> irule eval_storeC >> fs []) >>
  (* the bump-pointer advance: «bp» := out + 48 *)
  qabbrev_tac `t7 = set_var (strlit "bp") (ValWord (outB + 48w)) t6` >>
  `FLOOKUP t6.locals (strlit "out") = SOME (ValWord outB) /\
   (?bpv. FLOOKUP t6.locals (strlit "bp") = SOME (ValWord bpv))`
     by (fs [] >> metis_tac []) >>
  `evaluate (Assign Local (strlit "bp")
               (Op Add [Var Local (strlit "out"); Const (48w:word64)]), t6)
     = (NONE, t7)`
     by (simp [Once evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
               Abbr `t7`, is_valid_value_def, lookup_kvar_def, shape_of_def] >>
         `48w + outB = outB + 48w` by simp [WORD_ADD_COMM] >> fs []) >>
  `t7.clock = s.clock` by simp [Abbr `t7`, set_var_def] >>
  (* assemble via Seq_NONE (every step preserves the clock) *)
  `evaluate (writeSpans, s) = (NONE, t7)`
     by (simp [writeSpans_def] >>
         irule Seq_NONE >> qexists_tac `t1` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         irule Seq_NONE >> qexists_tac `t2` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         irule Seq_NONE >> qexists_tac `t3` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         irule Seq_NONE >> qexists_tac `t4` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         irule Seq_NONE >> qexists_tac `t5` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         irule Seq_NONE >> qexists_tac `t6` >> conj_tac >- fs [] >> conj_tac >- fs [] >>
         fs []) >>
  qexists_tac `t7` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  (* the final arena memory, as a stack of six updates over s.memory *)
  `t7.memory = ((outB + 40w) =+ Word (n2w vLen))
                (((outB + 32w) =+ Word (n2w vOff))
                 (((outB + 24w) =+ Word (n2w tLen))
                  (((outB + 16w) =+ Word (n2w tOff))
                   (((outB + 8w)  =+ Word (n2w mLen))
                    ((outB =+ Word (n2w mOff)) s.memory)))))`
     by simp [Abbr `t7`, Abbr `t6`, Abbr `t5`, Abbr `t4`, Abbr `t3`, Abbr `t2`,
              Abbr `t1`, set_var_def] >>
  conj_tac
  >- (
    (* spansEncoded: read each of the three records back through the update stack *)
    simp [spansEncoded_def] >> rpt strip_tac >>
    `k = 0 \/ k = 1 \/ k = 2` by DECIDE_TAC >>
    fs [] >>
    simp [APPLY_UPDATE_THM, arena_addrs_neq]) >>
  (* «bp» = out + 48 *)
  simp [Abbr `t7`, set_var_def, FLOOKUP_UPDATE]
QED
val _ = (print "CKPT_DONE: writeSpans_encodes\n"; TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   LINK A tied to the LEAN SPEC.  When the Lean `parseReqLine off line` returns
   SOME spans and those spans are the writer's inputs, the emitted allocating
   program builds, in the arena, EXACTLY the `List Span` the Lean parser returns:
   `spansEncoded (spanListOf (parseReqLine off line)) outB s'`.
   --------------------------------------------------------------------------- *)
Theorem writeSpans_refines_parseReqLine:
  parseReqLine off line = SOME ((mOff,mLen),(tOff,tLen),(vOff,vLen)) /\
  FLOOKUP s.locals (strlit "out")  = SOME (ValWord outB) /\
  FLOOKUP s.locals (strlit "mOff") = SOME (ValWord (n2w mOff)) /\
  FLOOKUP s.locals (strlit "mLen") = SOME (ValWord (n2w mLen)) /\
  FLOOKUP s.locals (strlit "tOff") = SOME (ValWord (n2w tOff)) /\
  FLOOKUP s.locals (strlit "tLen") = SOME (ValWord (n2w tLen)) /\
  FLOOKUP s.locals (strlit "vOff") = SOME (ValWord (n2w vOff)) /\
  FLOOKUP s.locals (strlit "vLen") = SOME (ValWord (n2w vLen)) /\
  (?bpv. FLOOKUP s.locals (strlit "bp") = SOME (ValWord bpv)) /\
  arena6 outB s ==>
  ?s'. evaluate (writeSpans, s) = (NONE, s') /\
       spansEncoded (spanListOf (parseReqLine off line)) outB s'
Proof
  strip_tac >>
  `?s'. evaluate (writeSpans, s) = (NONE, s') /\
        spansEncoded [(mOff,mLen); (tOff,tLen); (vOff,vLen)] outB s' /\
        FLOOKUP s'.locals (strlit "bp") = SOME (ValWord (outB + 48w))`
     by (irule writeSpans_encodes >> fs []) >>
  qexists_tac `s'` >> conj_tac >- first_assum ACCEPT_TAC >>
  `spanListOf (parseReqLine off line) = [(mOff,mLen); (tOff,tLen); (vOff,vLen)]`
     by asm_simp_tac (srw_ss()) [spanListOf_def] >>
  fs []
QED
val _ = (print "CKPT_DONE: writeSpans_refines_parseReqLine\n"; TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   THE SEPARATION LEMMA — the verified MEMORY STORY for an allocator that writes
   while it reads.  An output-arena write (a full-word Store at address `a`) that
   is DISJOINT from the input buffer preserves the input byte-relation `memRel`.
   This is the fact that makes writing records into a bump arena sound WHILE the
   scan still reads the input, and is the seam a general-N collect loop rides.

   `mem_load_byte` reads `m (byte_align w)`; a write at `a` is invisible to it
   exactly when `a <> byte_align (bs + n2w j)` for every in-range input byte j.
   --------------------------------------------------------------------------- *)
Theorem memRel_store_disjoint:
  memRel input bs s /\
  (!j. j < LENGTH input ==> a <> byte_align (bs + n2w j)) ==>
  memRel input bs (s with memory := (a =+ Word v) s.memory)
Proof
  rw [memRel_def] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp [] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp [] >>
  rpt strip_tac >>
  fs [mem_load_byte_def, APPLY_UPDATE_THM]
QED
val _ = (print "CKPT_DONE: memRel_store_disjoint\n"; TextIO.flushOut TextIO.stdOut);

(* ===========================================================================
   PART 3 — THE GENERAL-N BUMP-ALLOCATING LOOP.

   The fixed-count writer above lays down a KNOWN number of records with no loop.
   The load-bearing question the critic raised is whether the ALLOCATION mechanism
   is mechanical for a DATA-DEPENDENT count — i.e. a loop that bump-allocates and
   writes an UNBOUNDED number of records, with the layout relation proven by
   induction.  This part answers it: `fillLoop` writes N single-word records into
   the arena at a bump pointer that advances by the element size each iteration,
   and `fillLoop_refines` proves (against real `panSem`, by loop-invariant
   induction over the clocked `While`) that the arena ends ENCODING the length-N
   list the Lean spec returns — for ALL N.

   The element content here is schematic (`GENLIST (\i.i) N`, record k = k) — the
   point is the general bump-allocate-and-encode LOOP, not the payload.  The
   invariant threads the (growable) layout relation `wordsEncoded`; the induction
   skeleton is C5's `scanLoop_scan_bounded`, reused.  The one thing beyond a scan
   is that each iteration WRITES a record and the invariant re-establishes the
   layout relation at k+1 (previous records preserved by bump distinctness).
   =========================================================================== *)

(* A `List num` is laid out at base `outB` iff element k is the word at outB+8*k. *)
Definition wordsEncoded_def:
  wordsEncoded (xs:num list) (outB:word64) (s:(64,'ffi) panSem$state) <=>
    !k. k < LENGTH xs ==> s.memory (outB + n2w (8 * k)) = Word (n2w (EL k xs))
End
Definition fillGuard_def:
  fillGuard = Cmp Less (Var Local (strlit "k")) (Var Local (strlit "n"))
End
Definition fillBody_def:
  fillBody =
    Seq (Store (Var Local (strlit "bp")) (Var Local (strlit "k")))
   (Seq (Assign Local (strlit "bp") (Op Add [Var Local (strlit "bp"); Const (8w:word64)]))
        (Assign Local (strlit "k") (Op Add [Var Local (strlit "k"); Const (1w:word64)])))
End
Definition fillLoop_def:
  fillLoop = While fillGuard fillBody
End
Definition fillInv_def:
  fillInv (N:num) (outB:word64) (k:num) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "k")  = SOME (ValWord (n2w k)) /\
    FLOOKUP s.locals (strlit "n")  = SOME (ValWord (n2w N)) /\
    FLOOKUP s.locals (strlit "bp") = SOME (ValWord (outB + n2w (8 * k))) /\
    k <= N /\ N < 2n ** 63 /\ 8 * N < dimword (:64) /\
    (!j. j < N ==> (outB + n2w (8 * j)) IN s.memaddrs) /\
    wordsEncoded (GENLIST (\i. i) k) outB s
End

Theorem eval_storeVar:
  FLOOKUP s.locals vp = SOME (ValWord a) /\
  FLOOKUP s.locals vv = SOME (ValWord w) /\ a IN s.memaddrs ==>
  evaluate (Store (Var Local vp) (Var Local vv), s)
    = (NONE, s with memory := (a =+ Word w) s.memory)
Proof
  strip_tac >>
  simp [evaluate_def, eval_def, flatten_def, mem_stores_def, mem_store_def]
QED
val _ = (print "CKPT_DONE: eval_storeVar\n"; TextIO.flushOut TextIO.stdOut);

Theorem slot8_neq:
  !(outB:word64) j k. 8 * j < dimword (:64) /\ 8 * k < dimword (:64) /\ j <> k ==>
    outB + n2w (8 * j) <> outB + n2w (8 * k)
Proof
  rw [WORD_EQ_ADD_LCANCEL, n2w_11] >>
  `8 * j MOD dimword (:64) = 8 * j` by simp [] >>
  `8 * k MOD dimword (:64) = 8 * k` by simp [] >> fs []
QED
val _ = (print "CKPT_DONE: slot8_neq\n"; TextIO.flushOut TextIO.stdOut);

Theorem fillInv_clock:
  fillInv N outB k s ==> fillInv N outB k (s with clock := ck)
Proof
  rw [fillInv_def, wordsEncoded_def]
QED
val _ = (print "CKPT_DONE: fillInv_clock\n"; TextIO.flushOut TextIO.stdOut);

Theorem eval_fillGuard:
  fillInv N outB k s ==> eval s fillGuard = SOME (ValWord (if k < N then 1w else 0w))
Proof
  strip_tac >>
  `FLOOKUP s.locals (strlit "k") = SOME (ValWord (n2w k)) /\
   FLOOKUP s.locals (strlit "n") = SOME (ValWord (n2w N)) /\
   k <= N /\ N < 2n ** 63` by fs [fillInv_def] >>
  `k < 2n ** 63` by (irule LESS_EQ_LESS_TRANS >> qexists_tac `N` >> fs []) >>
  `(n2w k:word64 < n2w N) = (k < N)` by (irule signed_lt_n2w64 >> fs []) >>
  simp [fillGuard_def, eval_def, asmTheory.word_cmp_def]
QED
val _ = (print "CKPT_DONE: eval_fillGuard\n"; TextIO.flushOut TextIO.stdOut);

(* Scalar accessor: exposes ONLY the scalar/pointer facts + arena availability,
   NEVER the quantified `wordsEncoded` — so `fillBody_step`'s plumbing keeps the
   memory-layout quantifier out of the general simplifier context (the C6
   discipline against the `!k`-over-memory blowup). *)
Theorem fillInv_scalars:
  fillInv N outB k s ==>
    FLOOKUP s.locals (strlit "k")  = SOME (ValWord (n2w k)) /\
    FLOOKUP s.locals (strlit "n")  = SOME (ValWord (n2w N)) /\
    FLOOKUP s.locals (strlit "bp") = SOME (ValWord (outB + n2w (8 * k))) /\
    k <= N /\ N < 2n ** 63 /\ 8 * N < dimword (:64)
Proof
  rw [fillInv_def]
QED
val _ = ck "fillInv_scalars";

Theorem fillInv_arena:
  fillInv N outB k s ==> !j. j < N ==> (outB + n2w (8 * j)) IN s.memaddrs
Proof
  rw [fillInv_def]
QED
val _ = ck "fillInv_arena";

Theorem fillInv_words:
  fillInv N outB k s ==> wordsEncoded (GENLIST (\i. i) k) outB s
Proof
  rw [fillInv_def]
QED
val _ = ck "fillInv_words";

(* The LAYOUT-PRESERVATION lemma, PROVEN IN ISOLATION over a single symbolic
   state: writing element k at the k-th bump slot extends the encoded list from k
   to k+1 records — earlier records survive (distinct, lower slots), the new one
   is written.  Stated memory-only (any state whose memory is the updated one), so
   it applies to the post-body state regardless of its locals.  Isolating it here
   keeps `wordsEncoded`'s `!k` quantifier out of `fillBody_step`'s big context. *)
Theorem wordsEncoded_extend:
  wordsEncoded (GENLIST (\i. i) k) outB s /\ 8 * k < dimword (:64) /\
  s2.memory = ((outB + n2w (8 * k)) =+ Word (n2w k)) s.memory ==>
  wordsEncoded (GENLIST (\i. i) (k + 1)) outB s2
Proof
  rw [wordsEncoded_def] >>
  `k' < k \/ k' = k` by DECIDE_TAC
  >- (
    `8 * k' < dimword (:64)` by (irule LESS_TRANS >> qexists_tac `8 * k` >> fs []) >>
    `outB + n2w (8 * k') <> outB + n2w (8 * k)` by (irule slot8_neq >> fs []) >>
    `k' < LENGTH (GENLIST (\i. i) k)` by simp [] >>
    `s.memory (outB + n2w (8 * k')) = Word (n2w (EL k' (GENLIST (\i. i) k)))`
       by (fs [wordsEncoded_def]) >>
    simp [APPLY_UPDATE_THM, EL_GENLIST]) >>
  simp [APPLY_UPDATE_THM, EL_GENLIST]
QED
val _ = ck "wordsEncoded_extend";

(* `x := x + c` in one shot: the operational reduction done ONCE over a symbolic
   state (so `fillBody_step` never runs the heavy `evaluate`/`is_valid_value` simp
   over the big post-store state — the source of the plumbing churn). *)
Theorem eval_assign_addC:
  FLOOKUP s.locals vp = SOME (ValWord a) ==>
  evaluate (Assign Local vp (Op Add [Var Local vp; Const c]), s)
    = (NONE, set_var vp (ValWord (c + a)) s)
Proof
  strip_tac >>
  fs [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
      is_valid_value_def, lookup_kvar_def, shape_of_def, set_var_def]
QED
val _ = ck "eval_assign_addC";

(* ONE iteration of the body: writes element k at the bump pointer, advances bp
   by 8, increments k, and RE-ESTABLISHES the layout relation at k+1 via the
   isolated `wordsEncoded_extend` (the quantifier never enters this proof's
   context).  Scalars come from `fillInv_scalars`; `wordsEncoded` is fetched
   folded from `fillInv_words` and immediately handed to `wordsEncoded_extend`. *)
(* The WHOLE body evaluated in one shot, over a SYMBOLIC state (no giant memory
   term in context) — so all the operational simp runs cheaply.  `fillBody_step`
   just instantiates this, keeping every simp small. *)
Theorem fillBody_eval:
  FLOOKUP s.locals (strlit "bp") = SOME (ValWord bpw) /\
  FLOOKUP s.locals (strlit "k") = SOME (ValWord kv) /\
  bpw IN s.memaddrs ==>
  ?s'. evaluate (fillBody, s) = (NONE, s') /\
       s'.clock = s.clock /\ s'.memaddrs = s.memaddrs /\
       s'.memory = (bpw =+ Word kv) s.memory /\
       FLOOKUP s'.locals (strlit "bp") = SOME (ValWord (8w + bpw)) /\
       FLOOKUP s'.locals (strlit "k")  = SOME (ValWord (1w + kv)) /\
       FLOOKUP s'.locals (strlit "n")  = FLOOKUP s.locals (strlit "n")
Proof
  strip_tac >>
  `strlit "bp" <> strlit "k" /\ strlit "k" <> strlit "bp" /\
   strlit "bp" <> strlit "n" /\ strlit "k" <> strlit "n"` by EVAL_TAC >>
  qabbrev_tac `s1 = s with memory := (bpw =+ Word kv) s.memory` >>
  `evaluate (Store (Var Local (strlit "bp")) (Var Local (strlit "k")), s) = (NONE, s1)`
     by (simp [Abbr `s1`] >> irule eval_storeVar >> fs []) >>
  `s1.clock = s.clock /\ s1.memaddrs = s.memaddrs /\
   s1.memory = (bpw =+ Word kv) s.memory /\
   FLOOKUP s1.locals (strlit "bp") = SOME (ValWord bpw) /\
   FLOOKUP s1.locals (strlit "k")  = SOME (ValWord kv) /\
   FLOOKUP s1.locals (strlit "n")  = FLOOKUP s.locals (strlit "n")`
     by fs [Abbr `s1`] >>
  (* prove the evaluate with the lemma's EXPLICIT output (no simp to reorder the
     `8w + bpw` sum), then abstract that exact term as s2 *)
  `evaluate (Assign Local (strlit "bp")
       (Op Add [Var Local (strlit "bp"); Const (8w:word64)]), s1)
     = (NONE, set_var (strlit "bp") (ValWord (8w + bpw)) s1)`
     by (irule eval_assign_addC >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `s2 = set_var (strlit "bp") (ValWord (8w + bpw)) s1` >>
  `s2.clock = s.clock /\ s2.memaddrs = s.memaddrs /\
   s2.memory = (bpw =+ Word kv) s.memory /\
   FLOOKUP s2.locals (strlit "bp") = SOME (ValWord (8w + bpw)) /\
   FLOOKUP s2.locals (strlit "k")  = SOME (ValWord kv) /\
   FLOOKUP s2.locals (strlit "n")  = FLOOKUP s.locals (strlit "n")`
     by fs [Abbr `s2`, set_var_def, FLOOKUP_UPDATE] >>
  `evaluate (Assign Local (strlit "k")
       (Op Add [Var Local (strlit "k"); Const (1w:word64)]), s2)
     = (NONE, set_var (strlit "k") (ValWord (1w + kv)) s2)`
     by (irule eval_assign_addC >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `s3 = set_var (strlit "k") (ValWord (1w + kv)) s2` >>
  `evaluate (Seq (Assign Local (strlit "bp")
                    (Op Add [Var Local (strlit "bp"); Const (8w:word64)]))
                 (Assign Local (strlit "k")
                    (Op Add [Var Local (strlit "k"); Const (1w:word64)])), s1)
     = (NONE, s3)`
     by (irule Seq_NONE >> qexists_tac `s2` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE simp [Abbr `s2`, set_var_def])) >>
  `evaluate (fillBody, s) = (NONE, s3)`
     by (simp [fillBody_def] >> irule Seq_NONE >> qexists_tac `s1` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `s3` >>
  fs [Abbr `s3`, set_var_def, FLOOKUP_UPDATE]
QED
val _ = ck "fillBody_eval";

(* ONE iteration of the body: instantiate `fillBody_eval` at bpw = outB + 8k,
   kv = n2w k, then re-establish the invariant at k+1 (bump distinctness gives the
   layout preservation, via the isolated `wordsEncoded_extend`). *)
Theorem fillBody_step:
  fillInv N outB k s /\ k < N ==>
    ?s2. evaluate (fillBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         fillInv N outB (k + 1) s2
Proof
  strip_tac >>
  drule fillInv_scalars >> strip_tac >>
  `(outB + n2w (8 * k)) IN s.memaddrs`
     by (drule fillInv_arena >> disch_then (qspec_then `k` mp_tac) >> fs []) >>
  `8 * k < dimword (:64)` by (irule LESS_TRANS >> qexists_tac `8 * N` >> fs []) >>
  (* address / count normalisations — explicit REWRITE/metis (NOT a word-arith
     `simp`, which loops `word_add_n2w` <-> its GSYM / AC-normalises forever) *)
  `(8w + (outB + n2w (8 * k)) : word64) = outB + n2w (8 * (k + 1))`
     by (`8w + outB = outB + 8w : word64` by metis_tac [WORD_ADD_COMM] >>
         `8w + (outB + n2w (8 * k)) = outB + (8w + n2w (8 * k)) : word64`
            by (REWRITE_TAC [WORD_ADD_ASSOC] >> asm_rewrite_tac []) >>
         `8w + n2w (8 * k) = n2w (8 * (k + 1)) : word64`
            by (REWRITE_TAC [word_add_n2w] >> AP_TERM_TAC >> DECIDE_TAC) >>
         asm_rewrite_tac []) >>
  `(1w + n2w k : word64) = n2w (k + 1)`
     by (REWRITE_TAC [word_add_n2w] >> AP_TERM_TAC >> DECIDE_TAC) >>
  (* run the entire body in one shot over the (symbolic) start state *)
  drule_all fillBody_eval >> strip_tac >>
  qexists_tac `s'` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  (* the exit locals in normalised form — single-equation rewrites only (no
     asm_rewrite over the whole context, which drags the big `s'.memory` term) *)
  `FLOOKUP s'.locals (strlit "bp") = SOME (ValWord (outB + n2w (8 * (k + 1))))`
     by (qpat_x_assum `FLOOKUP s'.locals (strlit "bp") = _` mp_tac >>
         qpat_x_assum `8w + (outB + n2w (8 * k)) = _` (fn th => once_rewrite_tac [th]) >>
         disch_then ACCEPT_TAC) >>
  `FLOOKUP s'.locals (strlit "k") = SOME (ValWord (n2w (k + 1)))`
     by (qpat_x_assum `FLOOKUP s'.locals (strlit "k") = _` mp_tac >>
         qpat_x_assum `1w + n2w k = _` (fn th => once_rewrite_tac [th]) >>
         disch_then ACCEPT_TAC) >>
  `FLOOKUP s'.locals (strlit "n") = SOME (ValWord (n2w N))`
     by (qpat_x_assum `FLOOKUP s'.locals (strlit "n") = FLOOKUP s.locals (strlit "n")`
           (fn th => once_rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
  (* the layout relation at k+1, via the isolated lemma *)
  `wordsEncoded (GENLIST (\i. i) k) outB s`
     by (irule fillInv_words >> qexists_tac `N` >> first_assum ACCEPT_TAC) >>
  `s'.memory = ((outB + n2w (8 * k)) =+ Word (n2w k)) s.memory` by first_assum ACCEPT_TAC >>
  `wordsEncoded (GENLIST (\i. i) (k + 1)) outB s'`
     by (irule wordsEncoded_extend >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexists_tac `s` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* arena availability transfers (memaddrs unchanged) *)
  `s'.memaddrs = s.memaddrs` by first_assum ACCEPT_TAC >>
  `!j. j < N ==> (outB + n2w (8 * j)) IN s'.memaddrs`
     by (drule fillInv_arena >> strip_tac >>
         qpat_x_assum `s'.memaddrs = s.memaddrs` (fn th => rewrite_tac [th]) >>
         first_assum ACCEPT_TAC) >>
  `k + 1 <= N`
     by (qpat_x_assum `k < N` mp_tac >> rpt (pop_assum kall_tac) >> DECIDE_TAC) >>
  PURE_REWRITE_TAC [fillInv_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
val _ = ck "fillBody_step";

Theorem fillLoop_unfold:
  fillInv N outB k s /\ k < N /\ s.clock <> 0 ==>
  ?s2. evaluate (fillLoop, s) = evaluate (fillLoop, s2) /\
       s2.clock = s.clock - 1 /\ fillInv N outB (k + 1) s2
Proof
  strip_tac >>
  `eval s fillGuard = SOME (ValWord 1w)` by (drule eval_fillGuard >> fs []) >>
  `fillInv N outB k (dec_clock s)` by (simp [dec_clock_def] >> irule fillInv_clock >> fs []) >>
  `?s2. evaluate (fillBody, dec_clock s) = (NONE, s2) /\
        s2.clock = (dec_clock s).clock /\ fillInv N outB (k + 1) s2`
     by (irule fillBody_step >> fs []) >>
  qexists_tac `s2` >>
  `s2.clock <= (dec_clock s).clock` by fs [] >>
  `evaluate (fillLoop, s) = evaluate (fillLoop, s2)`
     by (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [fillLoop_def] THENC ONCE_REWRITE_CONV [evaluate_def])) >>
         simp [GSYM fillLoop_def, fix_clock_id] >> fs [fix_clock_id]) >>
  `s2.clock = s.clock - 1` by fs [dec_clock_def] >> fs []
QED
val _ = ck "fillLoop_unfold";

Theorem fillLoop_run:
  !m N outB k s.
    fillInv N outB k s /\ N - k <= m /\ N - k <= s.clock ==>
    ?s'. evaluate (fillLoop, s) = (NONE, s') /\ wordsEncoded (GENLIST (\i. i) N) outB s'
Proof
  Induct_on `m`
  >- (
    rpt strip_tac >>
    `k = N` by fs [fillInv_def] >>
    `eval s fillGuard = SOME (ValWord 0w)` by (drule eval_fillGuard >> fs []) >>
    qexists_tac `s` >>
    `evaluate (fillLoop, s) = (NONE, s)` by (simp [fillLoop_def, Once evaluate_def]) >>
    `wordsEncoded (GENLIST (\i. i) N) outB s` by fs [fillInv_def] >> fs []) >>
  rpt strip_tac >>
  Cases_on `k < N`
  >- (
    `s.clock <> 0` by fs [] >>
    drule_all fillLoop_unfold >> strip_tac >>
    last_x_assum (qspecl_then [`N`,`outB`,`k + 1`,`s2`] mp_tac) >>
    impl_tac >- fs [] >>
    strip_tac >> qexists_tac `s'` >> fs []) >>
  `k = N` by fs [fillInv_def] >>
  `eval s fillGuard = SOME (ValWord 0w)` by (drule eval_fillGuard >> fs []) >>
  qexists_tac `s` >>
  `evaluate (fillLoop, s) = (NONE, s)` by (simp [fillLoop_def, Once evaluate_def]) >>
  `wordsEncoded (GENLIST (\i. i) N) outB s` by fs [fillInv_def] >> fs []
QED
val _ = ck "fillLoop_run";

Theorem fillLoop_refines:
  FLOOKUP s.locals (strlit "k")  = SOME (ValWord 0w) /\
  FLOOKUP s.locals (strlit "n")  = SOME (ValWord (n2w N)) /\
  FLOOKUP s.locals (strlit "bp") = SOME (ValWord outB) /\
  N < 2n ** 63 /\ 8 * N < dimword (:64) /\
  (!j. j < N ==> (outB + n2w (8 * j)) IN s.memaddrs) /\
  N <= s.clock ==>
  ?s'. evaluate (fillLoop, s) = (NONE, s') /\
       wordsEncoded (GENLIST (\i. i) N) outB s'
Proof
  strip_tac >>
  `fillInv N outB 0 s`
     by (simp [fillInv_def, wordsEncoded_def] >> fs []) >>
  qspecl_then [`N`,`N`,`outB`,`0`,`s`] mp_tac fillLoop_run >>
  impl_tac >- fs [] >> strip_tac >>
  qexists_tac `s'` >> fs []
QED
val _ = ck "fillLoop_refines";

val _ = export_theory ();
