(* ===========================================================================
   C9 probe — LINK A for the FIRST RECLAIMING allocator: a fixed-size-block
   LIFO FREELIST emitted to Pancake, with a proven ALLOCATOR INVARIANT (the free
   blocks and the allocated blocks PARTITION the managed region — disjoint, no
   overlap, every block accounted for — and the free list is a valid acyclic
   chain in memory), proven against real panSem$evaluate that BOTH `alloc` and
   `free` PRESERVE the invariant, and that a FREE-THEN-ALLOC HANDS BACK the freed
   block (memory REUSE — the first reclaim step).

   C7 proved bump allocation (writeSpans fixed, fillLoop general-N; pointer only
   advances).  C8 proved the variable-length collector (collectSp; still bump, no
   reuse).  Both named the residual verbatim: "No free / reclaim.  The bump
   pointer only advances.  A verified allocator with free, a freelist, coalescing,
   or fragmentation reasoning is NOT modelled and IS still open research."
   C9 takes the SMALLEST HONEST bite of exactly that.

   THE MODEL.  A managed region is a fixed list `blocks` of fixed-size block
   addresses.  A free block stores, in its FIRST WORD, the address of the next
   free block (0w = NULL sentinel = end of list).  The free list is a singly-
   linked chain from a head pointer «head».
     alloc() = pop the head:  ap := head ; head := *head     (return ap)
     free(p) = push p:        *p := head ; head := p

   THE INVARIANT (`allocInv blocks freeL allocL s`):
     * PERM (freeL ++ allocL) blocks  — THE PARTITION.  The free and allocated
       blocks together are a permutation of the managed region: every block in
       exactly one cell (DISJOINT, and they TILE blocks).  With ALL_DISTINCT
       blocks this forces ALL_DISTINCT (freeL ++ allocL): none is both free and
       allocated, none double-counted.
     * linked s.memory freeL  — the free list is a VALID chain in memory (each
       free block's first word points to the next, last to 0w); ALL_DISTINCT
       freeL (from the partition) forbids cycles.
     * «head» = chainHead freeL — the head pointer tracks the list head.
     * every managed block is available (in s.memaddrs).

   Reuses verbatim: `eval_storeVar` (C7 — the word Store), `Seq_NONE` (C3).  What
   is NEW is memory REUSE: a freed address is handed back out, with the partition
   invariant proven preserved across pop AND push, and free-then-alloc returning
   the SAME physical block.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory bitTheory wordsTheory wordsLib
     finite_mapTheory combinTheory sortingTheory;
open panLangTheory panSemTheory;
open machineStepLinkATheory;
open machineLoopLinkATheory;      (* Seq_NONE                                    *)
open arenaAllocLinkATheory;       (* eval_storeVar                               *)

val _ = new_theory "arenaFreelistLinkA";

fun ck s = (print ("\nCKPT_DONE: " ^ s ^ "\n"); TextIO.flushOut TextIO.stdOut);

(* ---------------------------------------------------------------------------
   THE FREELIST REPRESENTATION.
   --------------------------------------------------------------------------- *)
Definition chainHead_def:
  (chainHead [] = (0w:word64)) /\
  (chainHead (a::rest) = a)
End

Definition linked_def:
  (linked m ([]:word64 list) <=> T) /\
  (linked m ((a:word64)::rest) <=>
     a <> 0w /\ m a = Word (chainHead rest) /\ linked m rest)
End

(* A store DISJOINT from every chain block leaves the chain intact — this makes
   `free` (which writes ONLY the freed block's first word) preserve the OTHER
   free blocks' links.  Induction on the chain. *)
Theorem linked_store_disjoint:
  !addrs m p v. linked m addrs /\ ~MEM p addrs ==>
                linked ((p =+ Word v) m) addrs
Proof
  Induct >> rw [linked_def] >> fs [APPLY_UPDATE_THM]
QED
val _ = ck "linked_store_disjoint";

(* ---------------------------------------------------------------------------
   THE ALLOCATOR INVARIANT — the PARTITION reclaim invariant.
   --------------------------------------------------------------------------- *)
Definition allocInv_def:
  allocInv (blocks:word64 list) (freeL:word64 list) (allocL:word64 list)
           (s:(64,'ffi) panSem$state) <=>
    ALL_DISTINCT blocks /\
    ~MEM (0w:word64) blocks /\
    PERM (freeL ++ allocL) blocks /\
    linked s.memory freeL /\
    FLOOKUP s.locals (strlit "head") = SOME (ValWord (chainHead freeL)) /\
    (!x. MEM x blocks ==> x IN s.memaddrs)
End

(* Partition consequence: free and alloc are pairwise disjoint / internally
   distinct — no block is both free and allocated. *)
Theorem allocInv_distinct:
  allocInv blocks freeL allocL s ==> ALL_DISTINCT (freeL ++ allocL)
Proof
  rw [allocInv_def] >> metis_tac [ALL_DISTINCT_PERM]
QED
val _ = ck "allocInv_distinct";

(* Moving a block between the two partition cells. *)
Theorem PERM_pop:
  !rest a xs. PERM ((a::rest) ++ xs) (rest ++ (a::xs))
Proof
  Induct
  >- simp [PERM_REFL] >>
  rpt strip_tac >> simp [] >>
  `PERM (a::h::(rest ++ xs)) (h::a::(rest ++ xs))` by simp [PERM_SWAP_AT_FRONT] >>
  `PERM (a::(rest ++ xs)) (rest ++ (a::xs))`
     by (`PERM ((a::rest) ++ xs) (rest ++ (a::xs))` by metis_tac [] >> fs []) >>
  `PERM (h::a::(rest ++ xs)) (h::(rest ++ (a::xs)))` by metis_tac [PERM_MONO] >>
  metis_tac [PERM_TRANS]
QED
val _ = ck "PERM_pop";

(* ---------------------------------------------------------------------------
   THE EMITTED OPERATIONS (real panLang AST — transcription of freelist.pnk).
   --------------------------------------------------------------------------- *)
Definition allocProg_def:
  allocProg =
    Seq (Assign Local (strlit "ap") (Var Local (strlit "head")))
        (Assign Local (strlit "head")
           (Load One (Var Local (strlit "head"))))
End

Definition freeProg_def:
  freeProg =
    Seq (Store (Var Local (strlit "fp")) (Var Local (strlit "head")))
        (Assign Local (strlit "head") (Var Local (strlit "fp")))
End

Definition freeThenAlloc_def:
  freeThenAlloc = Seq freeProg allocProg
End

(* Word LOAD of the next-free pointer: `*p` reads Word w when memory holds it. *)
Theorem eval_loadWord:
  FLOOKUP s.locals vp = SOME (ValWord a) /\ a IN s.memaddrs /\
  s.memory a = Word w ==>
  eval s (Load One (Var Local vp)) = SOME (ValWord w)
Proof
  rw [eval_def, panLangTheory.is_wf_shape_def, mem_load_def]
QED
val _ = ck "eval_loadWord";

Theorem eval_assignVar:
  FLOOKUP s.locals vp = SOME (ValWord oldp) /\
  FLOOKUP s.locals vq = SOME (ValWord w) ==>
  evaluate (Assign Local vp (Var Local vq), s) = (NONE, set_var vp (ValWord w) s)
Proof
  rw [evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def, shape_of_def,
      set_kvar_def, set_var_def]
QED
val _ = ck "eval_assignVar";

Theorem eval_assignLoad:
  FLOOKUP s.locals vp = SOME (ValWord oldp) /\
  FLOOKUP s.locals vq = SOME (ValWord a) /\ a IN s.memaddrs /\
  s.memory a = Word w ==>
  evaluate (Assign Local vp (Load One (Var Local vq)), s)
    = (NONE, set_var vp (ValWord w) s)
Proof
  strip_tac >>
  `eval s (Load One (Var Local vq)) = SOME (ValWord w)`
     by (irule eval_loadWord >> fs []) >>
  rw [evaluate_def, is_valid_value_def, lookup_kvar_def, shape_of_def,
      set_kvar_def, set_var_def]
QED
val _ = ck "eval_assignLoad";

(* ---------------------------------------------------------------------------
   LINK A #1 — `alloc` POPS a free block and PRESERVES the invariant.
   --------------------------------------------------------------------------- *)
Theorem alloc_preserves_inv:
  allocInv blocks (a::rest) allocL s /\
  (?apv. FLOOKUP s.locals (strlit "ap") = SOME (ValWord apv)) ==>
  ?s'. evaluate (allocProg, s) = (NONE, s') /\ s'.clock = s.clock /\
       FLOOKUP s'.locals (strlit "ap")   = SOME (ValWord a) /\
       FLOOKUP s'.locals (strlit "head") = SOME (ValWord (chainHead rest)) /\
       allocInv blocks rest (a::allocL) s'
Proof
  strip_tac >>
  `ALL_DISTINCT blocks /\ ~MEM (0w:word64) blocks /\
   PERM ((a::rest) ++ allocL) blocks /\ linked s.memory (a::rest) /\
   FLOOKUP s.locals (strlit "head") = SOME (ValWord (chainHead (a::rest))) /\
   (!x. MEM x blocks ==> x IN s.memaddrs)` by fs [allocInv_def] >>
  `FLOOKUP s.locals (strlit "head") = SOME (ValWord a)` by fs [chainHead_def] >>
  `a <> 0w /\ s.memory a = Word (chainHead rest) /\ linked s.memory rest`
     by fs [linked_def] >>
  `MEM a blocks`
     by (`MEM a ((a::rest) ++ allocL)` by simp [] >> metis_tac [PERM_MEM_EQ]) >>
  `a IN s.memaddrs` by fs [] >>
  `strlit "ap" <> strlit "head" /\ strlit "head" <> strlit "ap"` by EVAL_TAC >>
  (* step 1: ap := head  (= a) *)
  qabbrev_tac `sA = set_var (strlit "ap") (ValWord a) s` >>
  `evaluate (Assign Local (strlit "ap") (Var Local (strlit "head")), s) = (NONE, sA)`
     by (simp [Abbr `sA`] >> irule eval_assignVar >> fs []) >>
  `sA.memory = s.memory /\ sA.memaddrs = s.memaddrs /\ sA.clock = s.clock /\
   FLOOKUP sA.locals (strlit "head") = SOME (ValWord a) /\
   FLOOKUP sA.locals (strlit "ap") = SOME (ValWord a)`
     by simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  `a IN sA.memaddrs /\ sA.memory a = Word (chainHead rest)` by fs [] >>
  (* step 2: head := *head  (= chainHead rest) *)
  qabbrev_tac `s' = set_var (strlit "head") (ValWord (chainHead rest)) sA` >>
  `evaluate (Assign Local (strlit "head") (Load One (Var Local (strlit "head"))), sA)
     = (NONE, s')`
     by (simp [Abbr `s'`] >> irule eval_assignLoad >> fs []) >>
  `evaluate (allocProg, s) = (NONE, s')`
     by (simp [allocProg_def] >> irule Seq_NONE >> qexists_tac `sA` >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         simp [Abbr `sA`, set_var_def]) >>
  qexists_tac `s'` >>
  `s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\ s'.clock = s.clock`
     by simp [Abbr `s'`, Abbr `sA`, set_var_def] >>
  `FLOOKUP s'.locals (strlit "ap") = SOME (ValWord a) /\
   FLOOKUP s'.locals (strlit "head") = SOME (ValWord (chainHead rest))`
     by simp [Abbr `s'`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  (* pre-prove every allocInv conjunct as an assumption *)
  `PERM (rest ++ (a::allocL)) blocks`
     by (`PERM ((a::rest) ++ allocL) (rest ++ (a::allocL))` by simp [PERM_pop] >>
         metis_tac [PERM_TRANS, PERM_SYM]) >>
  `linked s'.memory rest` by (`s'.memory = s.memory` by fs [] >> fs []) >>
  `FLOOKUP s'.locals (strlit "head") = SOME (ValWord (chainHead rest))`
     by first_assum ACCEPT_TAC >>
  `!x. MEM x blocks ==> x IN s'.memaddrs`
     by (rw [] >> `x IN s.memaddrs` by fs [] >> fs []) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  PURE_REWRITE_TAC [allocInv_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
val _ = ck "alloc_preserves_inv";

(* ---------------------------------------------------------------------------
   LINK A #2 — `free` PUSHES a block and PRESERVES the invariant.
   --------------------------------------------------------------------------- *)
Theorem free_preserves_inv:
  allocInv blocks freeL allocL s /\
  FLOOKUP s.locals (strlit "fp") = SOME (ValWord p) /\
  PERM allocL (p :: allocL') ==>
  ?s'. evaluate (freeProg, s) = (NONE, s') /\ s'.clock = s.clock /\
       FLOOKUP s'.locals (strlit "head") = SOME (ValWord p) /\
       (!k. k <> strlit "head" ==> FLOOKUP s'.locals k = FLOOKUP s.locals k) /\
       allocInv blocks (p :: freeL) allocL' s'
Proof
  strip_tac >>
  `ALL_DISTINCT blocks /\ ~MEM (0w:word64) blocks /\
   PERM (freeL ++ allocL) blocks /\ linked s.memory freeL /\
   FLOOKUP s.locals (strlit "head") = SOME (ValWord (chainHead freeL)) /\
   (!x. MEM x blocks ==> x IN s.memaddrs)` by fs [allocInv_def] >>
  `ALL_DISTINCT (freeL ++ allocL)` by metis_tac [allocInv_distinct] >>
  `MEM p allocL` by (`MEM p (p::allocL')` by simp [] >> metis_tac [PERM_MEM_EQ]) >>
  `~MEM p freeL` by (fs [ALL_DISTINCT_APPEND] >> metis_tac []) >>
  `MEM p blocks`
     by (`MEM p (freeL ++ allocL)` by simp [] >> metis_tac [PERM_MEM_EQ]) >>
  `p <> 0w` by (strip_tac >> fs []) >>
  `p IN s.memaddrs` by fs [] >>
  `strlit "fp" <> strlit "head" /\ strlit "head" <> strlit "fp"` by EVAL_TAC >>
  (* step 1: *fp := head  (write p's first word = chainHead freeL) *)
  qabbrev_tac `sS = s with memory := (p =+ Word (chainHead freeL)) s.memory` >>
  `evaluate (Store (Var Local (strlit "fp")) (Var Local (strlit "head")), s)
     = (NONE, sS)`
     by (simp [Abbr `sS`] >> irule eval_storeVar >> fs []) >>
  `sS.memaddrs = s.memaddrs /\ sS.clock = s.clock /\ sS.locals = s.locals /\
   sS.memory = (p =+ Word (chainHead freeL)) s.memory`
     by simp [Abbr `sS`] >>
  `FLOOKUP sS.locals (strlit "fp") = SOME (ValWord p) /\
   FLOOKUP sS.locals (strlit "head") = SOME (ValWord (chainHead freeL))`
     by fs [] >>
  (* step 2: head := fp  (= p) *)
  qabbrev_tac `s' = set_var (strlit "head") (ValWord p) sS` >>
  `evaluate (Assign Local (strlit "head") (Var Local (strlit "fp")), sS)
     = (NONE, s')`
     by (simp [Abbr `s'`] >> irule eval_assignVar >> fs []) >>
  `evaluate (freeProg, s) = (NONE, s')`
     by (simp [freeProg_def] >> irule Seq_NONE >> qexists_tac `sS` >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp [Abbr `sS`]) >>
  qexists_tac `s'` >>
  `s'.memory = (p =+ Word (chainHead freeL)) s.memory /\
   s'.memaddrs = s.memaddrs /\ s'.clock = s.clock`
     by simp [Abbr `s'`, Abbr `sS`, set_var_def] >>
  `FLOOKUP s'.locals (strlit "head") = SOME (ValWord p)`
     by simp [Abbr `s'`, set_var_def, FLOOKUP_UPDATE] >>
  (* locals frame: only «head» changed *)
  `!k. k <> strlit "head" ==> FLOOKUP s'.locals k = FLOOKUP s.locals k`
     by (rw [] >> simp [Abbr `s'`, Abbr `sS`, set_var_def, FLOOKUP_UPDATE]) >>
  (* pre-prove every allocInv conjunct *)
  `PERM ((p::freeL) ++ allocL') blocks`
     by (`PERM (freeL ++ allocL) (freeL ++ (p::allocL'))`
            by (irule PERM_CONG >> simp [PERM_REFL]) >>
         `PERM ((p::freeL) ++ allocL') (freeL ++ (p::allocL'))` by simp [PERM_pop] >>
         metis_tac [PERM_TRANS, PERM_SYM]) >>
  `s'.memory p = Word (chainHead freeL)` by fs [APPLY_UPDATE_THM] >>
  `linked ((p =+ Word (chainHead freeL)) s.memory) freeL`
     by (irule linked_store_disjoint >> fs []) >>
  `linked s'.memory freeL`
     by (`s'.memory = (p =+ Word (chainHead freeL)) s.memory` by fs [] >> fs []) >>
  `linked s'.memory (p::freeL)` by (fs [linked_def]) >>
  `FLOOKUP s'.locals (strlit "head") = SOME (ValWord (chainHead (p::freeL)))`
     by (`chainHead (p::freeL) = p` by simp [chainHead_def] >> fs []) >>
  `!x. MEM x blocks ==> x IN s'.memaddrs`
     by (rw [] >> `x IN s.memaddrs` by fs [] >> fs []) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  PURE_REWRITE_TAC [allocInv_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
val _ = ck "free_preserves_inv";

(* ---------------------------------------------------------------------------
   THE RECLAIM HEADLINE — FREE-THEN-ALLOC HANDS BACK the freed block.
   Free an allocated block p, then alloc: the emitted `freeThenAlloc` returns the
   SAME physical address p in «ap» (memory REUSED — a freed address handed back
   out), restores «head» to the pre-free head (chainHead freeL), and re-establishes
   the invariant with p allocated again.  This is the first reclaim step C7/C8
   named as open: a freed address becomes usable again, under the partition invariant.
   --------------------------------------------------------------------------- *)
Theorem freeThenAlloc_reuses:
  allocInv blocks freeL allocL s /\
  FLOOKUP s.locals (strlit "fp") = SOME (ValWord p) /\
  (?apv. FLOOKUP s.locals (strlit "ap") = SOME (ValWord apv)) /\
  PERM allocL (p :: allocL') ==>
  ?s'. evaluate (freeThenAlloc, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "ap")   = SOME (ValWord p) /\
       FLOOKUP s'.locals (strlit "head") = SOME (ValWord (chainHead freeL)) /\
       allocInv blocks freeL (p :: allocL') s'
Proof
  strip_tac >>
  (* free(p): p pushed, invariant now allocInv blocks (p::freeL) allocL' *)
  `?s1. evaluate (freeProg, s) = (NONE, s1) /\ s1.clock = s.clock /\
        FLOOKUP s1.locals (strlit "head") = SOME (ValWord p) /\
        (!k. k <> strlit "head" ==> FLOOKUP s1.locals k = FLOOKUP s.locals k) /\
        allocInv blocks (p::freeL) allocL' s1`
     by (irule free_preserves_inv >> fs [] >> metis_tac []) >>
  `strlit "ap" <> strlit "head"` by EVAL_TAC >>
  `?apv2. FLOOKUP s1.locals (strlit "ap") = SOME (ValWord apv2)`
     by (`FLOOKUP s1.locals (strlit "ap") = FLOOKUP s.locals (strlit "ap")` by fs [] >>
         fs []) >>
  (* alloc(): pops the head (= p, the just-freed block) — THE REUSE *)
  `?s2. evaluate (allocProg, s1) = (NONE, s2) /\ s2.clock = s1.clock /\
        FLOOKUP s2.locals (strlit "ap") = SOME (ValWord p) /\
        FLOOKUP s2.locals (strlit "head") = SOME (ValWord (chainHead freeL)) /\
        allocInv blocks freeL (p::allocL') s2`
     by (irule alloc_preserves_inv >> fs [] >> metis_tac []) >>
  qexists_tac `s2` >>
  conj_tac
  >- (simp [freeThenAlloc_def] >> irule Seq_NONE >> qexists_tac `s1` >> fs []) >>
  fs []
QED
val _ = ck "freeThenAlloc_reuses";

val _ = export_theory ();
