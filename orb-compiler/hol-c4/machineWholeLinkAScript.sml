(* ===========================================================================
   C4 probe — WHOLE-PROGRAM composition (Link A for a small `main`).

   C3 (`machineLoopLinkAScript.sml`) proved Link A for the LOOP in isolation:
   `machineLoop_refines_run` — the emitted `While` computes the Lean fold
   `FOLDL mstep 0 input` into local «c», ASSUMING the loop precondition
   `loopInv .. 0 0` (accumulator 0, index 0, «len»/«base» set, `memRel`).

   C3 named the residual: the WHOLE-PROGRAM FRAME — establishing `loopInv .. 0 0`
   from `main`'s initialisation (`Dec`s that set c:=0, i:=0), running the loop,
   and `Store`-ing the result out. This file DISCHARGES that frame end-to-end
   against real `panSem$evaluate`:

     mainFrame =
       Dec «c» 0 (Dec «i» 0 (Dec «b» 0
         (Seq machineLoop
              (Store (base_addr + 24) c))))          (* write the result out *)

   We prove `evaluate (mainFrame, s)` runs the proven `machineLoop` and writes
   `n2w (FOLDL mstep 0 input)` — the Lean model's `C2.run` over the input — into
   memory at `base_addr + 24`, given that the input has been provisioned into
   memory + locals (the @load_vec FFI postcondition, packaged as `loadedRel` and
   ASSUMED — see the report for the FFI-oracle-linkage residual).

   The two FFI calls of the full `.pnk` main (`@load_vec` before, `@report_vec`
   after) are elided: `@load_vec`'s postcondition is exactly the `loadedRel`
   hypothesis, and `@report_vec` only READS the already-stored result word. So
   this theorem is `main` with the FFI boundary replaced by its spec — the
   Dec/init/loop/Store frame, composed with C3's loop, proven whole.

   The proof: (1) `Dec_zero`, a reusable lemma for `Dec v One (Const 0w) prog`;
   (2) establish `loopInv input bufAddr 0 0` at the post-`Dec` state (this is the
   precondition discharge C3 named); (3) compose `machineLoop_refines_run`
   verbatim; (4) evaluate the `Store` of the fold result (`base_addr` is preserved
   across the loop by `evaluate_invariants`; the store address is in `memaddrs`);
   (5) peel the three `Dec`s (each restores a local, leaves memory untouched).
   Reuses C3's `fix_clock_id` and the real `panSem` `evaluate_clock`/
   `evaluate_invariants`.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory combinTheory;
open panLangTheory panSemTheory panPropsTheory;
open machineStepLinkATheory;   (* C2: mstep, mRel, stepBody, ...            *)
open machineLoopLinkATheory;   (* C3: machineLoop, loopInv, memRel, ...     *)

val _ = new_theory "machineWholeLinkA";

(* ---------------------------------------------------------------------------
   The WHOLE-PROGRAM frame: the .pnk `main` with the two FFI calls replaced by
   their spec. `Store (base_addr + 24) c` = the .pnk `st base + 24, c;` that
   writes the final counter to the control-block result slot (read afterwards by
   @report_vec). The buffer base local the loop reads is «base» (the .pnk's
   `buf`); the result address uses `BaseAddr` (= @base) directly, which the loop
   preserves.
   --------------------------------------------------------------------------- *)
Definition mainFrame_def:
  mainFrame =
    Dec (strlit "c") One (Const (0w:word64))
      (Dec (strlit "i") One (Const (0w:word64))
        (Dec (strlit "b") One (Const (0w:word64))
          (Seq machineLoop
               (Store (Op Add [BaseAddr; Const (24w:word64)])
                      (Var Local (strlit "c"))))))
End

(* ---------------------------------------------------------------------------
   The @load_vec FFI postcondition, packaged: the input stream is in the buffer
   at `bufAddr` (`memRel`), `«len»` holds its length, `«base»` holds the buffer
   pointer, and the byte/signed-range side conditions hold. This is what the
   elided `@load_vec(...)` + `var len = lds 1 (base+16)` establish; here it is the
   ASSUMED boundary (the FFI-oracle-linkage residual named in the report).
   --------------------------------------------------------------------------- *)
Definition loadedRel_def:
  loadedRel (input:num list) (bufAddr:word64) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "len")  = SOME (ValWord (n2w (LENGTH input))) /\
    FLOOKUP s.locals (strlit "base") = SOME (ValWord bufAddr) /\
    memRel input bufAddr s /\
    LENGTH input < 2n ** 63 /\
    EVERY (\x. x < 256) input
End

(* ---------------------------------------------------------------------------
   A `Dec v One (Const 0w) prog` node: evaluate the body in the extended locals,
   then restore `v`. Reusable for the three initialisers. `res_var` restores the
   outer binding; memory/clock are threaded through unchanged.
   --------------------------------------------------------------------------- *)
Theorem Dec_zero:
  evaluate (prog, st with locals := st.locals |+ (v, ValWord (0w:word64)))
      = (res, st') ==>
  evaluate (Dec v One (Const (0w:word64)) prog, st) =
    (res, st' with locals := res_var st'.locals (v, FLOOKUP st.locals v))
Proof
  strip_tac >>
  simp [Once evaluate_def, eval_def, shape_of_def] >>
  pairarg_tac >> gvs []
QED

(* Sequencing two NONE-returning statements where the first spends (but never
   raises) the clock: the `Seq` `fix_clock` collapses to the identity. This is
   C3's `Seq_NONE` weakened from `sa.clock = s.clock` to `sa.clock <= s.clock`,
   which is what the loop (it consumes clock) needs. *)
Theorem Seq_NONE_le:
  evaluate (p1,s) = (NONE,sa) /\ sa.clock <= s.clock /\
  evaluate (p2,sa) = (NONE,sb) ==>
  evaluate (Seq p1 p2, s) = (NONE, sb)
Proof
  strip_tac >>
  `fix_clock s (evaluate (p1,s)) = (NONE,sa)`
     by (asm_simp_tac (srw_ss()) [] >> irule fix_clock_id >>
         asm_simp_tac (srw_ss()) []) >>
  simp [Once evaluate_def] >>
  asm_simp_tac (srw_ss()) []
QED

(* ---------------------------------------------------------------------------
   The `Store` of the result: with «c» holding the fold and the result address in
   `memaddrs`, the emitted `Store (base_addr+24) c` writes `Word (n2w fold)` at
   `base_addr + 24`, leaving everything else. `bs_addr = s.base_addr` is the base
   the store computes; the loop preserved it (`evaluate_invariants`).
   --------------------------------------------------------------------------- *)
Theorem evaluate_result_store:
  FLOOKUP s'.locals (strlit "c") = SOME (ValWord w) /\
  (s'.base_addr + 24w) IN s'.memaddrs ==>
  evaluate (Store (Op Add [BaseAddr; Const (24w:word64)]) (Var Local (strlit "c")), s')
    = (NONE, s' with memory := ((s'.base_addr + 24w) =+ Word w) s'.memory)
Proof
  strip_tac >>
  simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        WORD_ADD_0, flatten_def, mem_stores_def, mem_store_def]
QED

(* ---------------------------------------------------------------------------
   THE WHOLE-PROGRAM Link A. From a state where @load_vec has provisioned the
   input (`loadedRel`), with enough clock and a valid result slot, the emitted
   `mainFrame` runs to completion (NONE — no error, no TimeOut) and leaves the
   Lean model's whole-stream result `n2w (FOLDL mstep 0 input)` (= `C2.run`) in
   memory at `base_addr + 24`.

   This COMPOSES C3's `machineLoop_refines_run` verbatim, DISCHARGING its
   `loopInv .. 0 0` precondition from the `Dec` initialisation + `loadedRel` — the
   exact whole-program frame C3 named UNCLOSED.
   --------------------------------------------------------------------------- *)
Theorem mainFrame_refines_run:
  loadedRel input bufAddr s /\
  LENGTH input <= s.clock /\
  (s.base_addr + 24w) IN s.memaddrs ==>
  ?fs. evaluate (mainFrame, s) = (NONE, fs) /\
       fs.memory (s.base_addr + 24w)
         = Word (n2w (FOLDL mstep 0 input))
Proof
  strip_tac >>
  (* the string-key disequalities the FLOOKUP reductions need *)
  `strlit "c" <> strlit "i" /\ strlit "c" <> strlit "b" /\
   strlit "i" <> strlit "b" /\
   strlit "len" <> strlit "c" /\ strlit "len" <> strlit "i" /\
   strlit "len" <> strlit "b" /\ strlit "base" <> strlit "c" /\
   strlit "base" <> strlit "i" /\ strlit "base" <> strlit "b"` by EVAL_TAC >>
  (* the three post-Dec states (c:=0, then i:=0, then b:=0) *)
  qabbrev_tac `stc = s   with locals := s.locals   |+ (strlit "c", ValWord (0w:word64))` >>
  qabbrev_tac `sti = stc with locals := stc.locals |+ (strlit "i", ValWord (0w:word64))` >>
  qabbrev_tac `sB  = sti with locals := sti.locals |+ (strlit "b", ValWord (0w:word64))` >>
  (* memory / memaddrs / base_addr / clock of the post-Dec state = the initial *)
  `sB.memory = s.memory /\ sB.memaddrs = s.memaddrs /\ sB.be = s.be /\
   sB.base_addr = s.base_addr /\ sB.clock = s.clock`
     by simp [Abbr `sB`, Abbr `sti`, Abbr `stc`] >>
  `sB.locals = s.locals |+ (strlit "c", ValWord (0w:word64))
                        |+ (strlit "i", ValWord (0w:word64))
                        |+ (strlit "b", ValWord (0w:word64))`
     by simp [Abbr `sB`, Abbr `sti`, Abbr `stc`] >>
  (* STEP 1 — discharge the loop precondition loopInv .. 0 0 at sB *)
  `loopInv input bufAddr 0 0 sB`
     by (fs [loadedRel_def] >>
         simp [loopInv_def] >>
         asm_simp_tac (srw_ss()) [FLOOKUP_UPDATE] >>
         gvs [memRel_def]) >>
  (* STEP 2 — compose C3's proven loop verbatim *)
  `LENGTH input <= sB.clock` by fs [] >>
  drule_all machineLoop_refines_run >> strip_tac >>
  (* base_addr / memaddrs preserved across the loop (real panSem frame lemma) *)
  drule evaluate_invariants >> strip_tac >>
  `s'.base_addr = s.base_addr /\ s'.memaddrs = s.memaddrs` by fs [] >>
  (* STEP 3 — the result Store writes n2w(fold) at base_addr + 24 *)
  `(s'.base_addr + 24w) IN s'.memaddrs` by fs [] >>
  drule_all evaluate_result_store >> strip_tac >>
  qabbrev_tac `sStore = s' with memory :=
                 ((s'.base_addr + 24w) =+ Word (n2w (FOLDL mstep 0 input))) s'.memory` >>
  (* STEP 4 — assemble the Seq (loop; store) via Seq_NONE_le. *)
  `s'.clock <= sB.clock` by (imp_res_tac evaluate_clock >> fs []) >>
  `evaluate (Seq machineLoop
       (Store (Op Add [BaseAddr; Const (24w:word64)]) (Var Local (strlit "c"))), sB)
     = (NONE, sStore)`
     by (irule Seq_NONE_le >> qexists_tac `s'` >>
         asm_simp_tac (srw_ss()) []) >>
  (* STEP 5 — peel the three Decs (each restores its local; memory untouched).
     Each state abbreviation is already in `Dec_zero`'s antecedent shape, so
     unfolding it and MATCH_MP'ing Dec_zero threads the frame out. *)
  qunabbrev_tac `sB` >>
  qpat_x_assum `evaluate (Seq _ _, _) = _`
     (assume_tac o MATCH_MP Dec_zero) >>
  qunabbrev_tac `sti` >>
  qpat_x_assum `evaluate (Dec (strlit "b") _ _ _, _) = _`
     (assume_tac o MATCH_MP Dec_zero) >>
  qunabbrev_tac `stc` >>
  qpat_x_assum `evaluate (Dec (strlit "i") _ _ _, _) = _`
     (assume_tac o MATCH_MP Dec_zero) >>
  (* fold the assembled `Dec «c» ...` back to `mainFrame`, supply it as the
     witness, then reduce the result memory: every Dec wrap is `_ with locals :=
     _`, so the memory is sStore's, and the `Store` update reads back n2w(fold). *)
  qpat_x_assum `evaluate (_, s) = (NONE, _)`
     (assume_tac o REWRITE_RULE [GSYM mainFrame_def]) >>
  first_assum (irule_at Any) >>
  simp [Abbr `sStore`, APPLY_UPDATE_THM] >> fs []
QED

val _ = export_theory ();
