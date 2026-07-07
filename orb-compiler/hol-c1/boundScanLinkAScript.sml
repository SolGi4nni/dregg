(* ===========================================================================
   C1 probe — LINK A, paid down for the bounds sub-primitive.

   C0 (C0-REPORT.md) dual-emitted the region bounds-check + byte-scan and
   *priced* the front-end preservation obligation (Link A: Lean/HOL4 SPEC
   <=> panLang source semantics) without discharging it. This file discharges
   Link A for the BOUNDS-CHECK sub-primitive against the REAL Pancake source
   semantics `panSem$evaluate` / `panSem$eval` (not the C0 behavioral twin):

     evaluate( <the .pnk bounds `If`>, s )  refines  boundScan / c0_encode.

   The scan `While` loop + its `LoadByte` memory relation (the digest) are NOT
   proven here — that is the itemized remaining cost (see C1-REPORT.md).

   Faithfulness note on the comparison: in Pancake the token `<` is `LessT`,
   which `panPtreeConversion` maps to `Cmp Less` — the SIGNED word comparison
   (`asm$word_cmp Less w1 w2 = (w1 < w2)`, HOL `word_lt`). `<+` would be the
   unsigned `Lower`. So the emitted bounds test is signed, and its correctness
   carries a signed-range side condition (lengths/offsets < 2^63 on the 64-bit
   target). That side condition is made explicit below — it is exactly the
   P2 §4.2 convention seam, and here it BITES: an honest Link A for this
   program must carry "the arena/view sizes fit the non-negative signed range".
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib;
open panLangTheory panSemTheory;

val _ = new_theory "boundScanLinkA";

(* ---------------------------------------------------------------------------
   The Lean SPEC, re-declared in HOL (byte-identical to C0's boundScanScript).
   `boundScan` = the region/view read: SOME digest iff in-bounds, else NONE.
   `c0_encode` = the single-word result encoding (NONE |-> 0xFFFFFFFF).
   --------------------------------------------------------------------------- *)
Definition step_def:
  step acc b = (acc * 31 + b) MOD 16777216
End

Definition scanFrom_def:
  (scanFrom a off 0 acc = acc) /\
  (scanFrom a off (SUC n) acc = scanFrom a (off + 1) n (step acc (EL off a)))
End

Definition boundScan_def:
  boundScan a off len =
    if off + len <= LENGTH a then SOME (scanFrom a off len 0) else NONE
End

Definition c0_encode_def:
  (c0_encode NONE = 4294967295n) /\
  (c0_encode (SOME (k:num)) = k)
End

(* ---------------------------------------------------------------------------
   The IMPLEMENTATION fragment: the .pnk bounds `If`, as a real panLang AST.

     if alen < (off + len) { result = 4294967295; } else { <scan loop> }

   with the scan loop's slot filled by `Skip` (the loop is out of scope for
   this fragment). `Cmp Less` = the SIGNED test the Pancake `<` compiles to.
   The `(4294967295w:word64)` literal fixes the word width to the x64 target.
   --------------------------------------------------------------------------- *)
Definition boundsChk_def:
  boundsChk =
    If (Cmp Less (Var Local (strlit "alen"))
                 (Op Add [Var Local (strlit "off"); Var Local (strlit "len")]))
       (Assign Local (strlit "result") (Const (4294967295w:word64)))
       Skip
End

(* ---------------------------------------------------------------------------
   The state relation: the local environment encodes (a, off, len) as words,
   `result` is a declared word slot, and the sizes fit the signed range.
   --------------------------------------------------------------------------- *)
Definition stRel_def:
  stRel (a:num list) off len r0 (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "alen")   = SOME (ValWord (n2w (LENGTH a))) /\
    FLOOKUP s.locals (strlit "off")    = SOME (ValWord (n2w off)) /\
    FLOOKUP s.locals (strlit "len")    = SOME (ValWord (n2w len)) /\
    FLOOKUP s.locals (strlit "result") = SOME (ValWord r0) /\
    LENGTH a < 2n ** 63 /\ off + len < 2n ** 63
End

(* ---------------------------------------------------------------------------
   The convention lemma (P2 §4.2 witness content): on the non-negative signed
   range, the SIGNED word order agrees with the nat order. This is where an
   off-by-a-sign-bit bug would live.
   --------------------------------------------------------------------------- *)
Theorem signed_lt_n2w64:
  !x y. x < 2n ** 63 /\ y < 2n ** 63 ==>
        (((n2w x):word64) < n2w y <=> x < y)
Proof
  rw [] >>
  `(2:num) ** 63 < 2 ** 64` by EVAL_TAC >>
  `x < dimword(:64) /\ y < dimword(:64)` by
    (`dimword(:64) = 2 ** 64` by EVAL_TAC >> fs [] >>
     conj_tac >> metis_tac [LESS_TRANS]) >>
  `~word_msb ((n2w x):word64) /\ ~word_msb ((n2w y):word64)` by
    (rw [word_msb_n2w] >> irule NOT_BIT_GT_TWOEXP >> fs []) >>
  rw [WORD_LT, w2n_n2w] >> fs []
QED

(* ---------------------------------------------------------------------------
   LINK A (bounds sub-primitive), the refinement core.
   `panSem$eval` of the bounds expression = 1w EXACTLY when the Lean SPEC says
   out-of-bounds (boundScan = NONE), else 0w. A kernel-checked equation between
   the real Pancake source semantics and the Lean model's bounds decision.
   --------------------------------------------------------------------------- *)
Theorem eval_bounds_expr:
  stRel a off len r0 s ==>
  eval s (Cmp Less (Var Local (strlit "alen"))
                   (Op Add [Var Local (strlit "off"); Var Local (strlit "len")]))
    = SOME (ValWord (if boundScan a off len = NONE then 1w else 0w))
Proof
  strip_tac >>
  qpat_x_assum `stRel _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE std_ss [stRel_def]) >>
  `(n2w (LENGTH a):word64 < n2w (len + off)) = (boundScan a off len = NONE)`
     by (`n2w (LENGTH a):word64 < n2w (len + off) <=> LENGTH a < len + off`
             by (irule signed_lt_n2w64 >> fs []) >>
         rw [boundScan_def] >> fs [NOT_LESS_EQUAL] >> metis_tac [ADD_COMM]) >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, word_add_n2w,
        asmTheory.word_cmp_def] >>
  fs []
QED

(* ---------------------------------------------------------------------------
   LINK A end-to-end for the fragment: running the REAL `panSem$evaluate` on
   the bounds `If` writes the sentinel `c0_encode NONE` into `result` exactly
   on the out-of-bounds inputs, and leaves the state untouched otherwise.
   The `n2w (c0_encode (boundScan a off len))` on the RHS is the Lean SPEC's
   own encoded result word — this is a Lean-model-step -> panLang-semantics
   equation, kernel-checked.
   --------------------------------------------------------------------------- *)
Theorem evaluate_boundsChk:
  stRel a off len r0 s ==>
  evaluate (boundsChk, s) =
    (NONE,
     if boundScan a off len = NONE
     then set_var (strlit "result")
                  (ValWord (n2w (c0_encode (boundScan a off len)))) s
     else s)
Proof
  rw [] >>
  drule eval_bounds_expr >> strip_tac >>
  simp [boundsChk_def, evaluate_def] >>
  Cases_on `boundScan a off len = NONE` >> fs [] >>
  fs [eval_def, is_valid_value_def, lookup_kvar_def, shape_of_def,
      stRel_def, set_kvar_def, c0_encode_def] >>
  `(4294967295w:word64) = n2w 4294967295` by EVAL_TAC >> fs []
QED

(* A named corollary in the report's own vocabulary: encode-form, both arms. *)
Theorem boundsChk_encodes_spec:
  stRel a off len r0 s ==>
  ?s'. evaluate (boundsChk, s) = (NONE, s') /\
       (boundScan a off len = NONE ==>
          FLOOKUP s'.locals (strlit "result")
            = SOME (ValWord (n2w (c0_encode (boundScan a off len))))) /\
       (boundScan a off len <> NONE ==> s' = s)
Proof
  rw [] >> drule evaluate_boundsChk >> rw [] >>
  fs [set_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

val _ = export_theory ();
