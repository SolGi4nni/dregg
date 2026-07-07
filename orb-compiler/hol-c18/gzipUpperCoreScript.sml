(* ===========================================================================
   C18 probe, FRAGMENT 3 — the DEPLOYED serve ASCII-uppercase test's Link-A core,
   derived AUTOMATICALLY by the C18 `panLinkA_branch_le` tactic — a NESTED cascade
   of TWO `<=` threshold guards, exercising BOTH operand orientations of the
   NotLess companion (variable-on-left from `65 <= b`, variable-on-right from
   `b <= 90`).

   THE FRAGMENT: the uppercase test at the heart of `Gzip.lowerByte` (drorb
   orb/Reactor/Stage/Gzip.lean):
     `lowerByte b = if 65 <= b && b <= 90 then b+32 else b`
   is the per-byte ASCII case-fold used by `Gzip.lower`, the header-name/value
   canonicalization the DEPLOYED serve runs in `Gzip.acceptsGzip` (gzipStage,
   position 10 of `Reactor.Deploy.deployStagesFull2`) and the deployed CORS
   canonical-origin path.  The loop-free DECISION core — whether byte `b` is an
   uppercase letter (whether to subtract 32) — is `65 <= b && b <= 90 -> 1 else 0`.
   Genuinely LOOP-FREE: two `<=` guards, no recursion, no `While`.

   Faithful lowering: the runtime input is the byte value `b`.  The Pancake parser
   lowers `65 <= b` to `Cmp NotLess (Var b) (Const 65w)` (variable-on-LEFT) and
   `b <= 90` to `Cmp NotLess (Const 90w) (Var b)` (variable-on-RIGHT).
   `gzipUpperCore` is the VERBATIM nested `If` from `functions gzipUpperProg` (the
   verified parser's output on gzipupper.pnk).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open panAutoTheory;        (* eval_ge_pinned, eval_ge_pinned_rhs, Annot_Seq_eval, ... *)
open c14GenericTheory;     (* noFFI (generic, reused) *)
open panAutoLib;           (* panLinkA_branch_le — reusable `<=` Link-A tactic (C18) *)

val _ = new_theory "gzipUpperCore";

(* --- the Lean SPEC, re-declared in the NESTED form the Lean `&&` short-circuits
   to (`65 <= b && b <= 90` = `if 65<=b then (if b<=90 then _ else _) else _`),
   byte-identical to the uppercase test in Gzip.lowerByte (uppercase = 1, not = 0).
   `gzipUpper_eq` records that this is exactly the conjunction predicate. --- *)
Definition gzipUpper_def:
  gzipUpper (b:num) = if 65 <= b then (if b <= 90 then 1n else 0n) else 0n
End

Theorem gzipUpper_eq:
  gzipUpper b = if 65 <= b /\ b <= 90 then 1n else 0n
Proof
  rw [gzipUpper_def] >> fs []
QED

(* --- gzipUpperCore = the VERBATIM emitted nested If (from `functions
   gzipUpperProg`), leaves behind their location Annots. --- *)
Definition gzipUpperCore_def:
  gzipUpperCore =
    If (Cmp NotLess (Var Local «b») (Const (65w:word64)))
       (Seq (Annot «location» «(28:7 31:15)»)
          (If (Cmp NotLess (Const 90w) (Var Local «b»))
             (Seq (Annot «location» «(29:6 29:15)») (Assign Local «result» (Const 1w)))
             (Seq (Annot «location» «(31:6 31:15)») (Assign Local «result» (Const 0w)))))
       (Seq (Annot «location» «(34:4 34:13)») (Assign Local «result» (Const 0w)))
End

(* --- the core relation: b/result in locals, byte range for the guards. --- *)
Definition gzipUpperRel_def:
  gzipUpperRel (b:num) (r0:word64) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «b» = SOME (ValWord (n2w b)) /\
    FLOOKUP s.locals «result» = SOME (ValWord r0) /\
    b < 4294967296
End

(* ===========================================================================
   The headline core equation, derived AUTOMATICALLY by the C18 REUSABLE tactic
   `panAutoLib.panLinkA_branch_le` — TWO `<=` guards, both operand orientations.
   The ONLY per-primitive inputs are the three definitional theorems and the
   finite `<=`-guard list.
   =========================================================================== *)
Theorem evaluate_gzipUpperCore:
  gzipUpperRel b r0 s ==>
  evaluate (gzipUpperCore, s) =
    (NONE, set_var «result» (ValWord (n2w (gzipUpper b))) s)
Proof
  panLinkA_branch_le (gzipUpperRel_def, gzipUpper_def, gzipUpperCore_def)
    [“65 <= b”, “b <= 90”]
QED

(* --- framed: for the whole-main wrapper; NO clock precondition (branch-only) --- *)
Theorem evaluate_gzipUpperCore_framed:
  gzipUpperRel b r0 s ==>
  ?s'. evaluate (gzipUpperCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (gzipUpper b))) /\
       (!v. v <> «result» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >> drule evaluate_gzipUpperCore >> strip_tac >>
  qexists_tac `set_var «result» (ValWord (n2w (gzipUpper b))) s` >>
  simp [set_var_def, FLOOKUP_UPDATE] >> rw [] >> simp [FLOOKUP_UPDATE]
QED

Theorem gzipUpperCore_noFFI:
  noFFI gzipUpperCore
Proof
  REWRITE_TAC [gzipUpperCore_def] >> EVAL_TAC
QED

val _ = export_theory ();
