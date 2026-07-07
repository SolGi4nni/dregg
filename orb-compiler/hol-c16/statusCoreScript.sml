(* ===========================================================================
   C15 probe, PART A — the THIRD primitive's Link-A core, derived AUTOMATICALLY
   by the `panLinkA_branch` tactic (no bespoke per-primitive hand proof).

   `statusCore` is the VERBATIM `If` cascade lifted from `functions
   statusClassProg` (the parser's output on statusclass.pnk).  We prove, against
   real `panSem$evaluate`, that it writes EXACTLY the Lean spec's class digit
   `n2w (statusClass code)` into the local «result».

   Unlike C14's `stepCore` (which reused the c2 `machineStepLinkA` guard lemmas
   and hand-cased the three arms), the ENTIRE core equation here is discharged
   by ONE tactic invocation, `panLinkA_branch`, which:
     (i)  exposes the relation (FLOOKUP facts + range bounds),
     (ii) evaluates every `Cmp Less` guard via the GENERIC `panAuto$eval_lt_pinned`
          (no per-primitive guard lemmas), and
     (iii) case-splits the finite guard set + reduces every straight-line leaf.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open panAutoTheory;        (* signed_lt_n2w64, eval_lt_pinned, Annot_Seq_eval *)
open c14GenericTheory;     (* noFFI (generic, reused) *)
open panAutoLib;           (* panLinkA_branch — the reusable loop-free Link-A tactic *)

val _ = new_theory "statusCore";

(* --- the Lean SPEC, re-declared in HOL (byte-identical to C15.statusClass) --- *)
Definition statusClass_def:
  statusClass (code:num) =
    if code < 200 then 1n
    else if code < 300 then 2n
    else if code < 400 then 3n
    else if code < 500 then 4n
    else 5n
End

(* --- statusCore = the VERBATIM emitted If cascade (from `functions
   statusClassProg`), with the Const-assign leaves behind their location Annots. --- *)
Definition statusCore_def:
  statusCore =
    If (Cmp Less (Var Local «code») (Const (200w:word64)))
       (Seq (Annot «location» «(27:4 27:13)») (Assign Local «result» (Const 1w)))
       (Seq (Annot «location» «(29:7 38:19)»)
          (If (Cmp Less (Var Local «code») (Const (300w:word64)))
             (Seq (Annot «location» «(30:6 30:15)») (Assign Local «result» (Const 2w)))
             (Seq (Annot «location» «(32:9 38:19)»)
                (If (Cmp Less (Var Local «code») (Const (400w:word64)))
                   (Seq (Annot «location» «(33:8 33:17)») (Assign Local «result» (Const 3w)))
                   (Seq (Annot «location» «(35:11 38:19)»)
                      (If (Cmp Less (Var Local «code») (Const (500w:word64)))
                         (Seq (Annot «location» «(36:10 36:19)») (Assign Local «result» (Const 4w)))
                         (Seq (Annot «location» «(38:10 38:19)») (Assign Local «result» (Const 5w)))))))))
End

(* --- the core relation: code/result in locals, range for the (signed) guards. --- *)
Definition statusRel_def:
  statusRel (code:num) (r0:word64) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «code» = SOME (ValWord (n2w code)) /\
    FLOOKUP s.locals «result» = SOME (ValWord r0) /\
    code < 1000
End

(* ===========================================================================
   The headline core equation, derived AUTOMATICALLY by the REUSABLE tactic
   `panAutoLib.panLinkA_branch` (NOT an inline copy — the library version).  The
   ONLY per-primitive inputs are the three definitional theorems and the finite
   guard-predicate list; the tactic reads the relation to map each pinned
   num-var to its local, symbolically evaluates the Dec/Annot/Seq/If spine, and
   case-splits the finite guard set leaf-by-leaf against the spec.  No bespoke
   per-primitive hand proof.
   =========================================================================== *)
Theorem evaluate_statusCore:
  statusRel code r0 s ==>
  evaluate (statusCore, s) =
    (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)
Proof
  panLinkA_branch (statusRel_def, statusClass_def, statusCore_def)
    [“code < 200n”, “code < 300n”, “code < 400n”, “code < 500n”]
QED

(* --- framed: for the whole-main wrapper; NO clock precondition (branch-only) --- *)
Theorem evaluate_statusCore_framed:
  statusRel code r0 s ==>
  ?s'. evaluate (statusCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (statusClass code))) /\
       (!v. v <> «result» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >> drule evaluate_statusCore >> strip_tac >>
  qexists_tac `set_var «result» (ValWord (n2w (statusClass code))) s` >>
  simp [set_var_def, FLOOKUP_UPDATE] >> rw [] >> simp [FLOOKUP_UPDATE]
QED

(* statusCore performs no FFI: reusing the generic noFFI predicate. *)
Theorem statusCore_noFFI:
  noFFI statusCore
Proof
  REWRITE_TAC [statusCore_def] >> EVAL_TAC
QED

val _ = export_theory ();
