(* ===========================================================================
   C18 probe, FRAGMENT 2 — the DEPLOYED serve rate-limit admit decision's Link-A
   core, derived AUTOMATICALLY by the NEW `panLinkA_branch_le` tactic.  This is
   the fragment that needs a GUARD KIND real serve code uses but neither C15's
   ordered-`<` nor C17's `=`-dispatch machinery covers: the `<=` (NotLess)
   THRESHOLD guard.  The whole delta is the ~2 `eval_ge_pinned` companions in
   panAutoScript + the `panLinkA_branch_le` tactic in panAutoLib, added ONCE.

   THE FRAGMENT: `Rate.tryAdmit` from the drorb serve
   (orb/Rate/Bucket.lean) — the token-bucket admit decision
   `if 1 <= b.tokens then (admit,true) else (reject,false)`.  It is consulted by
   `Reactor.Stage.Rate.admits` -> `rateStage`/`rateHighStage`, position 3 of
   `Reactor.Deploy.deployStagesFull2`.  Genuinely LOOP-FREE: a single `<=` on the
   available token count, no recursion, no `While`.

   Faithful lowering: the runtime input is the available token count `tokens`
   (post-`refill`); the decision bit is `1 <= tks -> admit(1) else reject(0)`.
   The Pancake parser lowers `1 <= tks` to `Cmp NotLess (Var tokens) (Const 1w)`
   (asm word_cmp NotLess = ~(<)) — the NEW guard kind.  `rateAdmitCore` is the
   VERBATIM `If` node lifted from `functions rateAdmitProg` (the verified parser's
   output on rateadmit.pnk).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open panAutoTheory;        (* eval_ge_pinned, Annot_Seq_eval, ... *)
open c14GenericTheory;     (* noFFI (generic, reused) *)
open panAutoLib;           (* panLinkA_branch_le — reusable `<=` Link-A tactic (C18) *)

val _ = new_theory "rateAdmitCore";

(* --- the Lean SPEC, re-declared: byte-identical to the Rate.tryAdmit admit bit
   (admit = 1, reject = 0). --- *)
Definition rateAdmit_def:
  rateAdmit (tks:num) = if 1 <= tks then 1n else 0n
End

(* --- rateAdmitCore = the VERBATIM emitted If node (from `functions
   rateAdmitProg`), leaves behind their location Annots. --- *)
Definition rateAdmitCore_def:
  rateAdmitCore =
    If (Cmp NotLess (Var Local «tokens») (Const (1w:word64)))
       (Seq (Annot «location» «(30:4 30:13)») (Assign Local «result» (Const 1w)))
       (Seq (Annot «location» «(32:4 32:13)») (Assign Local «result» (Const 0w)))
End

(* --- the core relation: tokens/result in locals, loose range for the guard. --- *)
Definition rateAdmitRel_def:
  rateAdmitRel (tks:num) (r0:word64) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «tokens» = SOME (ValWord (n2w tks)) /\
    FLOOKUP s.locals «result» = SOME (ValWord r0) /\
    tks < 4294967296
End

(* ===========================================================================
   The headline core equation, derived AUTOMATICALLY by the NEW REUSABLE tactic
   `panAutoLib.panLinkA_branch_le`.  The ONLY per-primitive inputs are the three
   definitional theorems and the finite `<=`-guard list.
   =========================================================================== *)
Theorem evaluate_rateAdmitCore:
  rateAdmitRel tks r0 s ==>
  evaluate (rateAdmitCore, s) =
    (NONE, set_var «result» (ValWord (n2w (rateAdmit tks))) s)
Proof
  panLinkA_branch_le (rateAdmitRel_def, rateAdmit_def, rateAdmitCore_def)
    [“1 <= tks”]
QED

(* --- framed: for the whole-main wrapper; NO clock precondition (branch-only) --- *)
Theorem evaluate_rateAdmitCore_framed:
  rateAdmitRel tks r0 s ==>
  ?s'. evaluate (rateAdmitCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (rateAdmit tks))) /\
       (!v. v <> «result» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >> drule evaluate_rateAdmitCore >> strip_tac >>
  qexists_tac `set_var «result» (ValWord (n2w (rateAdmit tks))) s` >>
  simp [set_var_def, FLOOKUP_UPDATE] >> rw [] >> simp [FLOOKUP_UPDATE]
QED

Theorem rateAdmitCore_noFFI:
  noFFI rateAdmitCore
Proof
  REWRITE_TAC [rateAdmitCore_def] >> EVAL_TAC
QED

val _ = export_theory ();
