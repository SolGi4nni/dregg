(* ===========================================================================
   C17 probe, PART A — the REAL deployed serve fragment's Link-A core, derived
   AUTOMATICALLY by the `panLinkA_branch_eq` tactic (no bespoke per-primitive
   hand proof).

   THE FRAGMENT: `Redirect.Code.status` from the drorb serve
   (orb/Redirect.lean) — the redirect-status pick of RFC 9110
   §15.4.  It is called by `Redirect.redirect` -> `redirectFor`/`redirectStage`,
   which is position 6 of `Reactor.Deploy.deployStagesFull2` (the real ten-stage
   orb serve).  It is genuinely LOOP-FREE: a total `match` on the 4-constructor
   `Code` enum, no recursion, no `While`.

   Faithful lowering: the `Code` enum is encoded as a tag word `code`
     moved301 = 0 , found302 = 1 , temp307 = 2 , perm308 = 3
   and `Redirect.Code.status` becomes the equality dispatch below.  UNLIKE C15's
   `statusClass` (an ORDERED `<` cascade), a real algebraic-type `match` lowers to
   an EQUALITY dispatch on the constructor tag — `Cmp Equal` guards — the one
   real-serve-specific friction this probe exercises.

   `redirectCore` is the VERBATIM `If` cascade lifted from `functions
   redirectStatusProg` (the verified parser's output on redirectstatus.pnk, dumped
   and transcribed exactly, Annot location strings included).  We prove, against
   real `panSem$evaluate`, that it writes EXACTLY the Lean spec's status number
   `n2w (redirectStatus code)` into the local «result».
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open panAutoTheory;        (* eq_n2w64, eval_eq_pinned, Annot_Seq_eval, ... *)
open c14GenericTheory;     (* noFFI (generic, reused) *)
open panAutoLib;           (* panLinkA_branch_eq — reusable equality Link-A tactic *)

val _ = new_theory "redirectCore";

(* --- the Lean SPEC, re-declared in HOL: byte-identical to Redirect.Code.status
   under the encoding moved301=0, found302=1, temp307=2, perm308=3. --- *)
Definition redirectStatus_def:
  redirectStatus (code:num) =
    if code = 0 then 301n
    else if code = 1 then 302n
    else if code = 2 then 307n
    else 308n
End

(* --- redirectCore = the VERBATIM emitted If cascade (from `functions
   redirectStatusProg`, the parser's output), with the Const-assign leaves behind
   their location Annots.  Transcribed exactly from the parser AST dump. --- *)
Definition redirectCore_def:
  redirectCore =
    If (Cmp Equal (Var Local «code») (Const (0w:word64)))
       (Seq (Annot «location» «(31:4 31:15)») (Assign Local «result» (Const 301w)))
       (Seq (Annot «location» «(33:7 39:19)»)
          (If (Cmp Equal (Var Local «code») (Const 1w))
             (Seq (Annot «location» «(34:6 34:17)») (Assign Local «result» (Const 302w)))
             (Seq (Annot «location» «(36:9 39:19)»)
                (If (Cmp Equal (Var Local «code») (Const 2w))
                   (Seq (Annot «location» «(37:8 37:19)») (Assign Local «result» (Const 307w)))
                   (Seq (Annot «location» «(39:8 39:19)») (Assign Local «result» (Const 308w)))))))
End

(* --- the core relation: code/result in locals, range for the guards.  The real
   domain is the 4 tags {0,1,2,3}; `code < 1000` is a loose, template-uniform
   bound (the equality dispatch is correct for ALL code — off-domain both spec
   and impl fall to 308 — so no monotonic-domain hypothesis is needed). --- *)
Definition redirectRel_def:
  redirectRel (code:num) (r0:word64) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «code» = SOME (ValWord (n2w code)) /\
    FLOOKUP s.locals «result» = SOME (ValWord r0) /\
    code < 1000
End

(* ===========================================================================
   The headline core equation, derived AUTOMATICALLY by the REUSABLE tactic
   `panAutoLib.panLinkA_branch_eq`.  The ONLY per-primitive inputs are the three
   definitional theorems and the finite equality-guard list.  No bespoke hand
   proof.
   =========================================================================== *)
Theorem evaluate_redirectCore:
  redirectRel code r0 s ==>
  evaluate (redirectCore, s) =
    (NONE, set_var «result» (ValWord (n2w (redirectStatus code))) s)
Proof
  panLinkA_branch_eq (redirectRel_def, redirectStatus_def, redirectCore_def)
    [“code = 0n”, “code = 1n”, “code = 2n”]
QED

(* --- framed: for the whole-main wrapper; NO clock precondition (branch-only) --- *)
Theorem evaluate_redirectCore_framed:
  redirectRel code r0 s ==>
  ?s'. evaluate (redirectCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (redirectStatus code))) /\
       (!v. v <> «result» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >> drule evaluate_redirectCore >> strip_tac >>
  qexists_tac `set_var «result» (ValWord (n2w (redirectStatus code))) s` >>
  simp [set_var_def, FLOOKUP_UPDATE] >> rw [] >> simp [FLOOKUP_UPDATE]
QED

(* redirectCore performs no FFI: reusing the generic noFFI predicate. *)
Theorem redirectCore_noFFI:
  noFFI redirectCore
Proof
  REWRITE_TAC [redirectCore_def] >> EVAL_TAC
QED

val _ = export_theory ();
