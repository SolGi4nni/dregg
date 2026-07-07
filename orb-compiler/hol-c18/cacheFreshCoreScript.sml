(* ===========================================================================
   C18 probe, FRAGMENT 1 — the DEPLOYED serve cache-freshness test's Link-A core,
   derived AUTOMATICALLY by the EXISTING `panLinkA_branch` tactic (C15's `<`
   machinery) — with NO new metatheory.  This is the result that C15's ordered-`<`
   cascade automation reaches REAL deployed serve code (C17 showed the same for
   `=`).

   THE FRAGMENT: `Cache.Meta.isFresh` from the drorb serve
   (orb/Cache.lean) — the RFC 9111 §4.2 freshness gate
   `response_is_fresh = (freshness_lifetime > current_age)`.  It is consulted by
   `Reactor.Stage.Cache.Config.onReq` -> `cacheEmptyStage`, position 4 of
   `Reactor.Deploy.deployStagesFull2`.  Genuinely LOOP-FREE: a single `<` on the
   resolved age vs the stored lifetime, no recursion, no `While`.

   Faithful lowering: the runtime input is the resolved `current_age` word `age`;
   the configured `freshnessLifetime` is the fixed stored-response field (deployed
   value 100).  `Meta.isFresh` becomes `if age < 100 then fresh(1) else stale(0)`.
   `cacheFreshCore` is the VERBATIM `If` node lifted from `functions
   cacheFreshProg` (the verified parser's output on cachefresh.pnk).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open panAutoTheory;        (* eval_lt_pinned, Annot_Seq_eval, ... *)
open c14GenericTheory;     (* noFFI (generic, reused) *)
open panAutoLib;           (* panLinkA_branch — reusable ordered-`<` Link-A tactic *)

val _ = new_theory "cacheFreshCore";

(* --- the Lean SPEC, re-declared: byte-identical to Cache.Meta.isFresh at the
   deployed freshnessLifetime 100 (fresh = 1, stale = 0). --- *)
Definition cacheFresh_def:
  cacheFresh (age:num) = if age < 100 then 1n else 0n
End

(* --- cacheFreshCore = the VERBATIM emitted If node (from `functions
   cacheFreshProg`), leaves behind their location Annots. --- *)
Definition cacheFreshCore_def:
  cacheFreshCore =
    If (Cmp Less (Var Local «age») (Const (100w:word64)))
       (Seq (Annot «location» «(30:4 30:13)») (Assign Local «result» (Const 1w)))
       (Seq (Annot «location» «(32:4 32:13)») (Assign Local «result» (Const 0w)))
End

(* --- the core relation: age/result in locals, loose range for the guard. --- *)
Definition cacheFreshRel_def:
  cacheFreshRel (age:num) (r0:word64) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «age» = SOME (ValWord (n2w age)) /\
    FLOOKUP s.locals «result» = SOME (ValWord r0) /\
    age < 4294967296
End

(* ===========================================================================
   The headline core equation, derived AUTOMATICALLY by the REUSED tactic
   `panAutoLib.panLinkA_branch` (C15's `<` tactic, UNCHANGED).  The ONLY
   per-primitive inputs are the three definitional theorems and the finite
   guard list.
   =========================================================================== *)
Theorem evaluate_cacheFreshCore:
  cacheFreshRel age r0 s ==>
  evaluate (cacheFreshCore, s) =
    (NONE, set_var «result» (ValWord (n2w (cacheFresh age))) s)
Proof
  panLinkA_branch (cacheFreshRel_def, cacheFresh_def, cacheFreshCore_def)
    [“age < 100n”]
QED

(* --- framed: for the whole-main wrapper; NO clock precondition (branch-only) --- *)
Theorem evaluate_cacheFreshCore_framed:
  cacheFreshRel age r0 s ==>
  ?s'. evaluate (cacheFreshCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (cacheFresh age))) /\
       (!v. v <> «result» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >> drule evaluate_cacheFreshCore >> strip_tac >>
  qexists_tac `set_var «result» (ValWord (n2w (cacheFresh age))) s` >>
  simp [set_var_def, FLOOKUP_UPDATE] >> rw [] >> simp [FLOOKUP_UPDATE]
QED

Theorem cacheFreshCore_noFFI:
  noFFI cacheFreshCore
Proof
  REWRITE_TAC [cacheFreshCore_def] >> EVAL_TAC
QED

val _ = export_theory ();
