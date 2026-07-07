(* GENERATED (SCAFFOLD) by emit.py from descriptor: machine_toggle
   Template: hol-emit/template/machine.sml.tmpl

   Machine-family Link A refinement SCAFFOLD. The SPEC (a finite-state
   transition), the .pnk dispatch AST, and the state relation are emitted and
   TYPECHECK against the real panSem. The refinement theorem is STATED as an
   OBLIGATION (not discharged) — honest scope: the machine template is
   scaffolded, the region template is fully paid. *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory;

val _ = new_theory "toggleEmit";

(* ---------------------------------------------------------------------------
   The Lean SPEC: a finite-state transition step.
   State = bool (2-state toggle), Input ignored here, Output = num (encoded to
   a word). toggle q i = (next state, emitted output).
   --------------------------------------------------------------------------- *)
Definition toggle_def:
  toggle (q:bool) (i:num) = (~q, if q then 1n else 0n)
End

(* state encoding: F |-> 0w, T |-> 1w *)
Definition encQ_def:
  encQ (q:bool) = (if q then 1w else 0w):word64
End

(* ---------------------------------------------------------------------------
   The IMPLEMENTATION fragment: the .pnk dispatch (single step, no run loop).
     if state == 0 { state = 1; out = 0 }
                     else  { state = 0; out = 1 }
   --------------------------------------------------------------------------- *)
Definition toggleStep_def:
  toggleStep =
    If (Cmp Equal (Var Local (strlit "state")) (Const (0w:word64)))
       (Seq (Assign Local (strlit "state") (Const (1w:word64)))
            (Assign Local (strlit "out")   (Const (0w:word64))))
       (Seq (Assign Local (strlit "state") (Const (0w:word64)))
            (Assign Local (strlit "out")   (Const (1w:word64))))
End

(* ---------------------------------------------------------------------------
   The state relation: the current-state tag and output slot as words.
   --------------------------------------------------------------------------- *)
Definition mRel_def:
  mRel (q:bool) o0 (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "state") = SOME (ValWord (encQ q)) /\
    FLOOKUP s.locals (strlit "out")   = SOME (ValWord o0)
End

val _ = export_theory ();

(* ===========================================================================
   OBLIGATION (NOT DISCHARGED — machine template scaffold).

   The Link A theorem the machine template must emit-and-prove is the transition
   refinement — real `panSem$evaluate` of the dispatch takes the relation from
   `q` to `FST (toggle q i)` and writes the encoded output:

     |- mRel q o0 s ==>
        ?s'. evaluate (toggleStep, s) = (NONE, s') /\
             mRel (FST (toggle q i))
                          (n2w (SND (toggle q i))) s'

   How it is proven — and how the machine template DIFFERS from the region one:

   (1) DISPATCH, not a bounds `If`. The proof is a finite CASE SPLIT on the
       state tag (`Cases_on q`), each arm reducing the real panSem `evaluate` of
       the `Seq` of `Assign`s. This is the direct analogue of the region
       `evaluate_impl` and equally tractable with the SAME eval/word toolkit
       (`eval_def`, `set_var_def`, `word_cmp_def`, `FLOOKUP_UPDATE`). For a
       k-state machine it is a k-way `Case`/nested-`If` and a k-way split.

   (2) THE RUN LOOP is the deferred cost. A machine that consumes an input
       STREAM wraps this step in a `While` over the input list. Its Link A is a
       loop-invariant induction over panSem's clocked `While` clause
       (`q_n = FOLDL (\q i. FST (toggle q i)) q0 inputs`), structurally
       identical to the region scan `While` deferred in C1 (§4-A-2). Same shape,
       same dominant cost, sitting on the proven single-step dispatch below it.

   So: machine template = { SPEC transition } x { dispatch AST } x { state
   relation } (all emitted above, all typecheck) + { case-split proof of the
   single step (tractable, region-toolkit) } + { `While` induction for the
   stream (deferred, = the region scan-loop cost) }.
   =========================================================================== *)
