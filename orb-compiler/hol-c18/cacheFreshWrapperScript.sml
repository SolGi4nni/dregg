(* ===========================================================================
   C15 probe, PART B — the FFI-oracle contract + the verbatim emitted mainBody
   for the THIRD (status-classifier) primitive.

   Structurally identical to C14's stepWrapper (same load_vec/report_vec ExtCall
   shape), but a SIMPLER control block: ONE input word `code` at [base+0) and a
   result slot at [base+8) — the classifier reads a single word (N=1, vs step's
   two), so the ctrlStaged/FFI contract is one word shorter and the store/report
   sit at +8w (vs step's +24w).  buf = base+16w; load_vec conf length = 8w.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory;
open cacheFreshCoreTheory;      (* cacheFreshCore, cacheFresh, evaluate_cacheFreshCore_framed, cacheFreshCore_noFFI *)
open cacheFreshLinkBInstTheory; (* cacheFreshProg, cacheFreshProg_def *)

val _ = new_theory "cacheFreshWrapper";

(* the staged control block the load_vec oracle establishes:
   [0)=code, [8)=result slot.  ONE input word, NO arena (no loop => no memRel). *)
Definition cacheFreshCtrlStaged_def:
  cacheFreshCtrlStaged (code:num) (ba:word64) (s:(64,'ffi) panSem$state) <=>
    ba IN s.memaddrs /\ s.memory ba = Word (n2w code) /\
    (ba + 8w) IN s.memaddrs /\
    code < 4294967296
End

(* THE SINGLE NAMED TRUSTED ASSUMPTION — the FFI-oracle contract (same shape as
   step/boundScan): (L) @load_vec stages the control block per cacheFreshCtrlStaged;
   (R) @report_vec emits the result word onto the observable FFI trace. *)
Definition cacheFreshFFI_def:
  cacheFreshFFI (code:num) (s0:(64,'ffi) panSem$state) <=>
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «base» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «buf»  = SOME (ValWord (s.base_addr + 16w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «base») (Const 8w)
                     (Var Local «buf») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         cacheFreshCtrlStaged code s.base_addr s1 /\
         s1.ffi.io_events = s.ffi.io_events ++ loadEv) /\
    (!(s:(64,'ffi) panSem$state) (w:word64).
           FLOOKUP s.locals «base» = SOME (ValWord s.base_addr) /\
           (s.base_addr + 8w) IN s.memaddrs /\
           s.memory (s.base_addr + 8w) = Word w ==>
       ?s2 rb.
         evaluate (ExtCall «report_vec» (Op Add [Var Local «base»; Const 8w])
                     (Const 8w) (Var Local «base») (Const 8w), s) = (NONE, s2) /\
         s2.clock = s.clock /\
         s2.ffi.io_events =
           s.ffi.io_events ++ [IO_event (ffi$ExtCall «report_vec») (word_to_bytes w F) rb])
End

(* cacheFreshMainBody = the VERBATIM body of «main» in cacheFreshProg (the parser
   output), with the C15 `cacheFreshCore` constant folded in for its decision `If`.
   BUILT BY ML SURGERY from `functions cacheFreshProg` (no hand transcription):
   extract the «main» body, then substitute the emitted If-node (= rhs of
   cacheFreshCore_def) by the constant `cacheFreshCore`.  So cacheFreshMainBody IS the
   parser output modulo the cacheFreshCore abbreviation. *)
val funcs_body = (REWRITE_CONV [cacheFreshProg_def] THENC EVAL)
                   “functions cacheFreshProg” |> concl |> rhs;
(* funcs_body = [(«main», [], <BODY>)] — dig out <BODY> *)
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
val body64      = Term.inst [Type.alpha |-> “:64”] body_tm;
val coreTm      = rhs (concl cacheFreshCore_def);
val body_core   = Term.subst [coreTm |-> “cacheFreshCore”] body64;
val cacheFreshMainBody_def =
  new_definition("cacheFreshMainBody_def", “cacheFreshMainBody = ^body_core”);

(* sanity: the substitution actually fired (cacheFreshCore occurs in the folded body) *)
val _ = if Term.free_in “cacheFreshCore” body_core then ()
        else raise Fail "cacheFreshCore substitution did not fire";

val _ = export_theory ();
