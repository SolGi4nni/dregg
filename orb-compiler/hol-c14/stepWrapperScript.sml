(* ===========================================================================
   C14 probe, PART B — the FFI-oracle contract + the verbatim emitted mainBody.
   Structurally IDENTICAL to C13's boundScanWrapper (same load_vec/report_vec
   ExtCall shape, same control-block staging), but with a SIMPLER ctrlStaged:
   only the two control words c/b + the result slot, and NO arena `memRel`
   (the branch-only primitive has no scanned buffer).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory;
open stepCoreTheory;      (* stepCore, mstep, evaluate_stepCore_framed, stepCore_noFFI *)
open stepLinkBInstTheory; (* stepGateProg, stepGateProg_def *)

val _ = new_theory "stepWrapper";

(* the staged control block the load_vec oracle establishes:
   [0)=c, [8)=b, [24)=result slot.  NO arena (no loop => no memRel). *)
Definition stepCtrlStaged_def:
  stepCtrlStaged (c:num) (b:num) (ba:word64) (s:(64,'ffi) panSem$state) <=>
    ba IN s.memaddrs /\ s.memory ba = Word (n2w c) /\
    (ba + 8w) IN s.memaddrs /\ s.memory (ba + 8w) = Word (n2w b) /\
    (ba + 24w) IN s.memaddrs /\
    c <= 255 /\ b < 256
End

(* THE SINGLE NAMED TRUSTED ASSUMPTION — the FFI-oracle contract (same shape as
   boundScanFFI): (L) @load_vec stages the control block per stepCtrlStaged;
   (R) @report_vec emits the result word onto the observable FFI trace. *)
Definition stepFFI_def:
  stepFFI (c:num) (b:num) (s0:(64,'ffi) panSem$state) <=>
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «base» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «buf»  = SOME (ValWord (s.base_addr + 32w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «base») (Const 24w)
                     (Var Local «buf») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         stepCtrlStaged c b s.base_addr s1 /\
         s1.ffi.io_events = s.ffi.io_events ++ loadEv) /\
    (!(s:(64,'ffi) panSem$state) (w:word64).
           FLOOKUP s.locals «base» = SOME (ValWord s.base_addr) /\
           (s.base_addr + 24w) IN s.memaddrs /\
           s.memory (s.base_addr + 24w) = Word w ==>
       ?s2 rb.
         evaluate (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w])
                     (Const 8w) (Var Local «base») (Const 8w), s) = (NONE, s2) /\
         s2.clock = s.clock /\
         s2.ffi.io_events =
           s.ffi.io_events ++ [IO_event (ffi$ExtCall «report_vec») (word_to_bytes w F) rb])
End

(* stepMainBody = the VERBATIM body of «main» in stepGateProg (the parser
   output), with the C14 `stepCore` constant folded in for its decision `If`.
   BUILT BY ML SURGERY from `functions stepGateProg` (no hand transcription):
   extract the «main» body, then substitute the emitted If-node (= rhs of
   stepCore_def) by the constant `stepCore`.  So stepMainBody IS the parser
   output modulo the stepCore abbreviation. *)
val funcs_body = (REWRITE_CONV [stepGateProg_def] THENC EVAL)
                   “functions stepGateProg” |> concl |> rhs;
(* funcs_body = [(«main», [], <BODY>)] — dig out <BODY> *)
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
val body64      = Term.inst [Type.alpha |-> “:64”] body_tm;
val coreTm      = rhs (concl stepCore_def);
val body_core   = Term.subst [coreTm |-> “stepCore”] body64;
val stepMainBody_def =
  new_definition("stepMainBody_def", “stepMainBody = ^body_core”);

(* sanity: the substitution actually fired (stepCore occurs in the folded body) *)
val _ = if Term.free_in “stepCore” body_core then ()
        else raise Fail "stepCore substitution did not fire";

val _ = export_theory ();
