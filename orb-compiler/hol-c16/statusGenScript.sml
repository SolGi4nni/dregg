(* ===========================================================================
   C16 — DEMONSTRATION 1: the status classifier (N=1 read, +8w result slot) whole
   -program wrapper, generated MECHANICALLY by panWrapperLib.mk_mainRefine from the
   parameters ⟨reads=[code], bufOff=16w, koff=8w, spec=n2w(statusClass code)⟩ —
   NO hand-written wrapper proof.  Reproduces C15's statusMainBody_refines.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory statusCoreTheory statusWrapperTheory statusLinkBInstTheory;
open panWrapperLib;

val _ = new_theory "statusGen";

val R = mk_wrapper
  { prefix       = "status",
    ffiName      = "statusFFI",        ffiDef        = statusFFI_def,
    ffiArgs      = "code",
    ctrlName     = "statusCtrlStaged", ctrlStagedDef = statusCtrlStaged_def,
    relName      = "statusRel",        relDef        = statusRel_def,
    reads        = [("code","code")],
    bufOff       = "16w",              koff          = "8w",
    boundsStr    = "code < 1000",
    specWord     = "n2w (statusClass code)",
    coreName     = "statusCore",       coreDef       = statusCore_def,
    coreFramed   = evaluate_statusCore_framed,
    coreNoFFI    = statusCore_noFFI,
    mainBodyName = "statusMainBody",   mainBodyDef   = statusMainBody_def,
    progName     = "statusClassProg",  progDef       = statusClassProg_def,
    linkB        = statusClassProg_linkB };

val _ = print "\n@@@ status mainRefine:\n";
val _ = print (thm_to_string (#mainRefine R));
val _ = print "\n@@@ status MACHINE CODE:\n";
val _ = print (thm_to_string (#machineCode R));
val _ = print ("\n@@@ statusGen axioms = " ^ Int.toString (length (axioms "statusGen")) ^ "\n");
val _ = print "\n@@@ statusGen DONE\n";

val _ = export_theory ();
