(* ===========================================================================
   C16 probe — THE WHOLE-PROGRAM WRAPPER GENERATOR (ML).  `mk_wrapper` closes the
   last automation gap for the loop-free class named in C14 §4.2 / C15 §6: it
   turns the fixed wrapper TEMPLATE (MainRefine + Sem + Install + EndToEnd) into a
   mechanical GENERATOR — a fold over the N-read Dec spine with the read-count N
   and the result-slot offset as parameters.  NO new metatheory: every obligation
   is discharged by the same reusable c14Generic lemmas the hand template used;
   the generator only ASSEMBLES the proof mechanically for arbitrary N.

     mk_wrapper : params -> { mainRefine, callMainRun, mainSemantics,
                              semanticsDecls, machineCode }

   The per-primitive inputs are exactly: the parsed program constant + its Link B,
   the core Link-A theorem (framed + noFFI), the relation/ctrl-block/FFI decls, the
   read list (local names + their pinned num-vars), the buf offset, and the result
   store offset.  No proof is written by hand per primitive.
   =========================================================================== *)
structure panWrapperLib =
struct

open HolKernel boolLib bossLib Parse proofManagerLib markerLib;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory pairTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open c14GenericTheory;

(* --- quotation helpers ---------------------------------------------------- *)
fun QS s = [QUOTE s] : term frag list;
fun EB q tac = ignore (e (q by tac));   (* prove a subgoal quotation by tac *)
val ABB = fn nm => Abbr (QS nm);        (* Abbr `nm` from a string *)
fun headName t = #Name (dest_thy_const (fst (strip_comb t))) handle _ => "";

(* =========================================================================
   mk_mainRefine — the whole-`main` FFI-trace refinement, mechanically for N reads.
   ========================================================================= *)
datatype nodeKind = KDEC | KANNOT | KLOADSEQ;

fun mk_mainRefine
      { prefix       : string,
        ffiName      : string,      ffiDef        : thm,
        ffiArgs      : string,      (* e.g. "code" or "c b" *)
        ctrlName     : string,      ctrlStagedDef : thm,
        relName      : string,      relDef        : thm,
        reads        : (string * string) list,  (* (localName, numVar) in order *)
        bufOff       : string,      koff          : string,
        boundsStr    : string,      (* the ctrl bounds, e.g. "code < 1000" *)
        specWord     : string,      (* e.g. "n2w (statusClass code)" *)
        coreName     : string,      coreFramed    : thm,   coreNoFFI : thm,
        mainBodyName : string,      mainBodyDef   : thm } : thm =
  let
    val N        = length reads
    val locals   = ["base","buf"] @ map #1 reads @ ["result"]
    fun stl s    = "(strlit \"" ^ s ^ "\")"
    fun readOff i = Int.toString (8 * (i-1)) ^ "w"    (* read i offset, 1-based *)
    val nUnders  = length (String.tokens Char.isSpace ffiArgs) + 1
    val ffiPat   = ffiName ^ String.concat (List.tabulate (nUnders, fn _ => " _"))

    (* ---- the goal ---- *)
    val goal = QS (
      ffiName ^ " " ^ ffiArgs ^ " s0 /\\ s0.locals = FEMPTY ==>\n" ^
      " ?sF loadEv rb.\n" ^
      "   evaluate (" ^ mainBodyName ^ ", s0) = (SOME (Return (ValWord 0w)), sF) /\\\n" ^
      "   sF.ffi.io_events = s0.ffi.io_events ++ loadEv ++\n" ^
      "     [IO_event (ffi$ExtCall " ^ stl "report_vec" ^ ")\n" ^
      "        (word_to_bytes (" ^ specWord ^ " : word64) F) rb]")
    val _ = g goal

    (* ---- ML peel of the emitted mainBody spine ---- *)
    val ty64  = fcpSyntax.mk_numeric_type (Arbnum.fromInt 64)
    val mbT   = Term.inst [Type.alpha |-> ty64] (rhs (concl mainBodyDef))
    (* walk down the single-successor rand chain, classifying nodes; stop when the
       (N+3)-th Dec (the result Dec) is consumed — its body is RBODY. *)
    val totalDecs = N + 3
    fun walk t acc dc =
      let val hn = headName t in
        if hn = "Dec" then
          (if dc + 1 = totalDecs then (List.rev ((t,KDEC)::acc), rand t)
           else walk (rand t) ((t,KDEC)::acc) (dc+1))
        else if hn = "Seq" then
          let val a1 = rand (rator t)
              val k  = if headName a1 = "Annot" then KANNOT else KLOADSEQ
          in walk (rand t) ((t,k)::acc) dc end
        else (List.rev acc, t)
      end
    val (nodes, RBODY) = walk mbT [] 0
    (* peel RBODY = Seq CORE (Seq STORE (Seq REPORT RETURN)) *)
    val CORE  = rand (rator RBODY);  val REST1 = rand RBODY;
    val STORE = rand (rator REST1);  val REST2 = rand REST1;
    val REPORT= rand (rator REST2);  val RETURN= rand REST2;
    (* the load seq is the LOADSEQ node's first component *)
    val loadSeqNode = #1 (valOf (List.find (fn (_,k) => k=KLOADSEQ) nodes))
    val loadSeq = rand (rator loadSeqNode)

    (* ---- per-Dec metadata, in walk order: base, buf, reads.., result ---- *)
    fun postState k =
      if k = 0 then "sB"
      else if k = 1 then "sBU"
      else if k = N + 2 then "sRz"
      else "sV" ^ Int.toString (k - 1)        (* reads: k-1 in 1..N *)
    fun preState k =
      if k = 0 then "s0"
      else if k = 1 then "sB"
      else if k = 2 then "s1"                 (* first read enters at s1 *)
      else if k = N + 2 then ("sV" ^ Int.toString N)
      else "sV" ^ Int.toString (k - 2)        (* read j=k-1 enters at sV(j-1) *)
    fun decVal k =
      if k = 0 then "ValWord ba"
      else if k = 1 then "ValWord (ba + " ^ bufOff ^ ")"
      else if k = N + 2 then "ValWord 0w"
      else "ValWord (n2w " ^ #2 (List.nth (reads, k-2)) ^ ")"
    fun decEq k =
      preState k ^ " with locals := _ = " ^ postState k

    (* ================= run the proof ================= *)
    val _ = e strip_tac
    val _ = e (qpat_x_assum (QS ffiPat)
                 (strip_assume_tac o SIMP_RULE std_ss [ffiDef]))
    val _ = e (qabbrev_tac (QS "ba = s0.base_addr"))
    (* distinctness of all local keys *)
    val pairs = let fun go [] = [] | go (x::xs) = map (fn y => (x,y)) xs @ go xs
                in go locals end
    val distinctConj =
      String.concatWith " /\\ "
        (map (fn (a,b) => stl a ^ " <> " ^ stl b) pairs)
    val _ = EB (QS distinctConj) EVAL_TAC
    val _ = e (qabbrev_tac (QS ("sB = s0 with locals := s0.locals |+ (" ^
                                stl "base" ^ ", ValWord ba)")))
    val _ = e (qabbrev_tac (QS ("sBU = sB with locals := sB.locals |+ (" ^
                                stl "buf" ^ ", ValWord (ba + " ^ bufOff ^ "))")))
    val _ = EB (QS ("sBU.base_addr = ba /\\ sBU.clock = s0.clock /\\ sBU.memory = s0.memory /\\ " ^
                    "sBU.memaddrs = s0.memaddrs /\\ sBU.be = s0.be /\\ sBU.ffi = s0.ffi /\\ " ^
                    "sBU.structs = s0.structs"))
                (simp [ABB "sBU", ABB "sB", ABB "ba"])
    val _ = EB (QS ("FLOOKUP sBU.locals " ^ stl "base" ^ " = SOME (ValWord ba) /\\ " ^
                    "FLOOKUP sBU.locals " ^ stl "buf" ^ " = SOME (ValWord (ba + " ^ bufOff ^ "))"))
                (simp [ABB "sBU", ABB "sB", FLOOKUP_UPDATE] >> fs [])
    (* apply the load oracle *)
    val _ = e (qpat_x_assum (QS "!s. _ ==> _") (qspec_then (QS "sBU") mp_tac))
    val _ = e (impl_tac >- fs [])
    val _ = e strip_tac
    (* s1 facts from ctrlStaged *)
    val s1facts =
      String.concatWith " /\\ "
        (List.tabulate (N, fn j =>
           let val i = j+1 val xi = #2 (List.nth (reads, j)) in
             if i = 1 then "ba IN s1.memaddrs /\\ s1.memory ba = Word (n2w " ^ xi ^ ")"
             else "(ba + " ^ readOff i ^ ") IN s1.memaddrs /\\ s1.memory (ba + " ^
                  readOff i ^ ") = Word (n2w " ^ xi ^ ")"
           end)
         @ ["(ba + " ^ koff ^ ") IN s1.memaddrs", boundsStr])
    val _ = EB (QS s1facts) (fs [ctrlStagedDef])
    val _ = EB (QS ("FLOOKUP s1.locals " ^ stl "base" ^ " = SOME (ValWord ba) /\\ " ^
                    "FLOOKUP s1.locals " ^ stl "buf" ^ " = SOME (ValWord (ba + " ^ bufOff ^ "))"))
                ((QS "s1.locals = sBU.locals") by (fs []) >> fs [])
    (* ---- per-read reads ---- *)
    val prevAbbrs = ref ([] : string list)   (* sV names built so far, newest first *)
    fun doRead j =
      let val i = j+1
          val (li, xi) = List.nth (reads, j)
          val pv  = if i = 1 then "s1" else "sV" ^ Int.toString (i-1)
          val cur = "sV" ^ Int.toString i
          val allA = map ABB (!prevAbbrs)
      in
        (if i = 1 then
           EB (QS ("eval s1 (Load One (Var Local " ^ stl "base" ^ ")) = SOME (ValWord (n2w " ^ xi ^ "))"))
              (irule eval_load_ctrl >> qexists_tac (QS "ba") >> fs [])
         else
          (EB (QS ("(ba + " ^ readOff i ^ ") IN " ^ pv ^ ".memaddrs /\\ " ^
                   pv ^ ".memory (ba + " ^ readOff i ^ ") = Word (n2w " ^ xi ^ ")"))
              (gvs (map ABB (!prevAbbrs)));
           EB (QS ("eval " ^ pv ^ " (Load One (Op Add [Var Local " ^ stl "base" ^ "; Const " ^
                   readOff i ^ "])) = SOME (ValWord (n2w " ^ xi ^ "))"))
              (irule eval_load_off >> qexists_tac (QS "ba") >> fs [])));
        e (qabbrev_tac (QS (cur ^ " = " ^ pv ^ " with locals := " ^ pv ^
                            ".locals |+ (" ^ stl li ^ ", ValWord (n2w " ^ xi ^ "))")));
        prevAbbrs := cur :: (!prevAbbrs);
        EB (QS (cur ^ ".memory = s1.memory /\\ " ^ cur ^ ".memaddrs = s1.memaddrs /\\ " ^
                cur ^ ".be = s1.be /\\ " ^ cur ^ ".structs = s1.structs /\\ " ^
                cur ^ ".clock = s1.clock /\\ " ^ cur ^ ".ffi = s1.ffi"))
           (simp (map ABB (!prevAbbrs)) >> fs []);
        EB (QS ("FLOOKUP " ^ cur ^ ".locals " ^ stl "base" ^ " = SOME (ValWord ba)"))
           (simp (ABB cur :: [FLOOKUP_UPDATE]) >> fs [])
      end
    val _ = List.tabulate (N, doRead)
    (* ---- sRz + relation ---- *)
    val sVN = "sV" ^ Int.toString N
    val allV = map ABB (!prevAbbrs)
    val _ = e (qabbrev_tac (QS ("sRz = " ^ sVN ^ " with locals := " ^ sVN ^
                                ".locals |+ (" ^ stl "result" ^ ", ValWord 0w)")))
    val _ = EB (QS ("sRz.memory = s1.memory /\\ sRz.memaddrs = s1.memaddrs /\\ sRz.be = s1.be /\\ " ^
                    "sRz.structs = s1.structs /\\ sRz.clock = s1.clock /\\ sRz.ffi = s1.ffi /\\ " ^
                    "sRz.base_addr = ba"))
                (simp (ABB "sRz" :: allV) >> fs [])
    val flookupRz =
      String.concatWith " /\\ "
        (map (fn (li,xi) => "FLOOKUP sRz.locals " ^ stl li ^ " = SOME (ValWord (n2w " ^ xi ^ "))")
             reads
         @ ["FLOOKUP sRz.locals " ^ stl "result" ^ " = SOME (ValWord 0w)",
            "FLOOKUP sRz.locals " ^ stl "base" ^ " = SOME (ValWord ba)"])
    val _ = EB (QS flookupRz) (simp (ABB "sRz" :: FLOOKUP_UPDATE :: allV) >> fs [])
    val _ = EB (QS (relName ^ " " ^ ffiArgs ^ " 0w sRz")) (simp [relDef] >> fs [])
    (* ---- the core (no clock precondition) ---- *)
    val _ = e (drule coreFramed >> strip_tac)
    val _ = e (qmatch_asmsub_rename_tac (QS ("evaluate (" ^ coreName ^ ", sRz) = (NONE, sCore)")))
    val _ = e (qabbrev_tac (QS ("wstar = " ^ specWord ^ " : word64")))
    val _ = EB (QS ("FLOOKUP sCore.locals " ^ stl "result" ^ " = SOME (ValWord wstar)"))
                (fs [ABB "wstar"])
    val _ = EB (QS ("FLOOKUP sCore.locals " ^ stl "base" ^ " = FLOOKUP sRz.locals " ^ stl "base"))
                (first_x_assum (qspec_then (QS (stl "base")) mp_tac) >>
                 impl_tac >- EVAL_TAC >> simp [])
    val _ = EB (QS ("FLOOKUP sCore.locals " ^ stl "base" ^ " = SOME (ValWord ba)")) (fs [])
    val _ = EB (QS "sCore.clock <= sRz.clock") (imp_res_tac evaluate_clock >> fs [])
    val _ = EB (QS "sCore.memaddrs = s1.memaddrs /\\ sCore.base_addr = ba")
                (imp_res_tac evaluate_invariants >> gvs [])
    val _ = EB (QS "sCore.ffi.io_events = s0.ffi.io_events ++ loadEv")
                ((QS "sCore.ffi.io_events = sRz.ffi.io_events") by
                    ((QS ("evaluate (" ^ coreName ^ ", sRz) = (NONE, sCore)")) by (fs []) >>
                     drule noFFI_io_events >> simp [coreNoFFI]) >> fs [])
    (* ---- store / report / return ---- *)
    val _ = EB (QS ("(ba + " ^ koff ^ ") IN sCore.memaddrs")) (gvs [])
    val _ = e (qabbrev_tac (QS ("sS = sCore with memory := ((ba + " ^ koff ^ ") =+ Word wstar) sCore.memory")))
    val _ = EB (QS ("evaluate (Store (Op Add [Var Local " ^ stl "base" ^ "; Const " ^ koff ^
                    "]) (Var Local " ^ stl "result" ^ "), sCore) = (NONE, sS)"))
                (simp [ABB "sS"] >> irule evaluate_store_result >> fs [])
    val _ = EB (QS ("sS.base_addr = ba /\\ sS.memaddrs = sCore.memaddrs /\\ sS.locals = sCore.locals /\\ " ^
                    "sS.clock = sCore.clock /\\ sS.ffi = sCore.ffi")) (simp [ABB "sS"])
    val _ = EB (QS ("FLOOKUP sS.locals " ^ stl "base" ^ " = SOME (ValWord sS.base_addr)")) (gvs [])
    val _ = EB (QS ("(sS.base_addr + " ^ koff ^ ") IN sS.memaddrs")) (gvs [])
    val _ = EB (QS ("sS.memory (sS.base_addr + " ^ koff ^ ") = Word wstar"))
                (gvs [ABB "sS", combinTheory.APPLY_UPDATE_THM])
    val _ = e (qpat_x_assum (QS "!s w. _") (qspecl_then [QS "sS", QS "wstar"] mp_tac))
    val _ = e (impl_tac >- fs [])
    val _ = e strip_tac
    val _ = e (qmatch_asmsub_rename_tac
                 (QS ("evaluate (ExtCall " ^ stl "report_vec" ^ " _ _ _ _, sS) = (NONE, sRep)")))
    val _ = EB (QS "sS.ffi.io_events = s0.ffi.io_events ++ loadEv") (fs [])
    val _ = e (qabbrev_tac (QS ("tr = s0.ffi.io_events ++ loadEv ++ [IO_event (ffi$ExtCall " ^
                                stl "report_vec" ^ ") (word_to_bytes wstar F) rb]")))
    val _ = EB (QS "sRep.ffi.io_events = tr") (simp [ABB "tr"] >> fs [])
    val _ = EB (QS "evaluate (Return (Const 0w), sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)")
                (simp [evaluate_def, eval_def, size_of_sh_with_ctxt_def, shape_of_def])
    val _ = EB (QS "(empty_locals sRep).ffi.io_events = tr") (simp [empty_locals_def])
    (* ---- RBODY base case (peel terms) ---- *)
    val _ = EB ([QUOTE "evaluate (", ANTIQUOTE RETURN,
                 QUOTE ", sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)"])
                (irule Annot_Seq >> fs [])
    val _ = EB ([QUOTE "evaluate (", ANTIQUOTE REPORT, QUOTE ", sS) = (NONE, sRep)"])
                (irule Annot_Seq >> fs [])
    val _ = EB ([QUOTE "evaluate (", ANTIQUOTE REST2,
                 QUOTE ", sS) = (SOME (Return (ValWord 0w)), empty_locals sRep)"])
                (irule Seq_thread >> qexists_tac (QS "sRep") >> fs [])
    val _ = EB ([QUOTE "evaluate (", ANTIQUOTE STORE, QUOTE ", sCore) = (NONE, sS)"])
                (irule Annot_Seq >> fs [])
    val _ = EB ([QUOTE "evaluate (", ANTIQUOTE REST1,
                 QUOTE ", sCore) = (SOME (Return (ValWord 0w)), empty_locals sRep)"])
                (irule Seq_thread >> qexists_tac (QS "sS") >> fs [])
    val _ = EB ([QUOTE "evaluate (", ANTIQUOTE CORE, QUOTE ", sRz) = (NONE, sCore)"])
                (irule Annot_Seq >> fs [])
    val _ = EB ([QUOTE "evaluate (", ANTIQUOTE RBODY,
                 QUOTE ", sRz) = (SOME (Return (ValWord 0w)), empty_locals sRep)"])
                (irule Seq_thread >> qexists_tac (QS "sCore") >> fs [])
    val _ = EB ([QUOTE "?st. evaluate (", ANTIQUOTE RBODY,
                 QUOTE ", sRz) = (SOME (Return (ValWord 0w)), st) /\\ st.ffi.io_events = tr"])
                (qexists_tac (QS "empty_locals sRep") >> fs [])
    (* ---- wrap prelude ---- *)
    val _ = EB (QS ("s0 with locals := s0.locals |+ (" ^ stl "base" ^ ", ValWord ba) = sB"))
                (simp [ABB "sB"])
    val _ = EB (QS ("sB with locals := sB.locals |+ (" ^ stl "buf" ^ ", ValWord (ba + " ^ bufOff ^ ")) = sBU"))
                (simp [ABB "sBU"])
    val _ = List.tabulate (N, fn j =>
              let val i = j+1 val (li,xi) = List.nth (reads,j)
                  val pv = if i=1 then "s1" else "sV" ^ Int.toString (i-1)
                  val cur = "sV" ^ Int.toString i in
                EB (QS (pv ^ " with locals := " ^ pv ^ ".locals |+ (" ^ stl li ^
                        ", ValWord (n2w " ^ xi ^ ")) = " ^ cur)) (simp [ABB cur])
              end)
    val _ = EB (QS (sVN ^ " with locals := " ^ sVN ^ ".locals |+ (" ^ stl "result" ^
                    ", ValWord 0w) = sRz")) (simp [ABB "sRz"])
    val _ = EB (QS "eval s0 BaseAddr = SOME (ValWord ba)") (simp [eval_def, ABB "ba"])
    val _ = EB (QS ("FLOOKUP sB.locals " ^ stl "base" ^ " = SOME (ValWord ba)"))
                (simp [ABB "sB", FLOOKUP_UPDATE] >> fs [])
    val _ = EB (QS ("eval sB (Op Add [Var Local " ^ stl "base" ^ "; Const " ^ bufOff ^
                    "]) = SOME (ValWord (ba + " ^ bufOff ^ "))"))
                (irule eval_var_add >> fs [])
    val _ = EB ([QUOTE "evaluate (", ANTIQUOTE loadSeq, QUOTE ", sBU) = (NONE, s1)"])
                (irule Annot_Seq >> first_assum ACCEPT_TAC)
    (* ---- forward wrap: bottom-up over the peeled spine ---- *)
    val decw = fn (vq, steq) =>
      irule Dec_trace >> qexists_tac (QS vq) >> rpt conj_tac >>
      TRY (qpat_x_assum (QS steq) (fn th => REWRITE_TAC [th])) >>
      FIRST [ first_assum ACCEPT_TAC,
              (simp [eval_def, shape_of_def] >> NO_TAC),
              (metis_tac []) ]
    val annotw = irule Annot_trace >> (first_assum ACCEPT_TAC ORELSE metis_tac [])
    val seqldw = irule Seq_trace >> qexists_tac (QS "s1") >> rpt conj_tac >>
                 FIRST [ first_assum ACCEPT_TAC, (fs [] >> NO_TAC), (metis_tac []) ]
    (* attach (for Dec) val/eq to each node; consume decs in top-down order *)
    fun label [] _ = []
      | label ((t,k)::rest) dc =
          (case k of
             KDEC => (t, k, SOME (decVal dc, decEq dc)) :: label rest (dc+1)
           | _    => (t, k, NONE) :: label rest dc)
    val infos = label nodes 0               (* top-down; index 0 = mbT (outermost) *)
    (* number of Decs strictly before node-index j = the dec-number of a Dec at j *)
    fun decPos j = length (List.filter (fn (_,k,_) => k=KDEC) (List.take (infos, j)))
    (* enter-state of node at index idx *)
    fun enterOf idx =
      let val (_,k,_) = List.nth (infos, idx) in
        case k of
          KDEC     => preState (decPos idx)
        | KLOADSEQ => "sBU"
        | KANNOT   =>
            let fun back j = if j < 0 then "s0"
                             else case List.nth (infos,j) of
                                    (_,KDEC,_)     => postState (decPos j)
                                  | (_,KLOADSEQ,_) => "s1"
                                  | _              => back (j-1)
            in back (idx-1) end
      end
    (* wrap bottom-up: indices length-1 down to 1 (excluding index 0 = mbT) *)
    val idxs = List.tabulate (length infos - 1, fn i => length infos - 1 - i)
    val _ = app (fn idx =>
              let val (t,k,d) = List.nth (infos, idx)
                  val enter = enterOf idx
                  val goalq = [QUOTE "?st'. evaluate (", ANTIQUOTE t,
                               QUOTE (", " ^ enter ^ ") = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")]
                  val tac = case (k,d) of
                              (KDEC, SOME (vq,steq)) => decw (vq, steq)
                            | (KANNOT, _)   => annotw
                            | (KLOADSEQ, _) => seqldw
                            | _ => raise Fail "wrap: bad node"
              in EB goalq tac end) idxs
    (* outermost: the mainBody constant *)
    val _ = EB (QS ("?sF. evaluate (" ^ mainBodyName ^ ", s0) = (SOME (Return (ValWord 0w)), sF) /\\ sF.ffi.io_events = tr"))
                (simp [Once mainBodyDef] >> annotw)
    (* close *)
    val _ = e (pop_assum strip_assume_tac)
    val _ = e (qexists_tac (QS "sF") >> qexists_tac (QS "loadEv") >> qexists_tac (QS "rb"))
    val _ = e (conj_tac >- first_assum ACCEPT_TAC)
    val _ = e (fs [ABB "tr", ABB "wstar"])
    val thm = top_thm ()
    val _ = save_thm (prefix ^ "MainBody_refines", thm)
  in thm end;

(* =========================================================================
   mk_wrapper — the WHOLE wrapper: MainRefine + Sem + Install + EndToEnd, all
   generated from the parameters.  Sem/Install/EndToEnd are the thin, uniform
   template stages (clock-lift, single-Function install, Link-B composition);
   they differ across primitives only in names + the spec-word + the FFI arity,
   so they are produced by `prove` from parameterized goals with the same fixed
   tactics the hand template used.
   ========================================================================= *)
fun mk_wrapper
      { prefix, ffiName, ffiDef, ffiArgs, ctrlName, ctrlStagedDef, relName, relDef,
        reads, bufOff, koff, boundsStr, specWord, coreName, coreDef, coreFramed,
        coreNoFFI, mainBodyName, mainBodyDef, progName, progDef, linkB } =
  let
    fun TM s = Term (QS s)
    fun stl s = "(strlit \"" ^ s ^ "\")"
    fun traceOf sv =
      sv ^ ".ffi.io_events ++ loadEv ++\n" ^
      "  [IO_event (ffi$ExtCall " ^ stl "report_vec" ^ ")\n" ^
      "     (word_to_bytes (" ^ specWord ^ " : word64) F) rb]"
    val ffiApp = ffiName ^ " " ^ ffiArgs
    (* -- 1. MainRefine (the hard part) -- *)
    val mainRefine = mk_mainRefine
      { prefix=prefix, ffiName=ffiName, ffiDef=ffiDef, ffiArgs=ffiArgs,
        ctrlName=ctrlName, ctrlStagedDef=ctrlStagedDef, relName=relName, relDef=relDef,
        reads=reads, bufOff=bufOff, koff=koff, boundsStr=boundsStr, specWord=specWord,
        coreName=coreName, coreFramed=coreFramed, coreNoFFI=coreNoFFI,
        mainBodyName=mainBodyName, mainBodyDef=mainBodyDef }

    (* -- 2. Sem: call_main_run + main_semantics -- *)
    val callMainRun = prove (
      TM (
        "FLOOKUP (s'':(64,'ffi)panSem$state).code " ^ stl "main" ^ " = SOME ([], " ^ mainBodyName ^ ") /\\ " ^
        "s''.clock <> 0 /\\ " ^ ffiApp ^ " ((dec_clock s'') with locals := FEMPTY) ==> " ^
        "?t loadEv rb. evaluate (Call NONE " ^ stl "main" ^ " [], s'') = (SOME (Return (ValWord 0w)), t) /\\ " ^
        "t.ffi.io_events = " ^ traceOf "s''"),
      strip_tac >>
      qabbrev_tac (QS "s0 = (dec_clock s'') with locals := FEMPTY") >>
      (QS ("s0.locals = FEMPTY /\\ " ^ ffiApp ^ " s0 /\\ s0.ffi = s''.ffi")) by
         (fs [ABB "s0", dec_clock_def]) >>
      drule_all mainRefine >> strip_tac >>
      qmatch_asmsub_rename_tac
         (QS ("evaluate (" ^ mainBodyName ^ ", s0) = (SOME (Return (ValWord 0w)), sF)")) >>
      (QS "sF.clock <= s0.clock") by (imp_res_tac evaluate_clock >> fs []) >>
      (QS ("evaluate (" ^ mainBodyName ^ ", dec_clock s'' with locals := FEMPTY) = (SOME (Return (ValWord 0w)), sF)"))
         by (fs [ABB "s0"]) >>
      map_every (fn q => qexists_tac (QS q)) ["empty_locals sF", "loadEv", "rb"] >>
      conj_tac
      >- (simp [Once evaluate_def, OPT_MMAP_def] >>
          gvs [lookup_code_def, FUPDATE_LIST_THM]) >>
      fs [empty_locals_def])
    val _ = save_thm (prefix ^ "_call_main_run", callMainRun)

    val mainSemantics = prove (
      TM (
        "FLOOKUP (s':(64,'ffi)panSem$state).code " ^ stl "main" ^ " = SOME ([], " ^ mainBodyName ^ ") /\\ " ^
        "(!K. " ^ ffiApp ^ " ((dec_clock (s' with clock := K)) with locals := FEMPTY)) ==> " ^
        "?loadEv rb. semantics s' " ^ stl "main" ^ " = Terminate Success (" ^ traceOf "s'" ^ ")"),
      strip_tac >>
      qabbrev_tac (QS "sc = s' with clock := 1") >>
      (QS "sc.code = s'.code /\\ sc.ffi = s'.ffi /\\ sc.clock = 1") by (simp [ABB "sc"]) >>
      (QS ("FLOOKUP sc.code " ^ stl "main" ^ " = SOME ([], " ^ mainBodyName ^ ")")) by (fs []) >>
      (QS "sc.clock <> 0") by (fs []) >>
      (QS (ffiApp ^ " ((dec_clock sc) with locals := FEMPTY)")) by
         (first_x_assum (qspec_then (QS "1") mp_tac) >> simp [ABB "sc"]) >>
      drule_all callMainRun >> strip_tac >>
      qexists_tac (QS "loadEv") >> qexists_tac (QS "rb") >>
      (QS ("evaluate (Call NONE " ^ stl "main" ^ " [], s' with clock := 1) = (SOME (Return (ValWord 0w)), t)"))
         by (fs [ABB "sc"]) >>
      drule semantics_Return_lift >> strip_tac >>
      (QS ("t.ffi.io_events = " ^ traceOf "s'")) by
         (qpat_x_assum (QS "t.ffi.io_events = _") mp_tac >> simp [ABB "sc"]) >>
      simp [])
    val _ = save_thm (prefix ^ "_main_semantics", mainSemantics)

    (* -- 3. Install: whole-program Link A at the decls level -- *)
    val decs_ev = (REWRITE_CONV [progDef] THENC EVAL) (TM ("decs_stcnames [] " ^ progName))
    val evd_ev  = (REWRITE_CONV [progDef] THENC EVAL)
                    (TM ("evaluate_decls ((s:(64,'ffi) panSem$state) with structs := []) " ^ progName))
    val semanticsDecls = prove (
      TM (
        "(s:(64,'ffi) panSem$state).code = FEMPTY /\\ " ^ ffiApp ^ " s ==> " ^
        "?loadEv rb. semantics_decls s " ^ stl "main" ^ " " ^ progName ^ " = Terminate Success (" ^
        traceOf "s" ^ ")"),
      strip_tac >>
      qabbrev_tac (QS ("s' = THE (evaluate_decls (s with structs := []) " ^ progName ^ ")")) >>
      (QS ("semantics_decls s " ^ stl "main" ^ " " ^ progName ^ " = semantics s' " ^ stl "main"))
         by (simp [semantics_decls_def, decs_ev, evd_ev, ABB "s'"]) >>
      (QS ("FLOOKUP s'.code " ^ stl "main" ^ " = SOME ([], " ^ mainBodyName ^ ")"))
         by (simp [ABB "s'"] >> REWRITE_TAC [progDef] >> EVAL_TAC >>
             REWRITE_TAC [mainBodyDef, coreDef]) >>
      (QS "s'.base_addr = s.base_addr /\\ s'.ffi = s.ffi")
         by (simp [ABB "s'"] >> REWRITE_TAC [progDef] >> EVAL_TAC) >>
      (QS ("!Kc. " ^ ffiApp ^ " ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)"))
         by (gen_tac >> qpat_x_assum (QS (ffiApp ^ " s")) mp_tac >>
             asm_simp_tac (srw_ss()) [ffiDef, dec_clock_def]) >>
      (QS ("?loadEv rb. semantics s' " ^ stl "main" ^ " = Terminate Success (" ^ traceOf "s'" ^ ")"))
         by (irule mainSemantics >> rpt conj_tac >>
             (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
      qexists_tac (QS "loadEv") >> qexists_tac (QS "rb") >> gvs [])
    val _ = save_thm (prefix ^ "Prog_semantics_decls", semanticsDecls)

    (* -- 4. EndToEnd: compose with Link B -- *)
    val linkB_ant   = linkB |> concl |> dest_imp |> #1
    val linkB_concl = linkB |> concl |> dest_imp |> #2
    val sd_tm = find_term (fn t => same_const (fst (strip_comb t)) “semantics_decls”
                           handle _ => false) linkB_concl
    val notFail_tm = valOf (List.find (fn c => is_neg c andalso
        (let val e = dest_neg c in is_eq e andalso
           (same_const (fst (strip_comb (lhs e))) “semantics_decls” handle _ => false) end))
        (boolSyntax.strip_conj linkB_ant))
    val pkg_tm = list_mk_conj (filter (fn c => not (aconv c notFail_tm))
                                 (boolSyntax.strip_conj linkB_ant))
    val trace_tm = TM (traceOf "(s:(64,'ffi) panSem$state)")
    val subset_sd   = linkB_concl
    val subset_spec = subst [sd_tm |-> Term [QUOTE "Terminate Success ", ANTIQUOTE trace_tm]] linkB_concl
    val e2e_goal =
      mk_imp (list_mk_conj [pkg_tm, TM (ffiApp ^ " (s:(64,'ffi) panSem$state)")],
              mk_exists (TM "loadEv:io_event list",
                mk_exists (TM "rb:(word8 # word8) list", subset_spec)))
    val machineCode = prove (e2e_goal,
      strip_tac >>
      (([QUOTE "?loadEv rb. ", ANTIQUOTE sd_tm, QUOTE " = Terminate Success ", ANTIQUOTE trace_tm])
         by (irule semanticsDecls >> rpt conj_tac >>
             (first_assum ACCEPT_TAC ORELSE metis_tac []))) >>
      qexists_tac (QS "loadEv") >> qexists_tac (QS "rb") >>
      (([ANTIQUOTE notFail_tm]) by
         (qpat_x_assum ([QUOTE "", ANTIQUOTE sd_tm, QUOTE " = _"]) (fn th => simp [th]))) >>
      (([ANTIQUOTE subset_sd]) by
         (match_mp_tac linkB >> rpt conj_tac >>
          (first_assum ACCEPT_TAC ORELSE metis_tac []))) >>
      qpat_x_assum ([QUOTE "", ANTIQUOTE sd_tm, QUOTE " = _"]) (fn th => gvs [th]))
    val _ = save_thm (prefix ^ "_machine_code", machineCode)
  in
    { mainRefine = mainRefine, callMainRun = callMainRun, mainSemantics = mainSemantics,
      semanticsDecls = semanticsDecls, machineCode = machineCode }
  end;

end
