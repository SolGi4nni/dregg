val relDef = statusRel_def;
val _ = print ("\n@@CONCL@@ " ^ term_to_string (concl relDef) ^ "\n");
val (_, body) = strip_forall (concl relDef);
val relRHS = rhs body;
val relConjs = boolSyntax.strip_conj relRHS;
val nvmap = List.mapPartial (fn c =>
    (let val (l,r) = dest_eq c val v = rand l val nv = r |> rand |> rand |> rand in SOME (nv, v) end) handle _ => NONE) relConjs;
val _ = print ("@@NVMAP@@ " ^ String.concatWith " ; " (map (fn (nv,v) => term_to_string nv ^ "->" ^ term_to_string v) nvmap) ^ "\n");
val gp = “code < 200n”;
val (x,y) = numSyntax.dest_less gp;
val _ = print ("@@X@@ " ^ term_to_string x ^ " @@Y@@ " ^ term_to_string y ^ "\n");
val found = List.find (fn (nv,_) => aconv nv x) nvmap;
val _ = print ("@@FOUND@@ " ^ (case found of NONE => "NONE" | SOME (_,v) => term_to_string v) ^ "\n");
val _ = TextIO.flushOut TextIO.stdOut;
