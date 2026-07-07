open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
val _ = new_theory "tst";

Theorem signed_lt_n2w64:
  !x y. x < 2n ** 63 /\ y < 2n ** 63 ==>
        (((n2w x):word64) < n2w y <=> x < y)
Proof
  rw [] >>
  `(2:num) ** 63 < 2 ** 64` by EVAL_TAC >>
  `x < dimword(:64) /\ y < dimword(:64)` by
    (`dimword(:64) = 2 ** 64` by EVAL_TAC >> fs [] >>
     conj_tac >> metis_tac [LESS_TRANS]) >>
  `~word_msb ((n2w x):word64) /\ ~word_msb ((n2w y):word64)` by
    (rw [word_msb_n2w] >> irule NOT_BIT_GT_TWOEXP >> fs []) >>
  rw [WORD_LT, w2n_n2w] >> fs []
QED

Theorem eval_lt_pinned:
  FLOOKUP s.locals v = SOME (ValWord (n2w x)) /\
  x < 9223372036854775808 /\ y < 9223372036854775808 ==>
  eval s (Cmp Less (Var Local v) (Const (n2w y))) =
    SOME (ValWord (if x < y then 1w else 0w))
Proof
  strip_tac >>
  `(2:num) ** 63 = 9223372036854775808` by EVAL_TAC >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        asmTheory.word_cmp_def] >>
  `((n2w x):word64 < n2w y) = (x < y)`
     by (irule signed_lt_n2w64 >> fs []) >>
  (fn (asl,g) =>
     let val heq = hd asl
         val hl = lhs heq
         val gcond = g |> lhs |> dest_cond |> #1
         val _ = print ("\n@@ACONV=" ^ Bool.toString (aconv hl gcond) ^ "@@\n")
         val _ = print ("@@HLTY=" ^ Parse.type_to_string (type_of hl) ^ " GCTY=" ^ Parse.type_to_string (type_of gcond) ^ "@@\n")
         val _ = print ("@@HL=" ^ Parse.term_to_string hl ^ " GC=" ^ Parse.term_to_string gcond ^ "@@\n")
         fun opinfo t = let val (c,_) = strip_comb t in
             (let val {Name,Thy,...} = dest_thy_const c in Thy^"$"^Name end
              handle _ => ("nonconst:"^term_to_string c)) end
         val _ = print ("@@HLOP=" ^ opinfo hl ^ " GCOP=" ^ opinfo gcond ^ "@@\n")
         val ha = hl |> rator |> rand   val ga = gcond |> rator |> rand
         val _ = print ("@@HA=" ^ Parse.term_to_string ha ^ ":" ^ Parse.type_to_string (type_of ha) ^ " GA=" ^ Parse.term_to_string ga ^ ":" ^ Parse.type_to_string (type_of ga) ^ " ACONV=" ^ Bool.toString (aconv ha ga) ^ "@@\n")
     in ALL_TAC (asl,g) end) >>
  first_x_assum (fn th => SUBST1_TAC th ORELSE ALL_TAC) >>
  REWRITE_TAC []
QED

val _ = export_theory ();
