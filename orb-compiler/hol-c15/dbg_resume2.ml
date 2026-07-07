val _ = Globals.show_types := true;
val heq = ASSUME “((n2w (x:num)):word64 < n2w (y:num)) <=> (x < y)”;
val _ = print "\n@@HEQ@@\n"; val _ = print (thm_to_string heq);
val subg = “(if (n2w (x:num)):word64 < n2w (y:num) then (1w:word64) else 0w) = if x < y then 1w else 0w”;
val r = (SIMP_CONV bool_ss [heq] subg) handle _ => (print "\n@@bool_ss heq FAIL@@\n"; REFL subg);
val _ = print "\n@@R@@\n"; val _ = print (thm_to_string r); val _ = print "\n@@END@@\n";
