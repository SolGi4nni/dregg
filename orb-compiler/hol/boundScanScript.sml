(* C0 probe — HOL4 transcription of the Lean SPEC C0.boundScan, plus
   kernel-checked EVAL of the reference vectors. This is P2's behavioral
   round-trip (§1, layer 3) applied to THIS primitive: a HOL4 kernel
   computation of the same function on the same vectors, to sit beside the
   Lean model output and the compiled-Pancake machine output. Three
   independent kernels, one digest per vector.

   Bytes and accumulators are modelled as `num`; the mask 16777216 = 2^24 and
   the multiplier 31 are literal-for-literal the Pancake `& 16777215` / `* 31`
   and the Lean `&&& 0xFFFFFF` / `* 31`. (num MOD 2^24 = the low 24 bits, and
   every intermediate is < 2^24, so num/UInt32/word64 all agree here — the
   convention seam of P2 §4.2 does not bite because there is no division and no
   negative value on the path.) *)

open HolKernel boolLib bossLib listTheory arithmeticTheory;

val _ = new_theory "boundScan";

Definition step_def:
  step acc b = (acc * 31 + b) MOD 16777216
End

Definition scanFrom_def:
  (scanFrom a off 0 acc = acc) /\
  (scanFrom a off (SUC n) acc = scanFrom a (off + 1) n (step acc (EL off a)))
End

Definition boundScan_def:
  boundScan a off len =
    if off + len <= LENGTH a then SOME (scanFrom a off len 0) else NONE
End

(* "GET / HTTP/1.1\r\n" — byte-identical to C0.arena. *)
Definition arena_def:
  arena = [71;69;84;32;47;32;72;84;84;80;47;49;46;49;13;10]
End

(* The vectors, EVAL'd. Each theorem is kernel-checked; a wrong transcription
   fails to prove by EVAL/rfl (the P2 acceptance gate). *)
Theorem vec_0_16:
  boundScan arena 0 16 = SOME 14695237
Proof
  EVAL_TAC
QED

Theorem vec_0_3:
  boundScan arena 0 3 = SOME 70454
Proof
  EVAL_TAC
QED

Theorem vec_4_10:
  boundScan arena 4 10 = SOME 12467326
Proof
  EVAL_TAC
QED

Theorem vec_14_2:
  boundScan arena 14 2 = SOME 413
Proof
  EVAL_TAC
QED

Theorem vec_0_17:
  boundScan arena 0 17 = NONE
Proof
  EVAL_TAC
QED

Theorem vec_16_1:
  boundScan arena 16 1 = NONE
Proof
  EVAL_TAC
QED

Theorem vec_10_8:
  boundScan arena 10 8 = NONE
Proof
  EVAL_TAC
QED

Theorem vec_16_0:
  boundScan arena 16 0 = SOME 0
Proof
  EVAL_TAC
QED

val _ = export_theory ();
