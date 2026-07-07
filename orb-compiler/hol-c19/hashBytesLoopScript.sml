(* ===========================================================================
   C19 probe — FIRST REAL serve FOLD closes its loop core through the C16
   fold-loop schema.

   The fold is the DEPLOYED cache-key hash, drorb `Reactor/Stage/Cache.lean:115`:

       def hashBytes (b : Bytes) : Nat := b.foldl (fun a x => a * 257 + x.toNat + 1) 0

   used by `keyOf` (`Cache.lean:118`, `{ method := hashBytes c.req.method,
   uri := hashBytes c.req.target, .. }`) which the `cacheEmptyStage` (stage 4 of
   `Reactor.Deploy.deployStagesFull2`) runs on EVERY request to compute the cache
   key.  It is a genuine running-word-accumulator `FOLDL` over a byte array — the
   fold-loop schema's exact target — but with a MULTIPLY-ADD step (`a*257 + b + 1`),
   not the toy byte-sum's plain `+`, and a **Nat** accumulator (the Lean spec is
   over `Nat`; the machine register is `word64`).

   Result: the emitted `While` closes to `FOLDL hashAcc 0w (MAP n2w input)` from a
   ~8-line per-step fill-in via `foldLoop_refines` (identical route to C16's
   byte-sum, just a richer accf), and the Nat→word homomorphism `hashBytes_word`
   connects that word fold to `n2w (hashBytesN input)` — the deployed serve fold's
   result modulo 2^64 (exactly what leanc's fixed-width codegen computes).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory;
open panLangTheory panSemTheory;
open foldLoopSchemaTheory;   (* foldInv, foldLoop_refines, eval_foldByte, ... *)

val _ = new_theory "hashBytesLoop";

(* ---- the Lean SPEC, re-declared over nats (byte-identical to Cache.hashBytes,
   List.foldl (fun a x => a*257 + x + 1) 0) ---- *)
Definition hashAccN_def:
  hashAccN (a:num) (b:num) = a * 257 + b + 1
End

Definition hashBytesN_def:
  hashBytesN (input:num list) = FOLDL hashAccN 0 input
End

(* ---- the machine-word accumulator step (word64, wraps at 2^64) ---- *)
Definition hashAcc_def:
  hashAcc (a:word64) (b:word64) = a * 257w + b + 1w
End

(* ===========================================================================
   THE Nat -> word HOMOMORPHISM.  n2w is a semiring hom, so the whole Nat fold
   maps onto the word fold: this is what makes the word-level schema result the
   FAITHFUL statement of the deployed (fixed-width) hash.  The one real "non-word
   accumulator" friction, closed once by list induction.
   =========================================================================== *)
Theorem hashAccN_word:
  !a b. (n2w (hashAccN a b) : word64) = hashAcc (n2w a) (n2w b)
Proof
  rw [hashAccN_def, hashAcc_def] >>
  `(257w:word64) = n2w 257` by EVAL_TAC >>
  simp [word_add_n2w, word_mul_n2w] >> simp [GSYM word_add_n2w, GSYM word_mul_n2w]
QED

Theorem hashBytes_word_gen:
  !input a.
    (n2w (FOLDL hashAccN a input) : word64) =
    FOLDL hashAcc (n2w a) (MAP (\c. (n2w c):word64) input)
Proof
  Induct >> rw [] >> simp [hashAccN_word]
QED

Theorem hashBytes_word:
  !input.
    (n2w (hashBytesN input) : word64) =
    FOLDL hashAcc 0w (MAP (\c. (n2w c):word64) input)
Proof
  rw [hashBytesN_def] >>
  `(0w:word64) = n2w 0` by simp [] >>
  metis_tac [hashBytes_word_gen]
QED

(* ===========================================================================
   THE EMITTED BODY — the `a*257 + b + 1` mul-add fold body, in the exact
   emitted style of C13's verified-parser digest body (Annot-wrapped `Assign`s,
   `Panop Mul` for `*`, `Op Add` for `+`, a `LoadByte (base+i)` byte read).
   =========================================================================== *)
Definition hashBody_def:
  hashBody =
    Seq (Assign Local «b» (LoadByte (Op Add [Var Local «base»; Var Local «i»])))
   (Seq (Assign Local «acc»
           (Op Add [Panop Mul [Var Local «acc»; Const 257w];
                    Var Local «b»; Const 1w]))
        (Assign Local «i» (Op Add [Var Local «i»; Const 1w])))
End

(* ---- eval of the emitted mul-add expression = hashAcc acc byte ---- *)
Theorem eval_hashUpdate:
  FLOOKUP s.locals «acc» = SOME (ValWord acc) /\
  FLOOKUP s.locals «b»   = SOME (ValWord bw) ==>
    eval s (Op Add [Panop Mul [Var Local «acc»; Const 257w];
                    Var Local «b»; Const 1w])
      = SOME (ValWord (hashAcc acc bw))
Proof
  strip_tac >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, pan_op_def,
        hashAcc_def, WORD_ADD_ASSOC]
QED

(* ---- THE per-step fill-in : one iteration advances the fold by `hashAcc`.
   Same shape (and length) as C16's byte-sum `sumBody_step` — read byte, run the
   emitted `acc*257 + byte + 1` update, bump `i`, re-establish `foldInv` — the
   ONLY extra work over the byte-sum being `pan_op_def`/`word_mul_n2w` for the
   `Panop Mul`.  ~8 bespoke tactic lines (vs boundScan's 629). ---- *)
Theorem hashBody_step:
  !i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
    ?s2. evaluate (hashBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         foldInv input bs (i+1) (hashAcc acc (n2w (EL i input):word64)) s2
Proof
  rpt strip_tac >>
  `FLOOKUP s.locals «base» = SOME (ValWord bs) /\
   FLOOKUP s.locals «i»    = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals «acc»  = SOME (ValWord acc) /\
   FLOOKUP s.locals «len»  = SOME (ValWord (n2w (LENGTH input)))` by fs [foldInv_def] >>
  `?bb. FLOOKUP s.locals «b» = SOME (ValWord bb)` by fs [foldInv_def] >>
  `eval s (LoadByte (Op Add [Var Local «base»; Var Local «i»])) =
     SOME (ValWord (n2w (EL i input):word64))` by (drule_all eval_foldByte >> simp []) >>
  qexists_tac `set_var «i» (ValWord (n2w i + 1w))
    (set_var «acc» (ValWord (acc * 257w + n2w (EL i input) + 1w))
    (set_var «b»   (ValWord (n2w (EL i input))) s))` >>
  simp [hashBody_def, evaluate_def, eval_def, is_valid_value_simps, shape_of_def,
        set_var_def, FLOOKUP_UPDATE, wordLangTheory.word_op_def, pan_op_def,
        word_mul_n2w, OPT_MMAP_def] >>
  simp [foldInv_def, hashAcc_def, memRel_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  fs [foldInv_def, memRel_def]
QED

(* ===========================================================================
   THE CLOSED loop core : the emitted cache-key-hash `While` computes EXACTLY the
   deployed Lean fold `hashBytes input` (mod 2^64) over the whole byte array,
   discharging the schema's single obligation with `hashBody_step` and rewriting
   the word fold back to `n2w (hashBytesN input)` via the homomorphism.
   =========================================================================== *)
Theorem hashLoop_refines:
  !input bs (s:(64,'ffi) state).
    foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
    ?s'. evaluate (While foldGuard hashBody, s) = (NONE, s') /\
         FLOOKUP s'.locals «acc» =
           SOME (ValWord ((n2w (hashBytesN input)):word64))
Proof
  rpt strip_tac >>
  `!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
     ?s2. evaluate (hashBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
          foldInv input bs (i+1) (hashAcc acc (n2w (EL i input):word64)) s2`
     by (rpt strip_tac >> irule hashBody_step >> fs []) >>
  drule foldLoop_refines >>
  disch_then (qspecl_then [`0w`,`s`] mp_tac) >>
  impl_tac >- fs [] >> strip_tac >>
  qexists_tac `s'` >> simp [hashBytes_word]
QED

val _ = export_theory ();
