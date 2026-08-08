/-
# Dregg2.Bridge.PicklesWrapShapeGate — the RUNTIME-CALLABLE per-block **Pickles Wrap-proof**
preamble gate, `@[export] dregg_mina_wrap_shape_ok`, whose decision IS
`KimchiVerify.shapeOkRec` — the check `verifier.rs:810-830` runs before a Kimchi verify does
anything else.

## Why this module exists

`bridge/src/mina_observer.rs` fed the Mina light-client gate a compile-time constant for its
Pickles conjunct — `NEUTRAL_PICKLES_OK = true` — because `bestChain` did not fetch
`protocolStateProof` and nothing deployed could look at a Wrap proof. Meanwhile this tree
already had `shapeOkRec` running on a REAL Mina devnet block
(`Circuit.Emit.MinaRealBlockGate.real_block_shape_accepts`, on block 539508, whose Wrap proof
o1-labs' own `kimchi::verifier::verify` accepts) — and **nothing called it**. This module is the
`@[export]` that ends that: the observer decodes each block's `Mina_base.Proof.Stable.V2` in
Rust (a CODEC — `bridge/src/mina_pickles.rs`) and the ARCHIVE renders the decision.

## EXPORTED + PROVEN vs TRUSTED — say it plainly

  * EXPORTED + PROVEN (this gate): the proof's recursion count equals the VERIFIER INDEX's
    (`verifier.rs:810-813`, `VerifyError::IncorrectPrevChallengesLength`); ⚑ since 2026-08-08
    the public-input length `to_public_input` PRODUCES equals the index's declared `public`
    (`verifier.rs:816-820` — this line used to read "the public input is non-empty", which was
    the whole of the check and could not fail on this path); the step domain is within
    `BACKEND_TICK_ROUNDS_N`; no `prev_evals` vector is chunked, over a non-empty walk; there
    are `COLUMNS = 15` witness commitments and coefficient columns and
    `PERMUTS - 1 = 6` σ evaluations; `chunk_size = 1`; `t_comm` is within `7 · chunk_size`; the
    exhibited accumulator COMMITMENTS and challenge VECTORS agree in count; and the IPA round
    count is the index's `log₂ max_poly_size`. Pure `Nat`/`Bool`, no crypto — and exactly the
    rules-bug locus that the `prevLen = 0` freeze got wrong.
  * TRUSTED, and it is most of a verifier: the index parameters themselves. `idxPrev`,
    `publicLen`, `chunkSize` and `idxRounds` come from the observer's pinned
    `MinaWrapIndexParams`, not from the chain. Modelling the Wrap VK is P8/P9 and is NOT
    STARTED (`docs/MINA-REAL-BLOCK-GATE.md` §6). This gate says the proof has the shape the
    pinned index demands; it does not say the index is Mina's.
  * NOT HERE AT ALL: the arithmetic. C3/C5/C8, the group assembly and the IPA opening relation
    are `MinaRealBlockGate` / `MinaRealBlockTranscript` / `MinaWrap*`, and they are `by decide`
    over the literal constants of ONE extracted block. They are not functions of a proof and
    cannot be evaluated on a live one — see the header of `bridge/src/mina_observer.rs` for the
    measured reason.

## Scope (honest, current resolution)

An accept here means the proof's PREAMBLE passes. It says nothing about whether the proof
verifies: `shapeOkRec` is the first seven lines of `to_batch`, and everything expensive comes
after. Routing the observer through this export replaces a constant that meant nothing with a
verdict that means the preamble — and makes an absent archive a REFUSAL rather than a silent
`true`.
-/
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PicklesVerifyPreamble

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Dregg2.Bridge.PicklesWrapShapeGate

open Dregg2.Circuit.Emit.KimchiVerify (shapeOk shapeOkRec COLUMNS PERMUTS)
open Dregg2.Circuit.Emit.PicklesVerifyPreamble
  (publicInputLenOk toPublicInputLen stepDomainOk nonChunking maxPairLen
   maxPairLen_le_one_iff_nonChunking BACKEND_TICK_ROUNDS_N)

/-! ## §1 — THE DECISION.

⚑ **EXTENDED 2026-08-08 with four upstream legs this gate did not have.** The audit that
produced `Circuit.Emit.PicklesVerifyPreamble` found that `shapeOkRec`'s public-input conjunct is
`decide (0 < publicLen)` while the line it cites (`verifier.rs:816-820`) is an EQUALITY between
the length `to_public_input` produced and the length the index declares. On this path `publicLen`
arrives from `mina_pickles::MinaWrapIndexParams`, i.e. TRUSTED CONFIG — so the conjunct compared a
constant against zero and **could not fail**. `the_old_gate_admits_a_public_input_it_should_refuse`
exhibits the accept it let through. -/

/-- **`preambleLegsOk`** — the four legs added on 2026-08-08, each transcribed in
`Circuit.Emit.PicklesVerifyPreamble` from `mina-rust @ 82480cd46`.

  * **D1b + C3.** `publicInputLenOk (toPublicInputLen nChal) publicLen` — the packing schedule of
    `prepared_statement.rs:100-176` produces `24 + nChal` words and `:179` asserts that equals
    `npublic_input`; `verifier.rs:816-820` re-checks the same equality as a returned error. The
    produced length is COMPUTED from the wire's challenge count, never supplied beside it.
  * **B3.** `stepDomainOk branchDomainLog2` — `verification.rs:648-651`, `domain_log2 ≤ 16`.
    `branch_domain_log2` was already decoded (`mina_pickles.rs:640`) and fed nothing.
  * **B1.** `0 < prevEvalPairs` and `prevEvalMaxLen ≤ 1` — `verification.rs:628`. The second is
    the wire summary of the list predicate, and `maxPairLen_le_one_iff_nonChunking` proves the
    summary decides EXACTLY what the list decides. The first refuses an empty walk, which
    `nonChunking_nil` shows would otherwise be a vacuous accept. -/
def preambleLegsOk (nChal publicLen branchDomainLog2 prevEvalPairs prevEvalMaxLen : Nat) : Bool :=
  publicInputLenOk (toPublicInputLen nChal) publicLen
  && stepDomainOk branchDomainLog2
  && decide (0 < prevEvalPairs)
  && decide (prevEvalMaxLen ≤ 1)

/-- **`picklesWrapShapeOk`** — `shapeOkRec`, the two length agreements a RECURSIVE Wrap
proof owes that a single-proof index does not, and `preambleLegsOk`.

  * `proofPrevVecs = proofPrev`: `messages_for_next_step_proof` exhibits one accumulator
    COMMITMENT and one 16-challenge VECTOR per carried proof. A proof showing commitments
    without their challenge vectors (or the reverse) is malformed, and the fold that consumes
    them (`prevChalFoldOk`) would be reading a list of a different length.
  * `proofRounds = idxRounds`: `bulletproof.lr.len()` is the IPA round count `k`, which is
    `log₂ max_poly_size` of the index (`kimchi_pasta_basic.ml:16-17`, `SideShape.rounds = 15`
    on the Wrap side). A short `lr` is a proof over a smaller SRS. -/
def picklesWrapShapeOk
    (idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen tCommLen chunkSize
      idxRounds proofRounds nChal branchDomainLog2 prevEvalPairs prevEvalMaxLen : Nat) : Bool :=
  shapeOkRec idxPrev proofPrev publicLen wLen sLen coeffLen tCommLen chunkSize
  && decide (proofPrevVecs = proofPrev)
  && decide (proofRounds = idxRounds)
  && preambleLegsOk nChal publicLen branchDomainLog2 prevEvalPairs prevEvalMaxLen

/-- **`the_old_gate_shape`** — the decision EXACTLY as it shipped until 2026-08-08, kept only so
the theorem below can state what it admitted. It is not called by anything. -/
def the_old_gate_shape
    (idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen tCommLen chunkSize
      idxRounds proofRounds : Nat) : Bool :=
  shapeOkRec idxPrev proofPrev publicLen wLen sLen coeffLen tCommLen chunkSize
  && decide (proofPrevVecs = proofPrev)
  && decide (proofRounds = idxRounds)

/-- **THE REFINEMENT TIE.** The gate's decision is DEFINITIONALLY `shapeOkRec` conjoined with
the two length agreements — so gating the observer on this export gates it on the upstream
preamble check, not on a paraphrase of it. -/
theorem picklesWrapShapeOk_is_shapeOkRec
    (idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen tCommLen chunkSize
      idxRounds proofRounds nChal branchDomainLog2 prevEvalPairs prevEvalMaxLen : Nat) :
    picklesWrapShapeOk idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen tCommLen
        chunkSize idxRounds proofRounds nChal branchDomainLog2 prevEvalPairs prevEvalMaxLen
      = (shapeOkRec idxPrev proofPrev publicLen wLen sLen coeffLen tCommLen chunkSize
         && decide (proofPrevVecs = proofPrev)
         && decide (proofRounds = idxRounds)
         && preambleLegsOk nChal publicLen branchDomainLog2 prevEvalPairs prevEvalMaxLen) := rfl

/-- **THE PAYOFF DIRECTION.** An accept ENTAILS the upstream shape check accepts. (The converse
is deliberately false: `shapeOkRec` alone does not look at `lr` or at the accumulator vectors.) -/
theorem picklesWrapShapeOk_imp_shapeOkRec
    {idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen tCommLen chunkSize
      idxRounds proofRounds nChal branchDomainLog2 prevEvalPairs prevEvalMaxLen : Nat}
    (h : picklesWrapShapeOk idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen
          tCommLen chunkSize idxRounds proofRounds nChal branchDomainLog2 prevEvalPairs
          prevEvalMaxLen = true) :
    shapeOkRec idxPrev proofPrev publicLen wLen sLen coeffLen tCommLen chunkSize = true := by
  unfold picklesWrapShapeOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

/-- ⚑⚑ **THE NEW PAYOFF DIRECTION — an accept now ENTAILS the upstream public-input equality.**
`verifier.rs:816-820` compares the length `to_public_input` produced against the index's `public`,
and this is that comparison. It is the leg the gate did not have. -/
theorem picklesWrapShapeOk_imp_publicInputLen
    {idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen tCommLen chunkSize
      idxRounds proofRounds nChal branchDomainLog2 prevEvalPairs prevEvalMaxLen : Nat}
    (h : picklesWrapShapeOk idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen
          tCommLen chunkSize idxRounds proofRounds nChal branchDomainLog2 prevEvalPairs
          prevEvalMaxLen = true) :
    toPublicInputLen nChal = publicLen := by
  unfold picklesWrapShapeOk preambleLegsOk publicInputLenOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1.1.1

/-- ⚑⚑ **`picklesWrapShapeOk_imp_nonChunking`** — and an accept ENTAILS upstream's B1 over the
ACTUAL list of evaluation lengths, not over the summary the wire carries. This is what makes the
summary a reduction: the hypothesis is about the wire number, the conclusion is about
`verification.rs:628`'s universal. -/
theorem picklesWrapShapeOk_imp_nonChunking
    {idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen tCommLen chunkSize
      idxRounds proofRounds nChal branchDomainLog2 prevEvalPairs : Nat}
    {evalLens : List (Nat × Nat)}
    (h : picklesWrapShapeOk idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen
          tCommLen chunkSize idxRounds proofRounds nChal branchDomainLog2 prevEvalPairs
          (maxPairLen evalLens) = true) :
    nonChunking evalLens = true := by
  unfold picklesWrapShapeOk preambleLegsOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact (maxPairLen_le_one_iff_nonChunking evalLens).mp h.2.2

/-! ## §2 — THE REAL MINA DEVNET BLOCK. Same counts `MinaRealBlockGate` names on block 539508,
restated here so this gate's accept is anchored to a real object rather than to a plausible
tuple. The Rust decoder reads all five PROOF-side numbers straight out of the block's
`protocolStateProof` (`bridge/src/mina_pickles.rs`, `real_devnet_block_proof_decodes_to_the_pinned_shape`);
the four INDEX-side numbers are pinned config. -/

/-- `verifier_index.prev_challenges` of the devnet blockchain VK. -/
def IDX_PREV : Nat := 2
/-- `verifier_index.public`. -/
def PUBLIC : Nat := 40
/-- `k = log₂ max_poly_size = log₂ 2^15`. -/
def ROUNDS : Nat := 15
/-- `proof.prev_challenges.len()` on the real block. -/
def PREV : Nat := 2
/-- `bulletproof.lr.len()` on the real block. -/
def LR : Nat := 15
/-- `deferred_values.bulletproof_challenges.len()` — `BACKEND_TICK_ROUNDS_N`, and the number
`to_public_input`'s schedule needs to reach `PUBLIC`. -/
def NCHAL : Nat := 16
/-- `branch_data.domain_log2` on the real block — the STEP side's, hence `16` and not the Wrap
VK's own `14`. -/
def BRANCH_DOMAIN_LOG2 : Nat := 16
/-- Pairs the `prev_evals` walk yields on a no-lookup index: 15 `w` + 15 `coefficients` + `z` +
6 `s` + 6 unconditional selectors. Every optional evaluation is `None` and yields nothing
(`mina_pickles.rs:710-758`). -/
def PREV_EVAL_PAIRS : Nat := 43
/-- The largest `prev_evals` vector length on the real block — single-chunk, so `1`. -/
def PREV_EVAL_MAXLEN : Nat := 1

/-- ⚑ **`the_packing_reaches_the_index_public_count`** — `PUBLIC` is not an independent constant
next to `NCHAL`: it is what `to_public_input`'s schedule PRODUCES at `NCHAL`, and `NCHAL` is
`BACKEND_TICK_ROUNDS_N`. Stated so a future edit cannot move one without reddening the other. -/
theorem the_packing_reaches_the_index_public_count :
    toPublicInputLen NCHAL = PUBLIC ∧ NCHAL = BACKEND_TICK_ROUNDS_N := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`real_block_wrap_shape_accepts`** — the REAL devnet block 539508's decoded Wrap shape is
ACCEPTED, now including the four legs added on 2026-08-08. -/
theorem real_block_wrap_shape_accepts :
    picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN
      = true := by decide

/-- ⚑ **`real_block_wrap_shape_refused_by_freeze`** — and the retired `prevLen = 0` freeze
REFUSES it. This is the whole reason the Pickles conjunct could not simply be wired to the old
`shapeOk`: that predicate rejects Mina. -/
theorem real_block_wrap_shape_refused_by_freeze :
    picklesWrapShapeOk 0 PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    ∧ shapeOk PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑⚑⚑ **`the_old_gate_admits_a_public_input_it_should_refuse`** — THE WOUND, exhibited.

An index declaring **41** public inputs against a proof whose packing produces **40** is
`VerifyError::IncorrectPubicInputLength` upstream (`verifier.rs:816-820`). The gate that shipped
until 2026-08-08 **ACCEPTS** it, because its only public-input conjunct is `0 < publicLen`.

⚑ And the pair is not hypothetical: `MinaWrapVkDigestChain.the_index_digest_cannot_see_the_circuit_shape`
proves kimchi's index `digest()` binds `public` to `_`, so the 40-word and 41-word indices have the
SAME digest — the VK pin cannot separate them either. The new gate REFUSES. -/
theorem the_old_gate_admits_a_public_input_it_should_refuse :
    the_old_gate_shape IDX_PREV PREV PREV 41 COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR = true
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV 41 COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑ **`the_old_public_conjunct_could_not_fail_on_this_path`** — stronger than one example, and
this is the reason the leg was worth building rather than a curiosity: for EVERY declared public
length the config could carry (any non-zero `publicLen`), the old gate's verdict is unchanged. A
conjunct that is constant over its input's whole live range is not a check. -/
theorem the_old_public_conjunct_could_not_fail_on_this_path (p q : Nat) (hp : 0 < p) (hq : 0 < q) :
    the_old_gate_shape IDX_PREV PREV PREV p COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
      = the_old_gate_shape IDX_PREV PREV PREV q COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR := by
  have h1 : decide (0 < p) = true := by simpa using hp
  have h2 : decide (0 < q) = true := by simpa using hq
  unfold the_old_gate_shape shapeOkRec
  rw [h1, h2]

/-- **`real_block_wrap_shape_discriminates`** — every single-count tamper of the real shape is
REFUSED, including the two conjuncts this gate adds beyond `shapeOkRec` and the four added on
2026-08-08. Without this the accept above would be compatible with a decision that accepts
everything. -/
theorem real_block_wrap_shape_discriminates :
    picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = true
    -- the proof carries fewer accumulators than the index declares
    ∧ picklesWrapShapeOk IDX_PREV 1 1 PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- the index declares fewer than the proof carries
    ∧ picklesWrapShapeOk 1 PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- commitments and challenge vectors disagree
    ∧ picklesWrapShapeOk IDX_PREV PREV 1 PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- no public input
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV 0 COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- 14 witness commitments
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC 14 (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- 5 σ evaluations
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS 5 COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- 14 coefficient columns
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) 14 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- 8 quotient chunks at chunk_size 1
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 8 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- a chunked index
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 2 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- a short IPA: 14 rounds against a 2^15 SRS
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS 14
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- ⚑ D1b/C3: one bulletproof challenge short — the packing produces 39 against `public = 40`
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        15 BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- ⚑ D1b: the 41-word index the VK digest cannot see
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV 41 COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- ⚑ B3: a step domain above `BACKEND_TICK_ROUNDS_N`
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL 17 PREV_EVAL_PAIRS PREV_EVAL_MAXLEN = false
    -- ⚑ B1: a chunked previous evaluation
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 PREV_EVAL_PAIRS 2 = false
    -- ⚑ B1: an EMPTY prev-evals walk, which `nonChunking` alone would accept vacuously
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
        NCHAL BRANCH_DOMAIN_LOG2 0 PREV_EVAL_MAXLEN = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §3 — THE WIRE GATE + `@[export]`. Same `String → String` C-ABI shape as
`dregg_mina_lc_verify`. Fail-closed on any malformed wire (`"ERR"` ⇒ the caller treats it as
REJECT). -/

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- **`decodeWrapShapeWire`** — parse the `INPUT` grammar into the eleven counts. Fail-closed
(`none`) on any deviation.

```
INPUT := "ip=" Nat ";pc=" Nat ";pv=" Nat ";pl=" Nat ";w=" Nat ";s=" Nat ";cf=" Nat
         ";tc=" Nat ";ck=" Nat ";ir=" Nat ";pr=" Nat
```
(`ip`=index prev_challenges, `pc`=proof prev_challenges, `pv`=proof accumulator challenge
vectors, `pl`=index public length, `w`=witness commitments, `s`=σ evaluations, `cf`=coefficient
columns, `tc`=t_comm chunks, `ck`=chunk size, `ir`=index IPA rounds, `pr`=proof IPA rounds.) -/
def decodeWrapShapeWire (s : String) :
    Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat
            × Nat × Nat × Nat × Nat) :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] => do
      let ip ← (parseField? "ip" p0).bind String.toNat?
      let pc ← (parseField? "pc" p1).bind String.toNat?
      let pv ← (parseField? "pv" p2).bind String.toNat?
      let pl ← (parseField? "pl" p3).bind String.toNat?
      let w  ← (parseField? "w"  p4).bind String.toNat?
      let sl ← (parseField? "s"  p5).bind String.toNat?
      let cf ← (parseField? "cf" p6).bind String.toNat?
      let tc ← (parseField? "tc" p7).bind String.toNat?
      let ck ← (parseField? "ck" p8).bind String.toNat?
      let ir ← (parseField? "ir" p9).bind String.toNat?
      let pr ← (parseField? "pr" p10).bind String.toNat?
      let bc ← (parseField? "bc" p11).bind String.toNat?
      let bd ← (parseField? "bd" p12).bind String.toNat?
      let pe ← (parseField? "pe" p13).bind String.toNat?
      let pm ← (parseField? "pm" p14).bind String.toNat?
      some (ip, pc, pv, pl, w, sl, cf, tc, ck, ir, pr, bc, bd, pe, pm)
  | _ => none

/-- **`minaWrapShapeGate`** — THE GATE. Decode the wire, run `picklesWrapShapeOk`, encode `"1"`
(ACCEPT) / `"0"` (REJECT). A malformed wire returns `"ERR"` (fail-closed: the caller treats it as
REJECT).

⚑ The 2026-08-08 field additions are a WIRE BREAK on purpose: the eleven-field form no longer
parses and returns `"ERR"`, which the caller treats as REJECT. An observer that was not rebuilt
refuses every block rather than silently skipping the four new legs. -/
def minaWrapShapeGate (s : String) : String :=
  match decodeWrapShapeWire s with
  | some (ip, pc, pv, pl, w, sl, cf, tc, ck, ir, pr, bc, bd, pe, pm) =>
      if picklesWrapShapeOk ip pc pv pl w sl cf tc ck ir pr bc bd pe pm then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_wrap_shape_ok]` — the C-ABI entry `dregg-lean-ffi`
calls once per exhibited block. The Mina observer decodes the block's `protocolStateProof` and
the archive renders the preamble verdict. -/
@[export dregg_mina_wrap_shape_ok]
def dregg_mina_wrap_shape_ok (s : String) : String := minaWrapShapeGate s

/-- **`minaWrapShapeGate_eq_decision`** — the gate string IS the decision, by construction. -/
theorem minaWrapShapeGate_eq_decision (s : String)
    (ip pc pv pl w sl cf tc ck ir pr bc bd pe pm : Nat)
    (hd : decodeWrapShapeWire s
            = some (ip, pc, pv, pl, w, sl, cf, tc, ck, ir, pr, bc, bd, pe, pm)) :
    minaWrapShapeGate s
      = (if picklesWrapShapeOk ip pc pv pl w sl cf tc ck ir pr bc bd pe pm then "1" else "0") := by
  unfold minaWrapShapeGate
  rw [hd]

/-! ## §4 — NON-VACUITY at the wire, in the interpreter.

The STRING layer uses well-founded recursion the kernel cannot reduce under `decide`, so these
are `native_decide` + `#assert_compiled` — NAMED, with a term and an axiom record, per
`metatheory/docs/GUARD-DISCIPLINE.md`. (They were `#guard`s until 2026-08-08; a `#guard` is the
same compiled evaluation with the name, the term and the axiom record deleted.)
`minaWrapShapeGate_eq_decision` ties this string surface to the decision §2 proves about. -/

/-- The REAL devnet block 539508's decoded shape ACCEPTS at the wire, and the retired
`prevLen = 0` freeze REFUSES it. -/
theorem wire_accepts_the_real_block_and_the_freeze_refuses_it :
    minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "1"
    ∧ minaWrapShapeGate
        "ip=0;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1"
      = "0" := by
  refine ⟨?_, ?_⟩ <;> native_decide
#assert_compiled wire_accepts_the_real_block_and_the_freeze_refuses_it

/-- Every single-count tamper REJECTS at the wire, including the four legs added 2026-08-08. -/
theorem wire_rejects_every_single_count_tamper :
    minaWrapShapeGate
        "ip=2;pc=1;pv=1;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "0"
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=1;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "0"
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=0;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "0"
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=14;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "0"
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=5;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "0"
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=14;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "0"
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=8;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "0"
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=2;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "0"
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=14;bc=16;bd=16;pe=43;pm=1"
      = "0" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide
#assert_compiled wire_rejects_every_single_count_tamper

/-- ⚑⚑ **`wire_rejects_the_four_new_legs`** — and the 2026-08-08 legs reject AT THE WIRE, which
is the surface the observer actually calls. `pl=41` is the accept the old gate let through. -/
theorem wire_rejects_the_four_new_legs :
    -- ⚑ D1b: the 41-word index the VK digest cannot see, and the old gate ACCEPTED
    minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=41;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "0"
    -- ⚑ C3: one bulletproof challenge short — the packing produces 39 words
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=15;bd=16;pe=43;pm=1" = "0"
    -- ⚑ B3: a step domain above `BACKEND_TICK_ROUNDS_N`
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=17;pe=43;pm=1" = "0"
    -- ⚑ B1: a chunked previous evaluation
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=2" = "0"
    -- ⚑ B1: an EMPTY prev-evals walk, which `nonChunking` alone accepts vacuously
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=0;pm=1"
      = "0" := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide
#assert_compiled wire_rejects_the_four_new_legs

/-- A malformed wire is `"ERR"`, never an accept: a truncated field list, a wrong key, a
non-numeral, and garbage. ⚑ The FIRST case is the pre-2026-08-08 eleven-field wire — an observer
that was not rebuilt gets `"ERR"`, which the caller treats as REJECT, rather than an accept that
skipped four legs. -/
theorem wire_is_fail_closed_on_every_malformation :
    minaWrapShapeGate "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15" = "ERR"
    ∧ minaWrapShapeGate
        "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;bc=16;bd=16;pe=43;pm=1" = "ERR"
    ∧ minaWrapShapeGate
        "ix=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "ERR"
    ∧ minaWrapShapeGate
        "ip=x;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15;bc=16;bd=16;pe=43;pm=1" = "ERR"
    ∧ minaWrapShapeGate "garbage" = "ERR"
    ∧ minaWrapShapeGate "" = "ERR" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide
#assert_compiled wire_is_fail_closed_on_every_malformation

/-! ## §5 — axiom hygiene. -/

#assert_axioms picklesWrapShapeOk_is_shapeOkRec
#assert_axioms picklesWrapShapeOk_imp_shapeOkRec
#assert_axioms picklesWrapShapeOk_imp_publicInputLen
#assert_axioms picklesWrapShapeOk_imp_nonChunking
#assert_axioms the_packing_reaches_the_index_public_count
#assert_axioms real_block_wrap_shape_accepts
#assert_axioms real_block_wrap_shape_refused_by_freeze
#assert_axioms the_old_gate_admits_a_public_input_it_should_refuse
#assert_axioms the_old_public_conjunct_could_not_fail_on_this_path
#assert_axioms real_block_wrap_shape_discriminates
#assert_axioms minaWrapShapeGate_eq_decision

#print axioms real_block_wrap_shape_accepts
#print axioms picklesWrapShapeOk_imp_shapeOkRec
#print axioms picklesWrapShapeOk_imp_publicInputLen
#print axioms the_old_gate_admits_a_public_input_it_should_refuse

end Dregg2.Bridge.PicklesWrapShapeGate
