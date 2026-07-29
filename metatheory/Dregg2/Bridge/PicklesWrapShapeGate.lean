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
    (`verifier.rs:810-813`, `VerifyError::IncorrectPrevChallengesLength`); the public input is
    non-empty; there are `COLUMNS = 15` witness commitments and coefficient columns and
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

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Dregg2.Bridge.PicklesWrapShapeGate

open Dregg2.Circuit.Emit.KimchiVerify (shapeOk shapeOkRec COLUMNS PERMUTS)

/-! ## §1 — THE DECISION. -/

/-- **`picklesWrapShapeOk`** — `shapeOkRec` plus the two length agreements a RECURSIVE Wrap
proof owes that a single-proof index does not.

  * `proofPrevVecs = proofPrev`: `messages_for_next_step_proof` exhibits one accumulator
    COMMITMENT and one 16-challenge VECTOR per carried proof. A proof showing commitments
    without their challenge vectors (or the reverse) is malformed, and the fold that consumes
    them (`prevChalFoldOk`) would be reading a list of a different length.
  * `proofRounds = idxRounds`: `bulletproof.lr.len()` is the IPA round count `k`, which is
    `log₂ max_poly_size` of the index (`kimchi_pasta_basic.ml:16-17`, `SideShape.rounds = 15`
    on the Wrap side). A short `lr` is a proof over a smaller SRS. -/
def picklesWrapShapeOk
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
      idxRounds proofRounds : Nat) :
    picklesWrapShapeOk idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen tCommLen
        chunkSize idxRounds proofRounds
      = (shapeOkRec idxPrev proofPrev publicLen wLen sLen coeffLen tCommLen chunkSize
         && decide (proofPrevVecs = proofPrev)
         && decide (proofRounds = idxRounds)) := rfl

/-- **THE PAYOFF DIRECTION.** An accept ENTAILS the upstream shape check accepts. (The converse
is deliberately false: `shapeOkRec` alone does not look at `lr` or at the accumulator vectors.) -/
theorem picklesWrapShapeOk_imp_shapeOkRec
    {idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen tCommLen chunkSize
      idxRounds proofRounds : Nat}
    (h : picklesWrapShapeOk idxPrev proofPrev proofPrevVecs publicLen wLen sLen coeffLen
          tCommLen chunkSize idxRounds proofRounds = true) :
    shapeOkRec idxPrev proofPrev publicLen wLen sLen coeffLen tCommLen chunkSize = true := by
  unfold picklesWrapShapeOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

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

/-- **`real_block_wrap_shape_accepts`** — the REAL devnet block 539508's decoded Wrap shape is
ACCEPTED. -/
theorem real_block_wrap_shape_accepts :
    picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR
      = true := by decide

/-- ⚑ **`real_block_wrap_shape_refused_by_freeze`** — and the retired `prevLen = 0` freeze
REFUSES it. This is the whole reason the Pickles conjunct could not simply be wired to the old
`shapeOk`: that predicate rejects Mina. -/
theorem real_block_wrap_shape_refused_by_freeze :
    picklesWrapShapeOk 0 PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR = false
    ∧ shapeOk PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`real_block_wrap_shape_discriminates`** — every single-count tamper of the real shape is
REFUSED, including the two conjuncts this gate adds beyond `shapeOkRec`. Without this the accept
above would be compatible with a decision that accepts everything. -/
theorem real_block_wrap_shape_discriminates :
    picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR = true
    -- the proof carries fewer accumulators than the index declares
    ∧ picklesWrapShapeOk IDX_PREV 1 1 PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR = false
    -- the index declares fewer than the proof carries
    ∧ picklesWrapShapeOk 1 PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR = false
    -- commitments and challenge vectors disagree
    ∧ picklesWrapShapeOk IDX_PREV PREV 1 PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR = false
    -- no public input
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV 0 COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR = false
    -- 14 witness commitments
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC 14 (PERMUTS - 1) COLUMNS 7 1 ROUNDS LR = false
    -- 5 σ evaluations
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS 5 COLUMNS 7 1 ROUNDS LR = false
    -- 14 coefficient columns
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) 14 7 1 ROUNDS LR = false
    -- 8 quotient chunks at chunk_size 1
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 8 1 ROUNDS LR
        = false
    -- a chunked index
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 2 ROUNDS LR
        = false
    -- a short IPA: 14 rounds against a 2^15 SRS
    ∧ picklesWrapShapeOk IDX_PREV PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 ROUNDS 14
        = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

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
    Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10] => do
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
      some (ip, pc, pv, pl, w, sl, cf, tc, ck, ir, pr)
  | _ => none

/-- **`minaWrapShapeGate`** — THE GATE. Decode the wire, run `picklesWrapShapeOk`, encode `"1"`
(ACCEPT) / `"0"` (REJECT). A malformed wire returns `"ERR"` (fail-closed: the caller treats it as
REJECT). -/
def minaWrapShapeGate (s : String) : String :=
  match decodeWrapShapeWire s with
  | some (ip, pc, pv, pl, w, sl, cf, tc, ck, ir, pr) =>
      if picklesWrapShapeOk ip pc pv pl w sl cf tc ck ir pr then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_wrap_shape_ok]` — the C-ABI entry `dregg-lean-ffi`
calls once per exhibited block. The Mina observer decodes the block's `protocolStateProof` and
the archive renders the preamble verdict. -/
@[export dregg_mina_wrap_shape_ok]
def dregg_mina_wrap_shape_ok (s : String) : String := minaWrapShapeGate s

/-- **`minaWrapShapeGate_eq_decision`** — the gate string IS the decision, by construction. -/
theorem minaWrapShapeGate_eq_decision (s : String)
    (ip pc pv pl w sl cf tc ck ir pr : Nat)
    (hd : decodeWrapShapeWire s = some (ip, pc, pv, pl, w, sl, cf, tc, ck, ir, pr)) :
    minaWrapShapeGate s
      = (if picklesWrapShapeOk ip pc pv pl w sl cf tc ck ir pr then "1" else "0") := by
  unfold minaWrapShapeGate
  rw [hd]

/-! ## §4 — NON-VACUITY at the wire, in the interpreter (the STRING layer uses well-founded
recursion the kernel cannot reduce under `decide`; `minaWrapShapeGate_eq_decision` ties the
string surface to the decision `§2` proves about). -/

-- The REAL devnet block 539508's decoded shape ACCEPTS.
#guard minaWrapShapeGate "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15" == "1"
-- ⚑ The `prevLen = 0` freeze REFUSES it.
#guard minaWrapShapeGate "ip=0;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15" == "0"
-- Each single-count tamper REJECTS.
#guard minaWrapShapeGate "ip=2;pc=1;pv=1;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15" == "0"
#guard minaWrapShapeGate "ip=2;pc=2;pv=1;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15" == "0"
#guard minaWrapShapeGate "ip=2;pc=2;pv=2;pl=0;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15" == "0"
#guard minaWrapShapeGate "ip=2;pc=2;pv=2;pl=40;w=14;s=6;cf=15;tc=7;ck=1;ir=15;pr=15" == "0"
#guard minaWrapShapeGate "ip=2;pc=2;pv=2;pl=40;w=15;s=5;cf=15;tc=7;ck=1;ir=15;pr=15" == "0"
#guard minaWrapShapeGate "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=14;tc=7;ck=1;ir=15;pr=15" == "0"
#guard minaWrapShapeGate "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=8;ck=1;ir=15;pr=15" == "0"
#guard minaWrapShapeGate "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=2;ir=15;pr=15" == "0"
#guard minaWrapShapeGate "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=14" == "0"
-- A malformed wire is `"ERR"`, never an accept: a truncated field list, a wrong key, a
-- non-numeral, and garbage.
#guard minaWrapShapeGate "ip=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15" == "ERR"
#guard minaWrapShapeGate "ix=2;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15" == "ERR"
#guard minaWrapShapeGate "ip=x;pc=2;pv=2;pl=40;w=15;s=6;cf=15;tc=7;ck=1;ir=15;pr=15" == "ERR"
#guard minaWrapShapeGate "garbage" == "ERR"
#guard minaWrapShapeGate "" == "ERR"

/-! ## §5 — axiom hygiene. -/

#assert_axioms picklesWrapShapeOk_is_shapeOkRec
#assert_axioms picklesWrapShapeOk_imp_shapeOkRec
#assert_axioms real_block_wrap_shape_accepts
#assert_axioms real_block_wrap_shape_refused_by_freeze
#assert_axioms real_block_wrap_shape_discriminates
#assert_axioms minaWrapShapeGate_eq_decision

#print axioms real_block_wrap_shape_accepts
#print axioms picklesWrapShapeOk_imp_shapeOkRec

end Dregg2.Bridge.PicklesWrapShapeGate
