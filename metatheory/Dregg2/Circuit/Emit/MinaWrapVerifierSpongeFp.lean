/-
# `Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp` — the **PHASE-1** transcript sponge on the machine:
the same Kimchi round program at the **`fp_kimchi`** constants and the **Pallas BASE** modulus.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Not one gate, column, constraint or descriptor byte is authored in
Rust. The emitted descriptors are `EffectLower.lowerAir` of `MinaWrapVerifierProgram.programAir` —
**at `pLimb` instead of `qLimb`, which is the whole of the field change**, because `programAir` is
parametric in the limb vector `pl : Nat → ℤ` and always was. Rust PROVES the artifacts and authors
no constraint. House Law #1.

## THE GAP THIS CLOSES

`MinaPhase2Chain` folds the WHOLE 46-permutation phase-2 transcript of Mina devnet block 539508 and
ends on that block's own `v′`/`u′`. Its tape's **element 0 is `fq_digest`** — and nothing derived it.
`MinaRealBlockTranscript` recomputes it, but in kernel `decide`/`#guard` over a `Nat` reference:
there is no gate anywhere tying `fq_digest` to the block, so *the phase-2 chain proves that a tape
absorbs to the published challenges without proving whose tape.*

Phase 1 is the derivation of that element. It is the **same machine** — same 469 columns, same
register file, same instruction ROM shape, same `absorbProg` instruction stream — run at

| | phase 2 (deployed) | phase 1 (here) |
|---|---|---|
| field | Pallas SCALAR `Fq = ZMod qN` | Pallas BASE `Fp = ZMod pN` |
| limb vector | `qLimb` | `pLimb` |
| constants | `fq_kimchi` (`fqParams`) | **`fp_kimchi` (`fpParams`)** |
| tape | 91 evaluations | 37 + 2 + 14 commitment COORDINATES |

## ⚑ THE PROGRAM IS NOT FORKED — IT IS GENERALISED, AND THE DEPLOYED ONE IS AN INSTANCE

A second copy of `roundAt`/`permInstrs`/`absorbCore` at the other constants is exactly the drift
`PastaPoseidonFq`'s docblock exists to prevent. So §1 lifts those three definitions to an ARBITRARY
`PastaPoseidonFq.Params`, and `the_deployed_fq_programs_are_this_one_at_fqParams` proves — by `rfl` —
that `MinaWrapVerifierSponge.absorbCore` **is** `absorbCoreP fqParams`. There is one program and two
parameter sets, and an edit that broke the identity would red HERE rather than silently give the
tree two sponges.

The DENOTATION is generalised the same way (§2). `the_permutation_program_computes_gen` and
`the_absorb_program_permutes_gen` hold at every `Params` with a positive modulus, for every register
file, with no hypotheses on the state — and `the_deployed_fq_denotation_is_this_one` exhibits the
deployed Fq theorem as the instance. So the Fp leg inherits a proof rather than repeating one.

## ⚑ THE CONSTANTS ARE WELDED TO o1-labs, NOT TRANSCRIBED

`PastaPoseidon.mdsN`/`rcsN` are 174 decimal literals that **nothing had ever compared to
`mina_poseidon::pasta::fp_kimchi::static_params()`** — the identical hole the Fq lane found and
closed at 660/660 emitted ROM immediates. `metatheory/fp_kimchi_params.json` is the missing upstream
artifact (`fixtures/kimchi-extractors/fp_kimchi_export.rs`, o1-labs `proof-systems` `f6d958dc05`),
and `circuit/tests/pasta_fp_sponge_proves.rs` §9 refuses unless all **660** immediates of the
EMITTED `pasta-fp-absorb.json` instruction ROM are its numbers. The Lean side's job is to make those
immediates BE the constants (§3), which is what `the_fp_constants_are_K3_s` says.

## WHAT IS AND IS NOT ESTABLISHED

  * **General, kernel-clean:** the permutation program computes `Core.perm fpParams`, at every state.
  * **NOT established here:** that any particular tape is a real block's. That is
    `MinaPhase1Chain`, which puts the block's 53 coordinates on this machine and ties the digest.
  * **Not a Wrap verification.** One stage of six; the five MSM stages need curve arithmetic that is
    not programmed.

## Axiom hygiene

Kernel-clean: `#assert_axioms` on every theorem, no `sorry`/`admit`/`native_decide`, and **zero
`#guard`s** — every fact is a named theorem.

Import line for the root: `import Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp`
-/
import Dregg2.Circuit.Emit.MinaWrapVerifierSponge

namespace Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.EffectLower (lowerAir)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK limbAt pLimb qLimb)
open Dregg2.Circuit.Emit.MinaWrapVerifierProgram
open Dregg2.Circuit.Emit.MinaWrapVerifierSponge
open Dregg2.Circuit.Emit.PastaPoseidonFq (Params fpParams fqParams)

set_option autoImplicit false
-- ⚑ A `set_option` does not cross an import: `MinaWrapVerifierSponge` sets this and the setting
-- does not arrive here. The 55-round programs are the same size, so the same depth is needed.
set_option maxRecDepth 400000

/-! ## §1 — THE SPONGE PROGRAM AT AN ARBITRARY PARAMETER SET.

⚑ `MinaWrapVerifierSponge.roundInstrs`, `sboxInstrs`, `mdsRowInstrs`, `allocAt` and `absorbInstrs`
are ALREADY parametric in the MDS, the round constants and the register tuple — the Fq file just
never named the parameter. The four definitions below are the missing names, nothing more, and §1b
proves the deployed objects are their instances. -/

/-- Round `r`'s three constants, out of an arbitrary parameter set. The Fq file's `rQ` is this at
`fqParams`. -/
def rcOf (P : Params) (r i : Nat) : Nat := (P.rcs.getD r []).getD i 0

/-- The round program at parameter set `P`, at round `r`'s own allocation. -/
def roundAtP (P : Params) (r : Nat) : List Instr :=
  roundInstrs (allocAt r 0) (allocAt r 1) (allocAt r 2) (allocAt r 3) (allocAt r 4) (allocAt r 5)
    (PastaPoseidonFq.Core.mc P) (rcOf P r)

/-- Rounds `0 … n−1`, in order, each at its own allocation. -/
def permInstrsUpToP (P : Params) (n : Nat) : List Instr := (List.range n).flatMap (roundAtP P)

/-- The full `poseidon_block_cipher`: 55 full rounds, no initial ARK. -/
def permInstrsP (P : Params) : List Instr := permInstrsUpToP P PastaPoseidon.rounds

/-- Two absorbs then the permutation — "add two into lanes 0 and 1, then permute". -/
def absorbCoreP (P : Params) : List Instr := absorbInstrs ++ permInstrsP P

/-- The absorption, padded to `2^11`. -/
def absorbProgP (P : Params) : List Instr := absorbCoreP P ++ List.replicate 396 padInstr

/-- One full round, padded to `2^5`. -/
def roundProgP (P : Params) : List Instr := roundAtP P 0 ++ List.replicate 2 padInstr

/-! ### §1b — the deployed Fq programs ARE these, at `fqParams`. -/

/-- ⚑ **THERE IS ONE PROGRAM, NOT TWO.** The 2 048-instruction stream `pasta-fq-absorb.json`,
`pasta-fq-wraplink.json` and `pasta-fq-chainlink.json` all carry is `absorbProgP fqParams`, and the
32-instruction round is `roundProgP fqParams` — by `rfl`, so an edit that made the Fp leg a second
transcription of the schedule would red here instead of quietly giving the tree two sponges. -/
theorem the_deployed_fq_programs_are_this_one_at_fqParams :
    absorbCoreP fqParams = absorbCore
    ∧ absorbProgP fqParams = absorbProg
    ∧ roundProgP fqParams = roundProg
    ∧ permInstrsP fqParams = permInstrs :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The lengths are the deployed ones at EVERY parameter set — 30 instructions a round, 1 650 a
permutation, 1 652 an absorption, and the two power-of-two heights. -/
theorem the_program_lengths (P : Params) :
    (roundAtP P 0).length = 30
    ∧ (permInstrsP P).length = 1650
    ∧ (absorbCoreP P).length = 1652
    ∧ (absorbProgP P).length = 2048
    ∧ (roundProgP P).length = 32 := by
  have h : ∀ r, (roundAtP P r).length = 30 := fun r => roundInstrs_length _ _ _ _ _ _ _ _
  refine ⟨h 0, ?_, ?_, ?_, ?_⟩
  · simp [permInstrsP, permInstrsUpToP, PastaPoseidon.rounds, List.length_flatMap, h]
  · simp [absorbCoreP, absorbInstrs, permInstrsP, permInstrsUpToP, PastaPoseidon.rounds,
      List.length_flatMap, h]
  · simp [absorbProgP, absorbCoreP, absorbInstrs, permInstrsP, permInstrsUpToP,
      PastaPoseidon.rounds, List.length_flatMap, h]
  · simp [roundProgP, h]

/-- ⚑ **AND THE LAST INSTRUCTION OF EACH WRITES NOTHING**, at every parameter set. This is what
makes the OUTPUT pin read the value the last REAL instruction wrote: `reg_hold_forces_preservation`
carries it across the padding. A program with no trailing padding pins a register one write early. -/
theorem the_last_instruction_writes_nothing (P : Params) :
    ((roundProgP P).getD 31 padInstr).wr = NREG
    ∧ ((absorbProgP P).getD 2047 padInstr).wr = NREG := by
  constructor
  · simp only [roundProgP, List.getD]
    rfl
  · simp only [absorbProgP, List.getD]
    rfl

/-! ## §2 — WHAT THE PROGRAM COMPUTES, AT AN ARBITRARY PARAMETER SET.

⚑ `MinaWrapVerifierSponge`'s `schedule_at_alloc_0/4/2` are already stated at an arbitrary modulus,
MDS and round-constant function — they are kernel reductions of thirty `stepRegsAt` applications and
know nothing about which field they are in. What was Fq-specific was only the bridge from the
program's association order to `Core.round`'s, and that is four short lemmas. They are generalised
here, and §2b exhibits the deployed Fq theorem as the instance. -/

/-- `Core.sbox P` is the seventh power in `ZMod P.modulus` — from the ring axioms, at every `P`. -/
theorem coreSbox_cast (P : Params) (x : Nat) :
    ((PastaPoseidonFq.Core.sbox P x : Nat) : ZMod P.modulus) = (x : ZMod P.modulus) ^ 7 := by
  unfold PastaPoseidonFq.Core.sbox
  rw [ZMod.natCast_mod]
  push_cast
  rfl

/-- Both sides land in `[0, N)`, so an equality in `ZMod N` is an equality of naturals. -/
theorem nat_of_zmod_eq (N a b : Nat) (ha : a < N) (hb : b < N)
    (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this

theorem refAdd_lt (N : Nat) (hN : 0 < N) (x y : Nat) : refAdd N x y < N := Nat.mod_lt _ hN

/-- ⚑ **ONE MDS ROW OF THE PROGRAM IS ONE MDS ROW OF THE REFERENCE**, at every parameter set. The
program reduces after every operation and the reference reduces once at the end; they agree because
both are the same element of `ZMod P.modulus` and both are canonical. -/
theorem mdsRowSchedule_agrees (P : Params) (hP : 0 < P.modulus)
    (m₀ m₁ m₂ rc s₀ s₁ s₂ : Nat) :
    mdsRowSchedule P.modulus m₀ m₁ m₂ rc s₀ s₁ s₂
      = (m₀ * PastaPoseidonFq.Core.sbox P s₀ + m₁ * PastaPoseidonFq.Core.sbox P s₁
          + m₂ * PastaPoseidonFq.Core.sbox P s₂ + rc) % P.modulus := by
  refine nat_of_zmod_eq _ _ _ (refAdd_lt _ hP _ _) (Nat.mod_lt _ hP) ?_
  rw [ZMod.natCast_mod]
  simp only [mdsRowSchedule, refAdd_cast, refMul_cast, sboxSchedule_cast]
  push_cast [coreSbox_cast P]
  ring

/-- ⚑ **THE PROGRAM'S ROUND IS `PastaPoseidonFq.Core.round`, AT EVERY PARAMETER SET.** The schedule
the thirty instructions walk and the reference round agree on EVERY state, as naturals. This is the
theorem the whole leg rests on, and it is now field-agnostic. -/
theorem roundSchedule_is_the_kimchi_round (P : Params) (hP : 0 < P.modulus) (r s₀ s₁ s₂ : Nat) :
    tripleList (roundSchedule P.modulus (PastaPoseidonFq.Core.mc P) (rcOf P r) s₀ s₁ s₂)
      = PastaPoseidonFq.Core.round P (P.rcs.getD r []) [s₀, s₁, s₂] := by
  have hround : PastaPoseidonFq.Core.round P (P.rcs.getD r []) [s₀, s₁, s₂]
      = [ (PastaPoseidonFq.Core.mc P 0 0 * PastaPoseidonFq.Core.sbox P s₀
            + PastaPoseidonFq.Core.mc P 0 1 * PastaPoseidonFq.Core.sbox P s₁
            + PastaPoseidonFq.Core.mc P 0 2 * PastaPoseidonFq.Core.sbox P s₂ + rcOf P r 0)
              % P.modulus
        , (PastaPoseidonFq.Core.mc P 1 0 * PastaPoseidonFq.Core.sbox P s₀
            + PastaPoseidonFq.Core.mc P 1 1 * PastaPoseidonFq.Core.sbox P s₁
            + PastaPoseidonFq.Core.mc P 1 2 * PastaPoseidonFq.Core.sbox P s₂ + rcOf P r 1)
              % P.modulus
        , (PastaPoseidonFq.Core.mc P 2 0 * PastaPoseidonFq.Core.sbox P s₀
            + PastaPoseidonFq.Core.mc P 2 1 * PastaPoseidonFq.Core.sbox P s₁
            + PastaPoseidonFq.Core.mc P 2 2 * PastaPoseidonFq.Core.sbox P s₂ + rcOf P r 2)
              % P.modulus ] := rfl
  rw [hround]
  simp only [tripleList, roundSchedule, mdsRowSchedule_agrees P hP]

/-- ⚑ **THE PERMUTATION PROGRAM COMPUTES THE KIMCHI PERMUTATION, AT EVERY PARAMETER SET.** By
induction over rounds; `the_allocation_hands_off` is what makes the induction hypothesis's output
registers the next round's inputs, and `runProgAt_append` is what makes a 55-round program 55 round
programs with nothing smuggled at the seams. -/
theorem the_permutation_program_computes_gen (P : Params) (hP : 0 < P.modulus) (st : RegFile) :
    ∀ n : Nat,
      [ runProgAt P.modulus st (permInstrsUpToP P n) (allocAt n 0)
      , runProgAt P.modulus st (permInstrsUpToP P n) (allocAt n 1)
      , runProgAt P.modulus st (permInstrsUpToP P n) (allocAt n 2) ]
        = PastaPoseidonFq.Core.permFrom P 0 n [st 0, st 1, st 2] := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      have hsplit : permInstrsUpToP P (k + 1) = permInstrsUpToP P k ++ roundAtP P k := by
        simp [permInstrsUpToP, List.range_succ]
      have hstep : PastaPoseidonFq.Core.permFrom P 0 (k + 1) [st 0, st 1, st 2]
          = PastaPoseidonFq.Core.round P (P.rcs.getD k [])
              (PastaPoseidonFq.Core.permFrom P 0 k [st 0, st 1, st 2]) := by
        simp [PastaPoseidonFq.Core.permFrom, List.range_succ]
      rw [hsplit, runProgAt_append, hstep, ← ih]
      set mid := runProgAt P.modulus st (permInstrsUpToP P k) with hmid
      have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hk with h | h | h
      · obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2⟩ := alloc_case_0 k h
        simp only [roundAtP, e0, e1, e2, e3, e4, e5, f0, f1, f2]
        rw [← roundSchedule_is_the_kimchi_round P hP k (mid 0) (mid 1) (mid 2),
          ← schedule_at_alloc_0 P.modulus (PastaPoseidonFq.Core.mc P) (rcOf P k) mid]
        rfl
      · obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2⟩ := alloc_case_1 k h
        simp only [roundAtP, e0, e1, e2, e3, e4, e5, f0, f1, f2]
        rw [← roundSchedule_is_the_kimchi_round P hP k (mid 4) (mid 5) (mid 0),
          ← schedule_at_alloc_4 P.modulus (PastaPoseidonFq.Core.mc P) (rcOf P k) mid]
        rfl
      · obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2⟩ := alloc_case_2 k h
        simp only [roundAtP, e0, e1, e2, e3, e4, e5, f0, f1, f2]
        rw [← roundSchedule_is_the_kimchi_round P hP k (mid 2) (mid 3) (mid 4),
          ← schedule_at_alloc_2 P.modulus (PastaPoseidonFq.Core.mc P) (rcOf P k) mid]
        rfl

/-- ⚑⚑ **THE ABSORB PROGRAM IS `perm ∘ absorb`, AT EVERY PARAMETER SET AND EVERY STATE.** No
hypotheses on the register file: the machine reduces mod `P.modulus` on the add, which is exactly
what `Core.absorbAt` does. This is the statement every link of a transcript chain is an instance
of — one theorem for every link of both phases. -/
theorem the_absorb_program_permutes_gen (P : Params) (hP : 0 < P.modulus) (st : RegFile) :
    [ runProgAt P.modulus st (absorbCoreP P) (allocAt PastaPoseidon.rounds 0)
    , runProgAt P.modulus st (absorbCoreP P) (allocAt PastaPoseidon.rounds 1)
    , runProgAt P.modulus st (absorbCoreP P) (allocAt PastaPoseidon.rounds 2) ]
      = PastaPoseidonFq.Core.perm P
          [(st 0 + st 3) % P.modulus, (st 1 + st 4) % P.modulus, st 2] := by
  have h0 : runProgAt P.modulus st absorbInstrs 0 = (st 0 + st 3) % P.modulus := by
    simp [runProgAt, absorbInstrs, stepRegsAt, opResultAt, yValue, NREG, refAdd]
  have h1 : runProgAt P.modulus st absorbInstrs 1 = (st 1 + st 4) % P.modulus := by
    simp [runProgAt, absorbInstrs, stepRegsAt, opResultAt, yValue, NREG, refAdd]
  have h2 : runProgAt P.modulus st absorbInstrs 2 = st 2 := by
    simp [runProgAt, absorbInstrs, stepRegsAt, NREG]
  have hperm := the_permutation_program_computes_gen P hP
    (runProgAt P.modulus st absorbInstrs) PastaPoseidon.rounds
  rw [h0, h1, h2] at hperm
  have hsplit : runProgAt P.modulus st (absorbCoreP P)
      = runProgAt P.modulus (runProgAt P.modulus st absorbInstrs) (permInstrsP P) := by
    rw [absorbCoreP, runProgAt_append]
  rw [hsplit, permInstrsP]
  exact hperm

/-! ### §2b — the DEPLOYED Fq denotation is this one. -/

/-- ⚑ **THE Fq LEG'S OWN THEOREM, DISCHARGED FROM THIS ONE.**
`MinaBlockFqTranscript.the_absorb_program_permutes_the_absorbed_state` — the statement all 46
phase-2 chain links rest on — is the general theorem at `fqParams`. Stated so that "one program, two
fields" is a fact rather than a docblock claim. -/
theorem the_deployed_fq_denotation_is_this_one (st : RegFile) :
    [ runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 0)
    , runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 1)
    , runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 2) ]
      = PastaPoseidonFq.Core.perm fqParams [(st 0 + st 3) % qN, (st 1 + st 4) % qN, st 2] :=
  the_absorb_program_permutes_gen fqParams (by decide) st

/-! ## §3 — THE Fp INSTANTIATION: `fp_kimchi` AT THE PALLAS BASE MODULUS.

⚑ The constants are **K3's own** — `PastaPoseidon.mdsN` / `rcsN`, reached through `fpParams`, the
parameter set `PastaPoseidonFq.core_is_Ref_at_Fp` proves runs `PastaPoseidon.Ref` function for
function. This file writes NO constants and NO reference: it names the instantiation and states what
the emitted program computes. -/

/-- ⚑ **THE CONSTANTS ARE K3's, NOT A COPY.** Both accessors are `rfl`-equal to the
`PastaPoseidon` data, so an edit that introduced a local table would break this rather than
silently give the machine a second set of constants. `pN` is the modulus. -/
theorem the_fp_constants_are_K3_s :
    PastaPoseidonFq.Core.mc fpParams 0 0 = (PastaPoseidon.mdsN.getD 0 []).getD 0 0
    ∧ rcOf fpParams 0 0 = (PastaPoseidon.rcsN.getD 0 []).getD 0 0
    ∧ fpParams.modulus = pN := ⟨rfl, rfl, rfl⟩

/-- ⚑ **AND THEY ARE NOT THE `fq_kimchi` ONES.** Reading `static_params()` off the wrong module is
the failure mode the K3 audit named; if this leg had silently inherited `fqParams` every theorem
below would still be true and the object would be the phase-2 sponge again. -/
theorem the_fp_constants_are_the_other_module :
    PastaPoseidonFq.Core.mc fpParams 0 0 ≠ PastaPoseidonFq.Core.mc fqParams 0 0
    ∧ rcOf fpParams 0 0 ≠ rcOf fqParams 0 0
    ∧ fpParams.modulus ≠ fqParams.modulus := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE PALLAS BASE MODULUS IS SMALLER THAN THE SCALAR ONE**, which is the fact that makes
phase 1's `digest()` unconditional. `DefaultFqSponge::digest` reinterprets the base-field squeeze in
the SCALAR field and returns `0` when it does not fit (`sponge.rs:388-397`, the documented `(q−p)/q`
zero-bias). On the WRAP side the base field is `Fp` and the target is `Fq`; `pN < qN`, so every
phase-1 digest fits and **the bias arm is unreachable here**. The residual is real on the STEP side,
where the inclusion runs the other way. -/
theorem the_wrap_digest_guard_never_fires : pN < qN := by decide

/-- The Fp round program, and the Fp absorption program — the deployed instruction streams at the
other parameter set. -/
def fpRoundProg : List Instr := roundProgP fpParams
def fpAbsorbProg : List Instr := absorbProgP fpParams
def fpAbsorbCore : List Instr := absorbCoreP fpParams

theorem fpProg_lengths :
    fpRoundProg.length = 32 ∧ fpAbsorbProg.length = 2048 ∧ fpAbsorbCore.length = 1652 :=
  ⟨(the_program_lengths fpParams).2.2.2.2, (the_program_lengths fpParams).2.2.2.1,
   (the_program_lengths fpParams).2.2.1⟩

/-- ⚑ **THE EMITTED Fp ABSORPTION IS `perm ∘ absorb` AT `fp_kimchi`**, for every register file. The
instance of §2 the whole phase-1 chain is built on. -/
theorem the_fp_absorb_program_permutes (st : RegFile) :
    [ runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 0)
    , runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 1)
    , runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 2) ]
      = PastaPoseidonFq.Core.perm fpParams [(st 0 + st 3) % pN, (st 1 + st 4) % pN, st 2] :=
  the_absorb_program_permutes_gen fpParams (by decide) st

/-- ⚑ **AND `Core.perm fpParams` IS K3's `PastaPoseidon.Ref.perm`** — by `PastaPoseidonFq.perm_at_fp`,
which is `rfl`. So the emitted Fp machine computes the permutation whose salts are pinned to
openmina's own regression constants in `Bridge.MinaStateHashDerive` §3, not a second Poseidon. -/
theorem the_fp_machine_computes_K3s_permutation (st : RegFile) :
    [ runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 0)
    , runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 1)
    , runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 2) ]
      = PastaPoseidon.Ref.perm [(st 0 + st 3) % pN, (st 1 + st 4) % pN, st 2] :=
  (the_fp_absorb_program_permutes st).trans (PastaPoseidonFq.perm_at_fp _)

/-- The FRESH-sponge corollary: the two-element absorption's squeeze is `Core.hash fpParams [x₀,x₁]`
— the value `ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, 55>::new(fp_kimchi::static_params())`
returns from `absorb(&[x₀,x₁]); squeeze()`, and (by `core_is_Ref_at_Fp`) K3's `Ref.hash`. -/
theorem the_fp_absorb_program_computes_the_kimchi_sponge (st : RegFile)
    (h0 : st 0 = 0) (h1 : st 1 = 0) (h2 : st 2 = 0) (hx₀ : st 3 < pN) (hx₁ : st 4 < pN) :
    [ runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 0)
    , runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 1)
    , runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 2) ]
      = PastaPoseidonFq.Core.absorbAll fpParams [0, 0, 0] [st 3, st 4] := by
  have hspec : PastaPoseidonFq.Core.absorbAll fpParams [0, 0, 0] [st 3, st 4]
      = PastaPoseidonFq.Core.perm fpParams [(0 + st 3) % pN, (0 + st 4) % pN, 0] := rfl
  rw [Nat.zero_add, Nat.zero_add, Nat.mod_eq_of_lt hx₀, Nat.mod_eq_of_lt hx₁] at hspec
  rw [hspec]
  have h := the_fp_absorb_program_permutes st
  rw [h0, h1, h2, Nat.zero_add, Nat.zero_add, Nat.mod_eq_of_lt hx₀, Nat.mod_eq_of_lt hx₁] at h
  exact h

theorem the_fp_absorb_program_squeezes_the_kimchi_hash (st : RegFile)
    (h0 : st 0 = 0) (h1 : st 1 = 0) (h2 : st 2 = 0) (hx₀ : st 3 < pN) (hx₁ : st 4 < pN) :
    runProgAt pN st fpAbsorbCore (allocAt PastaPoseidon.rounds 0)
      = PastaPoseidonFq.Core.hash fpParams [st 3, st 4] := by
  have hlane : ∀ (P : Params) (xs : List Nat),
      PastaPoseidonFq.Core.hash P xs
        = (PastaPoseidonFq.Core.absorbAll P [0, 0, 0] xs).getD 0 0 := fun _ _ => rfl
  rw [hlane, ← the_fp_absorb_program_computes_the_kimchi_sponge st h0 h1 h2 hx₀ hx₁,
    List.getD_cons_zero]

/-! ## §4 — THE AIR, THE PINS AND THE EMITTED DESCRIPTORS.

⚑ `programAir` at `pLimb`. Not one gate is authored here. The ALU polarities at `pLimb` already
exist — `MinaWrapVerifierAir.alu_mul_forces`, `alu_add_forces`, `alu_sub_forces` — which is why the
Fq leg needed a §2 (`alu_add_forces_fq`/`alu_sub_forces_fq`) and this one does not: the Fp side had
all three from the start. -/

/-- 192 public inputs: three state lanes in, three out. -/
def SPONGE_PI_COUNT : Nat := 6 * SK

theorem SPONGE_PI_COUNT_eq : SPONGE_PI_COUNT = 192 := rfl

/-- The round instance's pins: the first row's `(R0,R1,R2)` is the input state, the last row's
`(R4,R5,R0)` is the output state — `allocAt 0 {0,1,2}` and `allocAt 1 {0,1,2}`, the hand-off. -/
def fpRoundPins : List AirLeg :=
  pinBlock VmRow.first 0 0 ++ pinBlock VmRow.first 1 SK ++ pinBlock VmRow.first 2 (2 * SK)
    ++ pinBlock VmRow.last 4 (3 * SK) ++ pinBlock VmRow.last 5 (4 * SK)
    ++ pinBlock VmRow.last 0 (5 * SK)

/-- The absorb instance's pins: the fresh sponge state, the two absorbed values, and the squeeze. -/
def fpAbsorbPins : List AirLeg :=
  pinBlock VmRow.first 0 0 ++ pinBlock VmRow.first 1 SK ++ pinBlock VmRow.first 2 (2 * SK)
    ++ pinBlock VmRow.first 3 (3 * SK) ++ pinBlock VmRow.first 4 (4 * SK)
    ++ pinBlock VmRow.last 4 (5 * SK)

/-- ⚑ **THE Fp ROUND'S AIR** — `programAir pLimb`, unchanged, plus the 192 boundary pins that make
it a statement. -/
def fpRoundAir : EffectAir :=
  { programAir pLimb fpRoundProg with
    legs := (programAir pLimb fpRoundProg).legs ++ fpRoundPins }

def fpAbsorbAir : EffectAir :=
  { programAir pLimb fpAbsorbProg with
    legs := (programAir pLimb fpAbsorbProg).legs ++ fpAbsorbPins }

theorem fpRoundAir_mainRailOk : fpRoundAir.mainRailOk = true := by
  unfold fpRoundAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨programAir_mainRailOk pLimb fpRoundProg, ?_⟩
  simp only [fpRoundPins, pinBlock, List.all_append, List.all_map, Bool.and_eq_true,
    List.all_eq_true]
  repeat' apply And.intro
  all_goals (intro _ _; rfl)

theorem fpAbsorbAir_mainRailOk : fpAbsorbAir.mainRailOk = true := by
  unfold fpAbsorbAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨programAir_mainRailOk pLimb fpAbsorbProg, ?_⟩
  simp only [fpAbsorbPins, pinBlock, List.all_append, List.all_map, Bool.and_eq_true,
    List.all_eq_true]
  repeat' apply And.intro
  all_goals (intro _ _; rfl)

/-- ⚑ **THE EMITTED Fp ROUND DESCRIPTOR.** -/
def fpRoundDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fp-round::v1" PROG_WIDTH SPONGE_PI_COUNT [] fpRoundAir

/-- ⚑ **THE EMITTED Fp ABSORPTION DESCRIPTOR.** -/
def fpAbsorbDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fp-absorb::v1" PROG_WIDTH SPONGE_PI_COUNT [] fpAbsorbAir

/-- Both ROMs fit the deployed cell cap, by the same margin the Fq pair does — the instruction word
is the same 55 cells and the programs are the same lengths. -/
theorem the_fp_sponge_roms_fit :
    32 * ROM_ARITY = 1760 ∧ 2048 * ROM_ARITY = 112640
      ∧ 2048 * ROM_ARITY < MAX_ROM_CELLS := by decide

/-! ## §5 — THE HONEST WITNESSES, generated here.

Rust fills cells; it does not author them. The row generator is `MinaWrapVerifierSponge.rowAsgAt`
at `pN`/`pLimb` — the SAME generator the Fq leg uses (`rowAsgAt_is_the_program_one` proves it is
also the Fp machine's), driven over the STRICT register file `runRowsVecAt`, whose weld to the
semantics is `runRowsVecAt_is_runRowsAt`. ⚑ The strict structure IS the semantics here: wrapping a
list around the closure does not work, which is the 412-CPU-minute lesson this generator exists
because of. -/

/-- Three full-width Fp state lanes, so every limb of every operand block is exercised on row 0. -/
def ROUND_S0 : Nat := PastaField.Ref.X % pN
def ROUND_S1 : Nat := PastaField.Ref.Y % pN
def ROUND_S2 : Nat := PastaField.Ref.fpAdd ROUND_S0 ROUND_S1

def fpRoundInitVec : List Nat := [ROUND_S0, ROUND_S1, ROUND_S2, 0, 0, 0]

def fpRoundInit : RegFile := regsOf fpRoundInitVec

def fpRoundTrace : List (List ℤ) := runRowsVecAt pN pLimb fpRoundInitVec 0 fpRoundProg

/-- ⚑ **AND THE EMITTED ROUND TRACE IS `runRowsAt`'s** — the object every denotation above is a
statement about. -/
theorem fpRoundTrace_is_the_program_run :
    fpRoundTrace = runRowsAt pN pLimb fpRoundInit 0 fpRoundProg := by
  rw [fpRoundTrace, runRowsVecAt_is_runRowsAt, fpRoundInit]

def fpRoundOutVec : List Nat := runProgVecAt pN fpRoundInitVec (roundAtP fpParams 0)

/-- The output state the machine reaches, computed by the interpreter — never asserted. -/
def fpRoundOut : List Nat :=
  [regsOf fpRoundOutVec 4, regsOf fpRoundOutVec 5, regsOf fpRoundOutVec 0]

/-- ⚑ **THE EMITTED Fp ROUND'S OUTPUT IS THE `fp_kimchi` KIMCHI ROUND OF ITS INPUT.** Not a `decide`
at a point: `roundSchedule_is_the_kimchi_round` instantiated, so the artifact inherits a statement
that holds at every state. -/
theorem the_emitted_fp_round_output_is_the_kimchi_round :
    fpRoundOut = PastaPoseidonFq.Core.round fpParams (PastaPoseidon.rcsN.getD 0 [])
      [fpRoundInit 0, fpRoundInit 1, fpRoundInit 2] := by
  have hregs : regsOf fpRoundOutVec = runProgAt pN fpRoundInit (roundAtP fpParams 0) := by
    rw [fpRoundOutVec, regsOf_runProgVecAt, fpRoundInit]
  have halloc : roundAtP fpParams 0
      = roundInstrs 0 1 2 3 4 5 (PastaPoseidonFq.Core.mc fpParams) (rcOf fpParams 0) := rfl
  show [ regsOf fpRoundOutVec 4, regsOf fpRoundOutVec 5, regsOf fpRoundOutVec 0 ] = _
  rw [hregs, halloc]
  exact (congrArg tripleList
      (schedule_at_alloc_0 pN (PastaPoseidonFq.Core.mc fpParams) (rcOf fpParams 0) fpRoundInit)).trans
    (roundSchedule_is_the_kimchi_round fpParams (by decide) 0
      (fpRoundInit 0) (fpRoundInit 1) (fpRoundInit 2))

def fpRoundPIs : List ℤ :=
  (List.range SK).map (limbAt ROUND_S0) ++ (List.range SK).map (limbAt ROUND_S1)
    ++ (List.range SK).map (limbAt ROUND_S2)
    ++ (List.range SK).map (limbAt (fpRoundOut.getD 0 0))
    ++ (List.range SK).map (limbAt (fpRoundOut.getD 1 0))
    ++ (List.range SK).map (limbAt (fpRoundOut.getD 2 0))

theorem fpRoundPIs_length : fpRoundPIs.length = 192 := by simp [fpRoundPIs, SK]

/-! ### §5b — the absorption's witness, at the values the UPSTREAM sponge was measured on.

⚑ The absorbed pair is `[1, 2]` deliberately: `metatheory/fp_kimchi_params.json`'s `pair12` KAT was
produced by `ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, 55>::new(fp_kimchi::static_params())`
itself, so the emitted descriptor's OUTPUT PUBLIC INPUT is a value o1-labs' own implementation
returns and the Rust harness pins its limbs. -/

def ABSORB_X0 : Nat := 1
def ABSORB_X1 : Nat := 2

def fpAbsorbInitVec : List Nat := [0, 0, 0, ABSORB_X0, ABSORB_X1, 0]

def fpAbsorbInit : RegFile := regsOf fpAbsorbInitVec

def fpAbsorbTrace : List (List ℤ) := runRowsVecAt pN pLimb fpAbsorbInitVec 0 fpAbsorbProg

theorem fpAbsorbTrace_is_the_program_run :
    fpAbsorbTrace = runRowsAt pN pLimb fpAbsorbInit 0 fpAbsorbProg := by
  rw [fpAbsorbTrace, runRowsVecAt_is_runRowsAt, fpAbsorbInit]

def fpAbsorbOutVec : List Nat := runProgVecAt pN fpAbsorbInitVec fpAbsorbCore

/-- The squeezed lane, computed by the interpreter. -/
def fpAbsorbOut : Nat := regsOf fpAbsorbOutVec (allocAt PastaPoseidon.rounds 0)

/-- ⚑ **THE EMITTED Fp ABSORPTION'S OUTPUT IS `Core.hash fpParams [1, 2]`** — the `fp_kimchi`
sponge's own answer, proved from the general theorem, so nothing here is a re-checked constant. -/
theorem the_emitted_fp_absorb_output_is_the_kimchi_hash :
    fpAbsorbOut = PastaPoseidonFq.Core.hash fpParams [ABSORB_X0, ABSORB_X1] := by
  have hregs : regsOf fpAbsorbOutVec = runProgAt pN fpAbsorbInit fpAbsorbCore := by
    rw [fpAbsorbOutVec, regsOf_runProgVecAt, fpAbsorbInit]
  show regsOf fpAbsorbOutVec (allocAt PastaPoseidon.rounds 0) = _
  rw [hregs]
  exact the_fp_absorb_program_squeezes_the_kimchi_hash fpAbsorbInit rfl rfl rfl
    (by decide) (by decide)

/-- ⚑ **AND IT IS K3's `Ref.hash [1,2]`**, by `core_is_Ref_at_Fp` — so the emitted public input is a
value of the sponge whose salts `Bridge.MinaStateHashDerive` pins to openmina's own constants. -/
theorem the_emitted_fp_absorb_output_is_K3s_hash :
    fpAbsorbOut = PastaPoseidon.Ref.hash [ABSORB_X0, ABSORB_X1] :=
  the_emitted_fp_absorb_output_is_the_kimchi_hash.trans (PastaPoseidonFq.core_is_Ref_at_Fp _)

def fpAbsorbPIs : List ℤ :=
  (List.range SK).map (fun _ => (0 : ℤ)) ++ (List.range SK).map (fun _ => (0 : ℤ))
    ++ (List.range SK).map (fun _ => (0 : ℤ))
    ++ (List.range SK).map (limbAt ABSORB_X0) ++ (List.range SK).map (limbAt ABSORB_X1)
    ++ (List.range SK).map (limbAt fpAbsorbOut)

theorem fpAbsorbPIs_length : fpAbsorbPIs.length = 192 := by simp [fpAbsorbPIs, SK]

/-- ⚑ **AND THE FRESH-SPONGE PINS ARE THE ZERO VECTOR.** The statement the absorption descriptor
makes is `Core.hash` only if the three initial state lanes are pinned to zero; a verifier supplied a
different initial state would be checking a different (still true) sentence about a sponge that was
not fresh. -/
theorem the_fp_absorb_pins_a_fresh_sponge :
    (fpAbsorbPIs.take (3 * SK)).all (fun v => decide (v = 0)) = true := by decide

#assert_axioms the_deployed_fq_programs_are_this_one_at_fqParams
#assert_axioms the_program_lengths
#assert_axioms the_last_instruction_writes_nothing
#assert_axioms coreSbox_cast
#assert_axioms nat_of_zmod_eq
#assert_axioms refAdd_lt
#assert_axioms mdsRowSchedule_agrees
#assert_axioms roundSchedule_is_the_kimchi_round
#assert_axioms the_permutation_program_computes_gen
#assert_axioms the_absorb_program_permutes_gen
#assert_axioms the_deployed_fq_denotation_is_this_one
#assert_axioms the_fp_constants_are_K3_s
#assert_axioms the_fp_constants_are_the_other_module
#assert_axioms the_wrap_digest_guard_never_fires
#assert_axioms fpProg_lengths
#assert_axioms the_fp_absorb_program_permutes
#assert_axioms the_fp_machine_computes_K3s_permutation
#assert_axioms the_fp_absorb_program_computes_the_kimchi_sponge
#assert_axioms the_fp_absorb_program_squeezes_the_kimchi_hash
#assert_axioms SPONGE_PI_COUNT_eq
#assert_axioms fpRoundAir_mainRailOk
#assert_axioms fpAbsorbAir_mainRailOk
#assert_axioms the_fp_sponge_roms_fit
#assert_axioms fpRoundTrace_is_the_program_run
#assert_axioms the_emitted_fp_round_output_is_the_kimchi_round
#assert_axioms fpRoundPIs_length
#assert_axioms fpAbsorbTrace_is_the_program_run
#assert_axioms the_emitted_fp_absorb_output_is_the_kimchi_hash
#assert_axioms the_emitted_fp_absorb_output_is_K3s_hash
#assert_axioms fpAbsorbPIs_length
#assert_axioms the_fp_absorb_pins_a_fresh_sponge

end Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp
