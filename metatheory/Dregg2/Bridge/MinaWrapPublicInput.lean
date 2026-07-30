/-
# Dregg2.Bridge.MinaWrapPublicInput — **the 40-word Wrap public input as a FUNCTION of wire data,
and the census of what the wire actually reaches.**

⚑ **SUBSTRATE.** No AIR here. This is a LAYOUT plus an MSM, authored in Lean because the layout IS
semantics: which of forty slots carries the block is the whole content of the proof↔header binding.

## The question this file answers

`MinaWrapPublicCommGate.PUBLIC_INPUT` is forty literals of ONE devnet block. Every rung above it —
`public_comm`, the Fq-sponge, β/γ/α′/ζ′, the IPA transcript, the opening relation — is stated over
those literals, so the whole ladder is pinned to one height. To run it per block you need the forty
words as a FUNCTION of what a peer serves. This file is that function, and the census of which
arguments a peer actually supplies.

## ⚑⚑ THE CENSUS — measured against the pinned block, not asserted

| slot(s) | word | where it comes from |
|---|---|---|
| 0 | `combined_inner_product` | ⚠ **`expand_deferred`** |
| 1 | `b` | ⚠ **`expand_deferred`** |
| 2 | `zeta_to_srs_length` | ⚠ **`expand_deferred`** |
| 3 | `zeta_to_domain_size` | ⚠ **`expand_deferred`** |
| 4 | `perm` | ⚠ **`expand_deferred`** |
| 5–8 | `plonk.{alpha, beta, gamma, zeta}` | ✅ WIRE — `deferred_values.plonk`, walked at `mina_pickles.rs` `decode_proof_at` |
| 9 | `xi` | ⚠ **`expand_deferred`** |
| 10 | `sponge_digest_before_evaluations` | ✅ WIRE — four 64-bit limbs, recombined |
| 11 | `messages_for_next_wrap_proof` digest | ✅ **DERIVED** — `MinaStateHashWordGate.word11`, compiled, per block |
| 12 | `messages_for_next_step_proof` digest | ✅ **DERIVED** — `MinaStateHashWordGate.word12`, compiled, per block, and the ONLY slot the served header enters |
| 13–28 | `deferred_values.bulletproof_challenges` (16) | ✅ WIRE |
| 29 | `branch_data`, packed | ✅ WIRE — `proofs_verified` tag + `domain_log2` |
| 30–39 | zero padding to 40 | ✅ constant |

**34 of 40 words are reachable from bytes a peer already serves**, and `bridge/src/mina_pickles.rs`
`decode_proof_at` already WALKS every one of them — it discards them because nothing asked. The six
that are not reachable are exactly `expand_deferred`'s outputs.

## ⚑ And `expand_deferred` needs NOTHING but the Wrap proof's own bytes

This is the fact that makes the per-block path finite, and it is a READING of the two
implementations rather than something this lane executed — say which:

  * `xi` and the evaluation-scale `r` come from an `Fr`-sponge **seeded with
    `sponge_digest_before_evaluations`**, which is slot 10 and is ON THE WIRE. That is what it is on
    the wire *for*.
  * `combined_inner_product` is the `(xi, r)`-fold of the STEP proof's evaluations — and the Wrap
    proof carries them as `prev_evals`, which `decode_proof_at` walks in full (15 `w`, 15
    `coefficients`, `z`, 6 `s`, 6 selectors, `ft_eval1`). `MinaRealBlockGate.cipR` already
    reproduces this fold on the real block across all 47 `es` entries.
  * `b` is `b_poly(chals, zeta) + r · b_poly(chals, zetaw)` over
    `messages_for_next_step_proof.old_bulletproof_challenges` — ON THE WIRE, and `b_poly` exists
    (`MinaWrapOpeningGate.bPoly`, `PastaIPA.sVec`).
  * `zeta_to_srs_length`, `zeta_to_domain_size` and `perm` are powers of `zeta` and the permutation
    scalar of `derive_plonk` — functions of wire values and the domain.

So there is **no missing source**, only missing computation. `docs/MINA-REAL-BLOCK-GATE.md` §8.3
already said this ("What is missing is **computation, not a source**"); this file makes the split
mechanical, and `DeferredWords` is the exact interface the next lane fills.

## What is proved here, and what is a stated reading

**PROVED, on the pinned block, kernel-clean:**

  * the layout is total and has length 40, and it READS every field (bump any input, the list moves);
  * slots 11 and 12 of `PUBLIC_INPUT` ARE `word11`/`word12` of the served header of block 539508 —
    independently sourced from `MinaStateHashWordGate.B539508`, so this is not circular;
  * the **width signature** discriminates: every slot this layout calls a `ScalarChallenge` is
    `< 2^128` and every slot it calls a full `Fq` element is `≥ 2^128`. A layout that swapped a
    challenge slot for a field slot fails this immediately, on real data;
  * slots 2 and 3 are EQUAL on the real block — `zeta_to_srs_length = zeta_to_domain_size`, which is
    what a Step `domain_log2 = 16` against `max_poly_size = 2^16` forces, and is a coincidence no
    other pair of slots exhibits;
  * `publicCommOf` at the pinned words IS `MinaWrapPublicCommGate.publicComm`, definitionally — so
    parameterising the MSM did not change the object rung 5e proved.

**COMPILED (`#guard`), not kernel — and the split is deliberate:** that moving word 12 moves the
commitment. That was written `by decide` and FAILED: one 40-ladder MSM is not a kernel proof term at
this file's option budget, and buying it would cost ~15 s for an INSTANCE. `MinaStateHashWordGate`
states the rule this follows — *the kernel's job is the CHECKER, the differential's job is the
INSTANCE* — and rung 5e already carries the kernel-side identity.

**A STATED READING, not a measurement — and the falsifier is named:** that the 34 non-deferred slots
carry the wire fields this table names, *for slots other than 11 and 12*. This lane did not run the
extractor. `WIRE_539508` below is projected OUT of `PUBLIC_INPUT` at the slots claimed, so the
round-trip is definitional and proves nothing about the claim; what tests it is the extractor
emitting the 34 values from the binprot bytes and `#guard`ing them against these projections. That
is the first item of this file's BUILD REQUEST, and until it runs the census is a reading.

## Trusted, unchanged and named

The 56 `VK_INDEX` elements and the 40 `LAGRANGE` points are **config**. Nothing here derives either
from the chain. A wrong VK makes word 12 the digest of the wrong statement and every rung above it
verifies the wrong claim, silently.

NOT imported by the `Dregg2` root, per house practice for gates.
-/
import Dregg2.Circuit.Emit.MinaWrapPublicInputFromHeader

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaWrapPublicInput

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurveComplete (projEqM)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt padd msmComm)
open Dregg2.Circuit.Emit.MinaWrapPublicCommGate
  (LAGRANGE SRS_H PUBLIC_INPUT PUBLIC_COMM_GOLD NEG_PUBLIC publicComm)
open Dregg2.Bridge.MinaStateHashWordGate (B539508)

/-! ## §1 — the two halves of the public input. -/

/-- **The 34 words a peer's bytes supply.** Field names are the WIRE's, not slot indices, because a
slot index is exactly the thing that goes wrong silently.

⚑ `word11`/`word12` are DERIVED rather than carried: `MinaStateHashWordGate.word11`/`word12`
compute them from the served `stateHash`, the proof's own accumulators and the pinned VK, in
compiled Lean at a measured **28.9 ms/block**. They are in this structure because they are inputs to
the LAYOUT, not because anyone hands them over. -/
structure WireWords where
  /-- `deferred_values.plonk.alpha`, a 128-bit `ScalarChallenge`. -/
  alpha : Nat
  /-- `deferred_values.plonk.beta`. -/
  beta : Nat
  /-- `deferred_values.plonk.gamma`. -/
  gamma : Nat
  /-- `deferred_values.plonk.zeta`. -/
  zeta : Nat
  /-- `sponge_digest_before_evaluations`, recombined from its four 64-bit limbs:
  `Σ limbᵢ · 2^(64i)`. -/
  spongeDigest : Nat
  /-- `messages_for_next_wrap_proof` digest — `word11 mnwComm mnwChals`. -/
  word11 : Nat
  /-- `messages_for_next_step_proof` digest — `word12 stateHash accComm accChals`. ⚑ The ONLY slot
  the served block enters. -/
  word12 : Nat
  /-- `deferred_values.bulletproof_challenges`, sixteen 128-bit `ScalarChallenge`s. -/
  bpChallenges : List Nat
  /-- `deferred_values.branch_data`, PACKED — `Field.pack [proofs_verified(2 bits) ‖
  domain_log2(8 bits)]`, i.e. `pvBits + 4 · domainLog2`.

  ⚑ A READING this lane did not run: the pinned block is `{proofs_verified = N2, domain_log2 = 16}`
  and its slot-29 value is `67 = 3 + 4·16`, so `Index.to_bits N2` must be `[1,1] = 3`, NOT
  `Proofs_verified.to_int N2 = 2`. `branchDataPacked` below exhibits the arithmetic; that the tag
  byte `2` maps to the bits `3` is `pickles_base/proofs_verified.ml`'s business and is the second
  thing the extractor must confirm. -/
  branchData : Nat
deriving Repr, DecidableEq

/-- **The six words `expand_deferred` must produce**, and the reason this is a structure rather than
six arguments: it is the exact obligation the next lane discharges, and an empty one is visible.

Every one is a function of the Wrap proof's OWN bytes — see the header. None is a function of the
block, of the chain, or of anything a peer could choose independently of the proof. -/
structure DeferredWords where
  /-- `combined_inner_product` — the `(xi, r)`-fold of `prev_evals` and `ft_eval1`. -/
  cip : Nat
  /-- `b` — `b_poly(chals, zeta) + r · b_poly(chals, zetaw)`. -/
  b : Nat
  /-- `zeta_to_srs_length` — `zeta ^ max_poly_size`. -/
  zetaToSrsLength : Nat
  /-- `zeta_to_domain_size` — `zeta ^ n`. -/
  zetaToDomainSize : Nat
  /-- `perm` — the permutation scalar of `derive_plonk`. -/
  perm : Nat
  /-- `xi` — the polynomial-scale challenge, squeezed from the `Fr`-sponge seeded with
  `sponge_digest_before_evaluations`. -/
  xi : Nat
deriving Repr, DecidableEq

/-- `Field.pack [proofs_verified bits ‖ domain_log2 bits]` — low bits first, so the two
`proofs_verified` bits are the least significant. -/
def branchDataPacked (pvBits domainLog2 : Nat) : Nat := pvBits + 4 * domainLog2

/-- The pinned block's `branch_data`, exhibited rather than asserted. -/
theorem branch_data_of_the_pinned_block : branchDataPacked 3 16 = 67 := by decide

/-! ## §2 — THE LAYOUT. -/

/-- **`publicInputWords`** — `PreparedStatement::to_public_input(40)`, as a function.

⚑ Order is the whole correctness question, exactly as it is in `MinaBinprot`: a slot map with two
fields swapped does not fail, it silently commits to a different statement and the Fq-sponge below
it produces different challenges that nothing compares against. The width signature in §3 is the
instrument that catches it.

⚑⚑ **CORRECTED 2026-07-30, and this is a MEASURED correction, not a re-reading.** Slots 5-7 used to
read `alpha, beta, gamma`. `Wrap.Statement.to_data` (`composition_types.ml:826-880`) lays the
`challenge` bucket down before the `scalar_challenge` one, so they are **`beta, gamma, alpha`**.
Every instrument this file had was blind to the difference — the round trip in §3 is definitional
(`WIRE_539508` is projected OUT of the list being reassembled, so it holds under any permutation of
the three names), `publicInputWords_reads_every_field` is permutation-blind by construction, and
all three are 128-bit challenges so the width signature cannot separate them. What sees it is
`MinaWrapDeferred.permOf`, which reads β, γ and α in three distinct roles;
`MinaWrapDeferredWeld` §5 exhibits the disagreement on the real block's own bytes.

**What broke:** any caller that fed this function three challenges positionally is now feeding
different slots. There is exactly one such shape in the tree and it was this file's own
`WIRE_539508`, corrected below; the transitional duplicate
`MinaWrapDeferred.publicInputWordsCorrected` is DELETED rather than kept beside this. -/
def publicInputWords (w : WireWords) (d : DeferredWords) : List Nat :=
  [d.cip, d.b, d.zetaToSrsLength, d.zetaToDomainSize, d.perm,
   w.beta, w.gamma, w.alpha, w.zeta, d.xi,
   w.spongeDigest, w.word11, w.word12]
  ++ w.bpChallenges
  ++ [w.branchData]
  ++ List.replicate 10 0

/-- **`publicCommOf`** — `Σ (−publicᵢ)·Lᵢ + srs.h`, the 40-point Lagrange MSM of `verifier.rs:850-871`,
as a function of the words rather than of one block's literals. -/
def publicCommOf (words : List Nat) : Pt :=
  padd (msmComm ((words.map (fun x => (qN - x % qN) % qN)).zip LAGRANGE)) SRS_H

/-- ⚑ **PARAMETERISING DID NOT CHANGE THE OBJECT.** At the pinned words `publicCommOf` IS rung 5e's
`publicComm` — the two terms are equal after delta-unfolding, so `publicComm_reproduces_kimchi` and
`publicComm_is_the_transcript_preimage` transfer without being re-proved.

⚑ Deliberately `unfold` and not `decide`: this must close SYNTACTICALLY. A `decide` here would run
40 × 255-bit ladders in the kernel (~15 s, by rung 5e's own measurement) to establish something that
is true by definition, and paying the 40-ladder cost twice is exactly what parameterising is for.

⚑ And the closing `rfl` is load-bearing, not decoration: `unfold` REWRITES, it does not close. Left
off, this reported `unsolved goals` and Lean recovered with `sorryAx` — a theorem that looks proved
and is not. By the time `rfl` runs both sides are the SAME TERM, so it is syntactic and instant; it
never reaches the MSM. -/
theorem publicCommOf_is_rung5e : publicCommOf PUBLIC_INPUT = publicComm := by
  unfold publicCommOf
    Dregg2.Circuit.Emit.MinaWrapPublicCommGate.publicComm
    Dregg2.Circuit.Emit.MinaWrapPublicCommGate.NEG_PUBLIC
  rfl

/-! ## §3 — THE CENSUS, on the pinned block.

`WIRE_539508` / `DEFERRED_539508` are PROJECTIONS out of `PUBLIC_INPUT` at the slots §2 claims. The
round trip is therefore definitional and is not evidence for the claim — it is exhibited only so the
structures are inhabited by real numbers and the width signature has something to run on. What tests
the claim is the extractor, and it has not been run. Said here rather than in a commit message. -/

/-- Read slot `i` of the pinned public input. -/
def w539508 (i : Nat) : Nat := PUBLIC_INPUT.getD i 0

/-- The 34 wire words of block 539508, as this layout locates them. -/
def WIRE_539508 : WireWords :=
  -- ⚑ β at slot 5, γ at 6, α′ at 7 — `to_data`'s order, MEASURED against the block's own binprot
  -- bytes in `MinaWrapDeferredWeld` §5. The three names used to be rotated here.
  { beta := w539508 5, gamma := w539508 6, alpha := w539508 7, zeta := w539508 8
    spongeDigest := w539508 10, word11 := w539508 11, word12 := w539508 12
    bpChallenges := (List.range 16).map (fun j => w539508 (13 + j))
    branchData := w539508 29 }

/-- The six deferred words of block 539508, as this layout locates them. -/
def DEFERRED_539508 : DeferredWords :=
  { cip := w539508 0, b := w539508 1, zetaToSrsLength := w539508 2,
    zetaToDomainSize := w539508 3, perm := w539508 4, xi := w539508 9 }

/-- The layout is total and reassembles the pinned forty. Definitional, and said to be so. -/
theorem layout_reassembles_the_pinned_words :
    publicInputWords WIRE_539508 DEFERRED_539508 = PUBLIC_INPUT := by decide

/-- …and it always has exactly forty slots, whatever it is fed, provided the challenge vector is the
sixteen the wire carries. A short `bpChallenges` would silently shorten the public input and shift
`branch_data` into a challenge slot. -/
theorem publicInputWords_length (w : WireWords) (d : DeferredWords)
    (h : w.bpChallenges.length = 16) : (publicInputWords w d).length = 40 := by
  simp [publicInputWords, h]

/-! ### §3a — the INDEPENDENT anchor: slots 11 and 12 carry the served header.

These two are NOT projections-and-back. `MinaStateHashWordGate.B539508.word11Gold`/`word12Gold` are
derived from the served `stateHash`, the proof's own accumulators and the pinned VK by a computation
that never reads `PUBLIC_INPUT`. So a slot map that put them anywhere else fails HERE. -/

/-- ⚑ **THE BLOCK IS AT SLOT 12, AND THE WRAP MESSAGE AT SLOT 11.** -/
theorem the_header_words_land_where_the_layout_says :
    (publicInputWords WIRE_539508 DEFERRED_539508).getD 12 0 = B539508.word12Gold
    ∧ (publicInputWords WIRE_539508 DEFERRED_539508).getD 11 0 = B539508.word11Gold := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **NON-VACUITY of that anchor**: the two digests are distinct, and neither appears at any OTHER
slot. Without this, "word 12 is at slot 12" is compatible with a constant list. -/
theorem the_header_words_are_at_no_other_slot :
    B539508.word12Gold ≠ B539508.word11Gold
    ∧ ((List.range 40).filter
        (fun i => PUBLIC_INPUT.getD i 0 == B539508.word12Gold)) = [12]
    ∧ ((List.range 40).filter
        (fun i => PUBLIC_INPUT.getD i 0 == B539508.word11Gold)) = [11] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### §3b — the WIDTH SIGNATURE: the instrument that catches a swapped slot.

A `ScalarChallenge` is 128 bits; a field element is ~255. On real data the two are never confusable,
so a layout that put a challenge where a field element belongs is caught by ARITHMETIC rather than by
reading the OCaml again. -/

/-- `2^128`. -/
def CHAL_BOUND : Nat := 340282366920938463463374607431768211456

/-- The slots this layout calls 128-bit `ScalarChallenge`s. -/
def CHAL_SLOTS : List Nat := [5, 6, 7, 8, 9] ++ (List.range 16).map (fun j => 13 + j)

/-- The slots this layout calls full `Fq` elements. -/
def FIELD_SLOTS : List Nat := [0, 1, 2, 3, 4, 10, 11, 12]

/-- ⚑⚑ **THE WIDTH SIGNATURE HOLDS, AND IT IS SHARP.** Every challenge slot is below `2^128`; every
field slot is above it. Twenty-one and eight slots, on the real block, with no overlap — so the
partition is not a coincidence of small numbers. -/
theorem the_width_signature_partitions_the_slots :
    (CHAL_SLOTS.all (fun i => decide (PUBLIC_INPUT.getD i 0 < CHAL_BOUND))) = true
    ∧ (FIELD_SLOTS.all (fun i => decide (CHAL_BOUND ≤ PUBLIC_INPUT.getD i 0))) = true
    ∧ CHAL_SLOTS.length = 21 ∧ FIELD_SLOTS.length = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The tail really is padding, and `branch_data` really is the small packed word — so the layout's
last eleven slots are not silently absorbing a real value. -/
theorem the_tail_is_padding_and_branch_data :
    PUBLIC_INPUT.getD 29 0 = 67
    ∧ ((List.range 10).all (fun j => PUBLIC_INPUT.getD (30 + j) 0 == 0)) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑ **SLOTS 2 AND 3 ARE EQUAL, AND NOTHING ELSE IS.** `zeta_to_srs_length = zeta_to_domain_size`
is what a Step `domain_log2 = 16` against `max_poly_size = 2^16` forces; that exactly one pair of
distinct slots coincides (outside the zero padding) makes it a signature of the layout rather than an
accident. -/
theorem the_two_zeta_powers_coincide_and_only_they_do :
    PUBLIC_INPUT.getD 2 0 = PUBLIC_INPUT.getD 3 0
    ∧ ((List.range 30).flatMap (fun i =>
         (List.range 30).filterMap (fun j =>
           if i < j && PUBLIC_INPUT.getD i 0 == PUBLIC_INPUT.getD j 0 then some (i, j) else none)))
       = [(2, 3)] := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### §3c — the layout READS every field.

Without this, `publicInputWords` could drop an argument and every theorem above would still hold. -/

/-- Bumping any one input field moves the output list. Stated as a list of concrete perturbations
rather than a quantifier so it is `decide`-checkable on the real inhabitant. -/
theorem publicInputWords_reads_every_field :
    let W := WIRE_539508; let D := DEFERRED_539508; let base := publicInputWords W D
    publicInputWords { W with alpha := W.alpha + 1 } D ≠ base
    ∧ publicInputWords { W with beta := W.beta + 1 } D ≠ base
    ∧ publicInputWords { W with gamma := W.gamma + 1 } D ≠ base
    ∧ publicInputWords { W with zeta := W.zeta + 1 } D ≠ base
    ∧ publicInputWords { W with spongeDigest := W.spongeDigest + 1 } D ≠ base
    ∧ publicInputWords { W with word11 := W.word11 + 1 } D ≠ base
    ∧ publicInputWords { W with word12 := W.word12 + 1 } D ≠ base
    ∧ publicInputWords { W with branchData := W.branchData + 1 } D ≠ base
    ∧ publicInputWords { W with bpChallenges := W.bpChallenges.set 0 0 } D ≠ base
    -- ⚑ the LAST challenge too: a fold that stopped early would pass the first control
    ∧ publicInputWords { W with bpChallenges := W.bpChallenges.set 15 0 } D ≠ base
    ∧ publicInputWords W { D with cip := D.cip + 1 } ≠ base
    ∧ publicInputWords W { D with b := D.b + 1 } ≠ base
    ∧ publicInputWords W { D with zetaToSrsLength := D.zetaToSrsLength + 1 } ≠ base
    ∧ publicInputWords W { D with zetaToDomainSize := D.zetaToDomainSize + 1 } ≠ base
    ∧ publicInputWords W { D with perm := D.perm + 1 } ≠ base
    ∧ publicInputWords W { D with xi := D.xi + 1 } ≠ base := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §4 — the MSM moves with the words.

`publicCommOf` is 40 × 255-bit RCB ladders. At rung 5e's measured kernel unit (0.19 s/ladder) that is
~15 s per instance as a PROOF TERM, and the two pins below were written that way and failed; they run
in the COMPILED evaluator instead, in milliseconds. The per-block path runs none of this in the
kernel either — see `Dregg2.Bridge.MinaWrapChallenges`. -/

/- ⚑ **A CHANGED WORD 12 CHANGES THE COMMITMENT.** So the served header is not merely *present* in
the preimage of slot 12; it reaches the point the transcript absorbs, and therefore every challenge
that descends from it. This is the one link that makes a re-labelled header falsifiable at all.

⚑ **A `#guard`, and the demotion is the point.** This was `by decide` and it FAILED — one 40-ladder
MSM is not a kernel proof term at this file's option budget, and raising `maxHeartbeats` to buy it
would be paying ~15 s (rung 5e's measured 0.19 s/ladder × 40) for an INSTANCE. That is precisely the
split `MinaStateHashWordGate` states in its own header: *the kernel's job is the CHECKER, the
differential's job is the INSTANCE.* Rung 5e already carries the kernel-side identity
(`publicComm_reproduces_kimchi`); this is a real-data pin and real-data pins here are compiled.

Compared with `projEqM` rather than tuple inequality, because these are PROJECTIVE points and
`(x, y, 1)` vs `(2x, 2y, 2)` is the same point. -/
#guard projEqM pN (publicCommOf (PUBLIC_INPUT.set 12 (B539508.word12Gold + 1)))
         PUBLIC_COMM_GOLD == false

/- …and the untampered words DO reproduce the gold, so the `#guard` above is a discrimination and
not a function that returns `false` on everything. -/
#guard projEqM pN (publicCommOf PUBLIC_INPUT) PUBLIC_COMM_GOLD == true

/-! ## §5 — THE RESIDUAL, stated so it cannot be mistaken for done.

`expandDeferred : WrapEvals → DeferredWords` **does not exist in this tree**, in Lean or in Rust
(`grep -rn expand_deferred metatheory/ bridge/` returns doc prose only). It is the whole distance
between this file and a per-block public input, and every input it needs is on the wire.

The interface the next lane implements:

```lean
structure WrapEvals where
  ftEval1 : Nat                 -- `prev_evals.ft_eval1`
  evals : List (Nat × Nat)      -- the 47 (ζ, ζω) pairs, in `es` order
  oldChals : List (List Nat)    -- `old_bulletproof_challenges`, 2 × 16
  zeta : Nat                    -- `deferred_values.plonk.zeta`
  spongeDigest : Nat            -- slot 10, the Fr-sponge SEED
  domainLog2 : Nat              -- `branch_data.domain_log2`

def expandDeferred (e : WrapEvals) : DeferredWords := …
```

`MinaRealBlockGate.cipR` already computes the `combined_inner_product` fold on the real block, and
`MinaWrapOpeningGate.bPoly` computes `b`. What is genuinely new is the `Fr`-sponge seeding and the
`derive_plonk` permutation scalar. -/

#assert_axioms branch_data_of_the_pinned_block
#assert_axioms publicCommOf_is_rung5e
#assert_axioms layout_reassembles_the_pinned_words
#assert_axioms publicInputWords_length
#assert_axioms the_header_words_land_where_the_layout_says
#assert_axioms the_header_words_are_at_no_other_slot
#assert_axioms the_width_signature_partitions_the_slots
#assert_axioms the_tail_is_padding_and_branch_data
#assert_axioms the_two_zeta_powers_coincide_and_only_they_do
#assert_axioms publicInputWords_reads_every_field

#print axioms the_width_signature_partitions_the_slots
#print axioms the_header_words_land_where_the_layout_says

end Dregg2.Bridge.MinaWrapPublicInput
