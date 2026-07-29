/-
# Dregg2.Circuit.Emit.MinaWrapSgCore — the shared objects of RUNG 5h.

Rung 5f (`MinaWrapOpeningGate`) proved the IPA opening relation (B) on Mina devnet block 539508
and named its second premise: statement **(A) `sg == ⟨s, srs.g⟩`**, the `2^15`-term SRS MSM.
Until 2026-07-28 that was asserted in Rust (`[gt8]`) and deferred in the kernel. This file and its
`MinaWrapSgChunk*` siblings discharge it.

## What is derived here rather than eaten

`SVEC` is **not** a fixture. It is `PastaIPA.sVec` applied to the block's own 15 IPA challenges —
the same `CHAL_F` that `MinaRealBlockTranscript` derives from the block's sponge and that
`MinaWrapOpeningGate.derived_ipa_challenges` ties to `endoMap ENDO_R` of the prechallenges. So the
`32768` scalars of the terminal MSM are computed in-kernel from `15` field elements, which is
exactly the compression `PastaIPA.deferral_compression` prices and `PastaIPA.sVec_eq_bPoly`
justifies. The only new DATA is `srs.g` itself (`MinaWrapSrsG`, 32768 points) and the 32 chunk
partials (`MinaWrapSgParts`), both emitted by the extractor from o1-labs' own objects.

## Why the evaluation looks like this

`PastaIpaFold.msmHorner_eq_msmN` is the identity: one shared doubling chain over the 255 bit
planes, one addition per set bit. `msmHornerM` below is that function with `+` replaced by
`PastaCurveComplete.rcbAddM` and `0` by `Oproj`, term for term — `bitPassM`/`hornerAuxM`/
`msmHornerM` mirror `bitPass`/`hornerAux`/`msmHorner`. The transport from the abstract statement
to this evaluation is the SAME inherited RCB residual (RCB'15 Thm 1) that rungs 5a–5f carry; no
new assumption.

The generator FOLD (`PastaIpaFold.msm_sVec_eq_fold`) is the right structural statement about this
object and is **not** what evaluates it: it costs `2^15 − 1` scalar multiplications against the
naive `2^15`, i.e. it saves one. See §4 of `PastaIpaFold` and §6.1 of
`docs/MINA-REAL-BLOCK-GATE.md`.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`.
-/
import Dregg2.Circuit.Emit.MinaWrapSrsG
import Dregg2.Circuit.Emit.MinaWrapSgParts
import Dregg2.Circuit.Emit.PastaIpaFold
import Dregg2.Circuit.Emit.MinaWrapOpeningGate

namespace Dregg2.Circuit.Emit.MinaWrapSgCore

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (CHAL CHAL_F)
open Dregg2.Circuit.Emit.MinaWrapSrsG (SRS_G)
open Dregg2.Circuit.Emit.MinaWrapSgParts (PARTS SG)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 0

abbrev Pt := Nat × Nat × Nat

/-! ## §1 — The scalars, derived in-kernel from the 15 carried challenges. -/

/-- The `2^15` scalars of the terminal MSM, as `PastaIPA.sVec` of the block's own IPA challenges.
`sVec_eq_bPoly` says this list IS the coefficient vector of `b(X) = ∏_j (1 + c_j X^{2^…})`, which
is `b_poly_coefficients` — the vector o1-labs' `SRS::verify` builds at `ipa.rs`. -/
def SVEC : List Nat := (Dregg2.Circuit.Emit.PastaIPA.sVec CHAL_F).map ZMod.val

/-! ## §2 — The kernel evaluator: `PastaIpaFold.msmHorner` over the RCB complete add. -/

/-- One bit plane over the RCB add: fold in the points whose scalar has bit `i` set.
Mirror of `PastaIpaFold.bitPass`. -/
def bitPassM (m b3 i : Nat) (as : List Nat) (ps : List Pt) (acc : Pt) : Pt :=
  (as.zip ps).foldl (fun a ap => if ap.1.testBit i then rcbAddM m b3 a ap.2 else a) acc

/-- The Horner scan over bit indices, MSB first. Mirror of `PastaIpaFold.hornerAux`. -/
def hornerAuxM (m b3 : Nat) (as : List Nat) (ps : List Pt) (idxs : List Nat) (acc : Pt) : Pt :=
  idxs.foldl (fun a i => bitPassM m b3 i as ps (rcbAddM m b3 a a)) acc

/-- `⟨a, P⟩` by ONE doubling chain. Mirror of `PastaIpaFold.msmHorner`. -/
def msmHornerM (m b3 nbits : Nat) (as : List Nat) (ps : List Pt) : Pt :=
  hornerAuxM m b3 as ps (List.range nbits).reverse Oproj

/-! ## §3 — The chunking, INDEX-PINNED.

A per-chunk theorem that only said "this point is a partial and the partials re-sum to `sg`"
would be insensitive to which SLICE each partial belongs to — a group sum does not remember its
order. So `chunkS k` and `chunkG k` are both cut at `1024 * k` from the SAME `k`, the statement
names the slice, and `chunks_partition_*` says the 32 slices reassemble the whole list in order. -/

/-- **512 terms per bit-plane fold, two folds per chunk.** Two independent measured walls set
this. (i) Peak elaborator RSS tracks the largest single `decide` — ~8 GB at 512 terms. (ii) The
kernel's `whnf` builds the `foldl` accumulator as a THUNK CHAIN of depth `nbits × terms`, and at
`255 × 1024 ≈ 2.6 · 10^5` frames it overflows the C stack outright (`Stack overflow detected.
Aborting.`, exit 134; `ulimit -s unlimited` does not help — Lean checks its own `--tstack`).
`255 × 512` is under it. So a 1024-term chunk is evaluated as TWO 512-term folds added together:
two sibling sub-terms of depth 1.3·10^5 rather than one nested term of depth 2.6·10^5. -/
def CH : Nat := 1024

/-- Half-chunk width: 512, `2 * 32 = 64` halves over the whole SRS. -/
def HW : Nat := 512

/-- The scalars of half `i`: indices `[512i, 512i+512)`. -/
def halfS (i : Nat) : List Nat := (SVEC.drop (HW * i)).take HW

/-- The generators of half `i`: indices `[512i, 512i+512)`, the SAME `i`. -/
def halfG (i : Nat) : List Pt := (SRS_G.drop (HW * i)).take HW

/-- **The chunk claim**, for one `k`: the MSM over indices `[1024k, 1024k+1024)` — assembled from
halves `2k` and `2k+1`, which are indices `[1024k, 1024k+512)` and `[1024k+512, 1024k+1024)` — is
the `k`-th partial arkworks' `msm_bigint` produced for that same slice. The index appears in the
STATEMENT: a per-chunk theorem that only said "P is a partial and the partials re-sum to sg"
would be blind to which slice each partial came from, since a group sum forgets its order. -/
def ChunkOk (k : Nat) : Prop :=
  projEqM pN
    (rcbAddM pN curveB3
      (msmHornerM pN curveB3 255 (halfS (2 * k)) (halfG (2 * k)))
      (msmHornerM pN curveB3 255 (halfS (2 * k + 1)) (halfG (2 * k + 1))))
    (PARTS.getD k Oproj) = true

instance (k : Nat) : Decidable (ChunkOk k) := by unfold ChunkOk; infer_instance

/-! ## §4 — Shape facts, all in-kernel, all cheap (no group operations). -/

/-- The SRS has `2^15` generators — the `k = 15` the block's opening proof carries. -/
theorem srs_g_length : SRS_G.length = 32768 := by decide

/-- The s-vector derived from 15 challenges has `2^15` entries (`PastaIPA.sVec_length`, here
CONCRETELY, on the block's own challenges). -/
theorem svec_length : SVEC.length = 32768 := by decide

/-- 15 challenges. -/
theorem chal_length : CHAL.length = 15 := by decide

/-- 32 chunk partials. -/
theorem parts_length : PARTS.length = 32 := by decide

/-- Every scalar fits the 255-bit budget — the hypothesis `msmHorner_eq_msmN` needs. -/
theorem svec_fits_255 : SVEC.all (fun a => a < 2 ^ 255) = true := by decide

/-- **`chunks_partition_scalars`** — the 32 slices reassemble `SVEC` exactly, in order. Nothing is
skipped, nothing is counted twice, and no chunk is at the wrong offset. Via the generic
`PastaIpaFold.flatMap_chunks`, so no `2^15`-element list equality is ever `decide`d. -/
theorem halves_partition_scalars : ((List.range 64).flatMap halfS) = SVEC :=
  Dregg2.Circuit.Emit.PastaIpaFold.flatMap_chunks HW 64 SVEC (by rw [svec_length]; rfl)

/-- **`halves_partition_generators`** — likewise for `srs.g`. The 64 halves the 32 chunk theorems
consume are exactly `srs.g`, in order: nothing skipped, nothing counted twice, no wrong offset. -/
theorem halves_partition_generators : ((List.range 64).flatMap halfG) = SRS_G :=
  Dregg2.Circuit.Emit.PastaIpaFold.flatMap_chunks HW 64 SRS_G (by rw [srs_g_length]; rfl)

/-- Each half really is 512 long (a ragged tail would make the partition look green while a slice
silently went short). -/
theorem halves_are_full (i : Nat) (hi : i < 64) :
    (halfS i).length = 512 ∧ (halfG i).length = 512 :=
  ⟨Dregg2.Circuit.Emit.PastaIpaFold.chunk_length HW 64 i SVEC (by rw [svec_length]; rfl) hi,
   Dregg2.Circuit.Emit.PastaIpaFold.chunk_length HW 64 i SRS_G (by rw [srs_g_length]; rfl) hi⟩

/-- The two halves chunk `k` consumes are halves `2k` and `2k+1`, i.e. exactly the SRS indices
`[1024k, 1024k+1024)` — so the chunk index in `ChunkOk k` and the partial index in `PARTS` are
the same `k`, and the 32 chunks tile the 64 halves. -/
theorem chunk_halves_are_contiguous (k : Nat) :
    HW * (2 * k) = CH * k ∧ HW * (2 * k + 1) = CH * k + 512 := by
  constructor <;> simp [HW, CH] <;> ring

/-- Every generator is a real Pallas point. -/
theorem srs_g_on_curve : SRS_G.all (projOnCurveM pN curveB) = true := by decide

/-- Every chunk partial is a real Pallas point, and none is the point at infinity. -/
theorem parts_on_curve :
    (PARTS.all (projOnCurveM pN curveB) && PARTS.all (fun P => !isInfM pN P)) = true := by decide

/-- `sg` is a real Pallas point, and it is the `sg` rung 5f used. -/
theorem sg_is_the_openings_sg :
    projOnCurveM pN curveB SG = true
      ∧ projEqM pN SG Dregg2.Circuit.Emit.MinaWrapOpeningGate.SG = true := by
  constructor <;> decide

/-! ## §5 — The assembly: the 32 partials re-sum to `sg`. -/

/-- The 32 chunk partials, added up left to right over the RCB complete add. -/
def partsSum : Pt := PARTS.foldl (fun acc P => rcbAddM pN curveB3 acc P) Oproj

/-- **`parts_sum_is_sg`** — the partials re-sum to the block's own `sg`. With the 32 `ChunkOk`
theorems (`MinaWrapSgChunk0..3`) this is statement (A). -/
theorem parts_sum_is_sg : projEqM pN partsSum SG = true := by decide

/-- Anti-vacuity: perturb ONE partial and the re-sum breaks. -/
theorem parts_sum_tamper :
    projEqM pN (((PARTS.set 7 (PARTS.getD 8 Oproj)).foldl
      (fun acc P => rcbAddM pN curveB3 acc P) Oproj)) SG = false := by decide

#assert_axioms srs_g_length
#assert_axioms svec_length
#assert_axioms chal_length
#assert_axioms parts_length
#assert_axioms svec_fits_255
#assert_axioms halves_partition_scalars
#assert_axioms halves_partition_generators
#assert_axioms halves_are_full
#assert_axioms chunk_halves_are_contiguous
#assert_axioms srs_g_on_curve
#assert_axioms parts_on_curve
#assert_axioms sg_is_the_openings_sg
#assert_axioms parts_sum_is_sg
#assert_axioms parts_sum_tamper

end Dregg2.Circuit.Emit.MinaWrapSgCore
