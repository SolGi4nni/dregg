/-
# Dregg2.Circuit.Emit.MinaWrapSgChunk3 — rung 5h, chunks 24..31 of 32.

Each theorem says: the terminal MSM `⟨s, srs.g⟩` RESTRICTED to indices `[1024k, 1024k+1024)` —
assembled from halves `2k` and `2k+1` — is the partial arkworks' own `msm_bigint` produced for
that same slice. `MinaWrapSgCore.halves_partition_*` says the 64 halves reassemble `srs.g` and
the derived s-vector in order; `MinaWrapSgCore.parts_sum_is_sg` says the 32 partials re-sum to the
block's `sg`. Together: **statement (A) of `SRS::verify`, in the Lean kernel, on Mina devnet
block 539508.**

Split across four modules so the heavy `decide`s can run concurrently and so peak elaborator RSS
tracks ONE chunk. `Elab.async false` keeps the theorems within a module SERIAL — parallel command
elaboration multiplies the peak instead of bounding it.

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`.
-/
import Dregg2.Circuit.Emit.MinaWrapSgCore

namespace Dregg2.Circuit.Emit.MinaWrapSgChunk3

open Dregg2.Circuit.Emit.MinaWrapSgCore (ChunkOk)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Chunk 24: SRS indices `[24576, 25600)`, halves 48 and 49. -/
theorem chunk_24 : ChunkOk 24 := by decide

/-- Chunk 25: SRS indices `[25600, 26624)`, halves 50 and 51. -/
theorem chunk_25 : ChunkOk 25 := by decide

/-- Chunk 26: SRS indices `[26624, 27648)`, halves 52 and 53. -/
theorem chunk_26 : ChunkOk 26 := by decide

/-- Chunk 27: SRS indices `[27648, 28672)`, halves 54 and 55. -/
theorem chunk_27 : ChunkOk 27 := by decide

/-- Chunk 28: SRS indices `[28672, 29696)`, halves 56 and 57. -/
theorem chunk_28 : ChunkOk 28 := by decide

/-- Chunk 29: SRS indices `[29696, 30720)`, halves 58 and 59. -/
theorem chunk_29 : ChunkOk 29 := by decide

/-- Chunk 30: SRS indices `[30720, 31744)`, halves 60 and 61. -/
theorem chunk_30 : ChunkOk 30 := by decide

/-- Chunk 31: SRS indices `[31744, 32768)`, halves 62 and 63. -/
theorem chunk_31 : ChunkOk 31 := by decide

#assert_axioms chunk_24
#assert_axioms chunk_25
#assert_axioms chunk_26
#assert_axioms chunk_27
#assert_axioms chunk_28
#assert_axioms chunk_29
#assert_axioms chunk_30
#assert_axioms chunk_31

end Dregg2.Circuit.Emit.MinaWrapSgChunk3
