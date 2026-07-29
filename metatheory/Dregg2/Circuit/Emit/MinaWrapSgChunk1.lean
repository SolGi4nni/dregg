/-
# Dregg2.Circuit.Emit.MinaWrapSgChunk1 — rung 5h, chunks 8..15 of 32.

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

namespace Dregg2.Circuit.Emit.MinaWrapSgChunk1

open Dregg2.Circuit.Emit.MinaWrapSgCore (ChunkOk)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Chunk 8: SRS indices `[8192, 9216)`, halves 16 and 17. -/
theorem chunk_08 : ChunkOk 8 := by decide

/-- Chunk 9: SRS indices `[9216, 10240)`, halves 18 and 19. -/
theorem chunk_09 : ChunkOk 9 := by decide

/-- Chunk 10: SRS indices `[10240, 11264)`, halves 20 and 21. -/
theorem chunk_10 : ChunkOk 10 := by decide

/-- Chunk 11: SRS indices `[11264, 12288)`, halves 22 and 23. -/
theorem chunk_11 : ChunkOk 11 := by decide

/-- Chunk 12: SRS indices `[12288, 13312)`, halves 24 and 25. -/
theorem chunk_12 : ChunkOk 12 := by decide

/-- Chunk 13: SRS indices `[13312, 14336)`, halves 26 and 27. -/
theorem chunk_13 : ChunkOk 13 := by decide

/-- Chunk 14: SRS indices `[14336, 15360)`, halves 28 and 29. -/
theorem chunk_14 : ChunkOk 14 := by decide

/-- Chunk 15: SRS indices `[15360, 16384)`, halves 30 and 31. -/
theorem chunk_15 : ChunkOk 15 := by decide

#assert_axioms chunk_08
#assert_axioms chunk_09
#assert_axioms chunk_10
#assert_axioms chunk_11
#assert_axioms chunk_12
#assert_axioms chunk_13
#assert_axioms chunk_14
#assert_axioms chunk_15

end Dregg2.Circuit.Emit.MinaWrapSgChunk1
