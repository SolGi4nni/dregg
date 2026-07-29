/-
# Dregg2.Circuit.Emit.MinaWrapSgChunk0 — rung 5h, chunks 0..7 of 32.

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

namespace Dregg2.Circuit.Emit.MinaWrapSgChunk0

open Dregg2.Circuit.Emit.MinaWrapSgCore (ChunkOk)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Chunk 0: SRS indices `[0, 1024)`, halves 0 and 1. -/
theorem chunk_00 : ChunkOk 0 := by decide

/-- Chunk 1: SRS indices `[1024, 2048)`, halves 2 and 3. -/
theorem chunk_01 : ChunkOk 1 := by decide

/-- Chunk 2: SRS indices `[2048, 3072)`, halves 4 and 5. -/
theorem chunk_02 : ChunkOk 2 := by decide

/-- Chunk 3: SRS indices `[3072, 4096)`, halves 6 and 7. -/
theorem chunk_03 : ChunkOk 3 := by decide

/-- Chunk 4: SRS indices `[4096, 5120)`, halves 8 and 9. -/
theorem chunk_04 : ChunkOk 4 := by decide

/-- Chunk 5: SRS indices `[5120, 6144)`, halves 10 and 11. -/
theorem chunk_05 : ChunkOk 5 := by decide

/-- Chunk 6: SRS indices `[6144, 7168)`, halves 12 and 13. -/
theorem chunk_06 : ChunkOk 6 := by decide

/-- Chunk 7: SRS indices `[7168, 8192)`, halves 14 and 15. -/
theorem chunk_07 : ChunkOk 7 := by decide

#assert_axioms chunk_00
#assert_axioms chunk_01
#assert_axioms chunk_02
#assert_axioms chunk_03
#assert_axioms chunk_04
#assert_axioms chunk_05
#assert_axioms chunk_06
#assert_axioms chunk_07

end Dregg2.Circuit.Emit.MinaWrapSgChunk0
