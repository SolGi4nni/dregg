/-
# Dregg2.Circuit.Emit.MinaWrapSgChunk2 — rung 5h, chunks 16..23 of 32.

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

namespace Dregg2.Circuit.Emit.MinaWrapSgChunk2

open Dregg2.Circuit.Emit.MinaWrapSgCore (ChunkOk)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Chunk 16: SRS indices `[16384, 17408)`, halves 32 and 33. -/
theorem chunk_16 : ChunkOk 16 := by decide

/-- Chunk 17: SRS indices `[17408, 18432)`, halves 34 and 35. -/
theorem chunk_17 : ChunkOk 17 := by decide

/-- Chunk 18: SRS indices `[18432, 19456)`, halves 36 and 37. -/
theorem chunk_18 : ChunkOk 18 := by decide

/-- Chunk 19: SRS indices `[19456, 20480)`, halves 38 and 39. -/
theorem chunk_19 : ChunkOk 19 := by decide

/-- Chunk 20: SRS indices `[20480, 21504)`, halves 40 and 41. -/
theorem chunk_20 : ChunkOk 20 := by decide

/-- Chunk 21: SRS indices `[21504, 22528)`, halves 42 and 43. -/
theorem chunk_21 : ChunkOk 21 := by decide

/-- Chunk 22: SRS indices `[22528, 23552)`, halves 44 and 45. -/
theorem chunk_22 : ChunkOk 22 := by decide

/-- Chunk 23: SRS indices `[23552, 24576)`, halves 46 and 47. -/
theorem chunk_23 : ChunkOk 23 := by decide

#assert_axioms chunk_16
#assert_axioms chunk_17
#assert_axioms chunk_18
#assert_axioms chunk_19
#assert_axioms chunk_20
#assert_axioms chunk_21
#assert_axioms chunk_22
#assert_axioms chunk_23

end Dregg2.Circuit.Emit.MinaWrapSgChunk2
