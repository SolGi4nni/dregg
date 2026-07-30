/-
# Dregg2.Bridge.MinaStateHashRealBlock — ⚑ **THE REALITY GATE FOR A TIP'S IDENTITY.**

`Bridge.MinaStateHashDerive` re-derives `state_hash` from the wire bytes. Every PRIMITIVE it uses is
anchored outside this repo — both Poseidon salts against openmina's own pinned regression constants,
SHA-256 against `hashlib` at two blocks, Poseidon against six o1js golds. What none of that anchors
is the **ORDER**: ~30 field elements and ~1,400 packed bits, assembled across four places where
`Body.to_input` deliberately disagrees with the binprot record order, plus two leaf facts (the
253-bit VRF truncation and the big-endian ledger hash into SHA-256) that a structure-level read gets
wrong. This module is where the order meets a real chain.

## ⚑ It takes NO ORACLE, and that is the point

`state_hash` is not on Mina's peer-to-peer wire — every node computes it, which is why
`get_best_tip` never sends one. But `previous_state_hash` IS on the wire, in the clear, as the first
32 bytes of every `Protocol_state.Value`. So for a CONSECUTIVE pair:

```text
    deriveStateHash(block_N)  =  block_{N+1}.previous_state_hash
```

Both sides came from the daemon. No transcription of ours is on either side, no explorer is asked,
nothing is compiled but this. A comparison against a value we or openmina computed would be a
differential against another implementation; this is a differential against **the chain**.

If any of the four order traps is wrong, or the VRF is read as 256 bits, or the ledger hash goes
into SHA-256 little-endian, the left side is a different 254-bit number and this file goes red.

## ⚑ And it catches what the 540186 gate structurally cannot

`MinaBinprotRealBlock` checks that the decoder lands on byte 1544 and that the eight fields `select`
reads have openmina's values. A field-order slip *inside* `Blockchain_state` — two adjacent field
elements swapped, say — passes both: the byte count is identical and `select` reads none of them.
It moves the hash preimage. This gate sees it.

## Kernel, and what that costs

⚑ Every theorem below is kernel `decide` — `native_decide` appears nowhere. The generator used to
emit it; that was a tool left behind when the modules were converted on 2026-07-30, which is how a
retired pattern reintroduces itself. Each derivation costs ~9 s of kernel (measured), so the file
states ONE derivation per theorem and gets both refusal polarities for free by instantiating
`MinaStateHashDerive.the_guard_accepts_the_derived_and_refuses_the_rest` — a `∀` over every wrong
hash, which is strictly stronger than sampling two neighbours and costs nothing.

⚑ Only the 1,544-byte PROTOCOL STATE is embedded, not the whole `get_best_tip` payload. The payload
is the protocol state followed by the rest of the block and the proof — 108 KB and 312 KB on the
captured pair — and embedding that produced a 17,600-line file that heartbeat out at `whnf` during
elaboration, before a single theorem ran.

Captured by `bridge/tools/mina-consecutive-pair.py` over Mina's own protocol
(`TCP → pnet → Noise XX → yamux → coda/rpcs/0.0.1 → get_best_tip v2`). REGENERATE, do not edit.
-/
import Dregg2.Bridge.MinaBinprotRealBlock

set_option autoImplicit false
-- ⚑ MEASURED: the Poseidon reductions exhaust 40000 with "maximum recursion depth has been
-- reached" — a limit, not a timeout. Same value as `MinaStateHashDerive`, for the same reason.
set_option maxRecDepth 1000000

namespace Dregg2.Bridge.MinaStateHashRealBlock

open Dregg2.Bridge.MinaBinprot
open Dregg2.Bridge.MinaStateHashDerive

/-- The parent block's `Protocol_state.Value.Stable.V2`, 1544 bytes, height 540221. -/
def devnetParent : List Nat := [
  222, 153, 67, 234, 219, 77, 237, 152, 99, 39, 94, 246, 107, 87, 213, 109, 55, 205, 66, 29, 85, 247, 40, 190,
  159, 8, 238, 17, 118, 251, 105, 56, 145, 168, 234, 178, 20, 192, 233, 236, 226, 167, 123, 12, 229, 92, 190, 144,
  63, 107, 76, 239, 59, 58, 122, 149, 210, 237, 217, 24, 167, 147, 38, 20, 145, 200, 4, 64, 106, 119, 63, 75,
  181, 214, 117, 197, 70, 231, 212, 3, 38, 186, 65, 207, 218, 135, 155, 217, 208, 108, 104, 182, 88, 85, 29, 50,
  32, 196, 33, 176, 194, 198, 93, 22, 254, 242, 53, 211, 147, 90, 125, 39, 166, 184, 221, 214, 77, 150, 228, 203,
  173, 128, 47, 79, 189, 176, 80, 34, 83, 32, 44, 113, 19, 125, 60, 191, 25, 152, 14, 21, 244, 100, 203, 219,
  242, 52, 125, 157, 36, 180, 178, 17, 132, 19, 240, 65, 15, 148, 239, 199, 133, 67, 198, 212, 244, 50, 250, 15,
  93, 113, 203, 190, 137, 131, 211, 254, 96, 63, 150, 231, 219, 37, 170, 193, 169, 40, 141, 75, 16, 239, 130, 180,
  164, 43, 252, 207, 248, 128, 20, 78, 119, 5, 89, 162, 155, 47, 112, 166, 125, 240, 178, 82, 236, 43, 2, 12,
  195, 185, 104, 102, 159, 184, 205, 94, 228, 57, 112, 252, 137, 254, 117, 202, 223, 88, 74, 184, 8, 249, 119, 60,
  89, 0, 101, 235, 201, 190, 38, 208, 251, 47, 41, 143, 74, 146, 90, 166, 91, 40, 51, 87, 186, 106, 4, 201,
  156, 73, 226, 219, 100, 71, 43, 216, 236, 237, 36, 56, 252, 81, 155, 31, 172, 146, 214, 239, 158, 172, 189, 78,
  80, 22, 53, 185, 213, 30, 93, 124, 116, 20, 86, 248, 103, 32, 115, 18, 65, 168, 40, 2, 115, 207, 198, 194,
  22, 104, 253, 123, 198, 197, 135, 208, 204, 29, 71, 25, 139, 13, 81, 154, 135, 47, 0, 89, 139, 241, 44, 233,
  243, 47, 47, 61, 116, 54, 239, 84, 253, 180, 195, 72, 118, 131, 216, 146, 15, 41, 71, 25, 139, 13, 81, 154,
  135, 47, 0, 89, 139, 241, 44, 233, 243, 47, 47, 61, 116, 54, 239, 84, 253, 180, 195, 72, 118, 131, 216, 146,
  15, 41, 108, 198, 112, 229, 38, 30, 251, 217, 204, 72, 197, 136, 205, 162, 244, 187, 41, 39, 208, 89, 192, 175,
  208, 112, 201, 142, 214, 148, 46, 102, 65, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
  0, 1, 108, 218, 104, 28, 205, 118, 139, 149, 136, 21, 26, 179, 165, 50, 164, 164, 234, 172, 82, 42, 186, 137,
  65, 116, 136, 89, 221, 40, 120, 15, 85, 20, 108, 218, 104, 28, 205, 118, 139, 149, 136, 21, 26, 179, 165, 50,
  164, 164, 234, 172, 82, 42, 186, 137, 65, 116, 136, 89, 221, 40, 120, 15, 85, 20, 196, 90, 191, 233, 216, 199,
  138, 47, 45, 193, 191, 14, 170, 62, 116, 63, 218, 24, 94, 13, 56, 10, 57, 12, 245, 65, 175, 14, 102, 203,
  239, 16, 71, 25, 139, 13, 81, 154, 135, 47, 0, 89, 139, 241, 44, 233, 243, 47, 47, 61, 116, 54, 239, 84,
  253, 180, 195, 72, 118, 131, 216, 146, 15, 41, 2, 195, 240, 72, 119, 27, 93, 59, 155, 206, 85, 147, 59, 210,
  81, 28, 114, 227, 177, 195, 25, 229, 80, 14, 159, 8, 246, 253, 28, 36, 6, 46, 108, 198, 112, 229, 38, 30,
  251, 217, 204, 72, 197, 136, 205, 162, 244, 187, 41, 39, 208, 89, 192, 175, 208, 112, 201, 142, 214, 148, 46, 102,
  65, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 51, 87, 186, 106, 4, 201,
  156, 73, 226, 219, 100, 71, 43, 216, 236, 237, 36, 56, 252, 81, 155, 31, 172, 146, 214, 239, 158, 172, 189, 78,
  80, 22, 108, 218, 104, 28, 205, 118, 139, 149, 136, 21, 26, 179, 165, 50, 164, 164, 234, 172, 82, 42, 186, 137,
  65, 116, 136, 89, 221, 40, 120, 15, 85, 20, 252, 0, 224, 171, 199, 76, 20, 0, 0, 0, 1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252, 192, 39, 239, 180, 159, 1,
  0, 0, 32, 216, 211, 24, 175, 172, 56, 92, 4, 242, 159, 57, 54, 135, 153, 20, 74, 205, 48, 177, 160, 248,
  147, 3, 209, 34, 108, 80, 119, 175, 23, 144, 204, 253, 61, 62, 8, 0, 56, 3, 11, 5, 3, 1, 2, 3,
  4, 6, 4, 4, 3, 2, 32, 236, 111, 131, 22, 21, 165, 189, 69, 67, 206, 55, 247, 201, 23, 44, 147, 60,
  158, 90, 190, 5, 148, 38, 236, 233, 220, 187, 22, 180, 97, 0, 0, 252, 232, 39, 206, 189, 208, 177, 253, 21,
  0, 253, 202, 42, 6, 0, 254, 228, 27, 0, 253, 110, 248, 12, 0, 22, 8, 72, 6, 84, 31, 0, 125, 80,
  152, 253, 225, 111, 201, 81, 195, 128, 148, 164, 245, 51, 228, 222, 208, 74, 70, 224, 51, 42, 91, 111, 58, 252,
  232, 113, 123, 52, 53, 145, 236, 21, 26, 4, 192, 233, 101, 239, 20, 130, 55, 39, 13, 11, 254, 199, 214, 158,
  24, 58, 192, 41, 19, 216, 78, 226, 234, 7, 180, 225, 235, 96, 108, 51, 244, 183, 202, 143, 227, 161, 134, 250,
  124, 215, 121, 247, 150, 66, 141, 196, 135, 236, 2, 127, 189, 164, 12, 139, 16, 96, 61, 115, 199, 73, 166, 24,
  20, 216, 235, 243, 194, 206, 70, 140, 229, 138, 159, 121, 58, 138, 223, 161, 12, 154, 225, 176, 244, 44, 208, 73,
  79, 195, 96, 180, 216, 169, 84, 33, 254, 184, 15, 197, 221, 10, 202, 10, 199, 91, 172, 218, 82, 79, 78, 68,
  197, 109, 145, 246, 90, 102, 233, 162, 37, 152, 174, 250, 3, 117, 231, 37, 52, 173, 58, 252, 232, 153, 235, 178,
  120, 134, 247, 21, 225, 8, 239, 234, 199, 123, 230, 227, 24, 49, 110, 5, 51, 42, 218, 190, 121, 60, 250, 143,
  10, 245, 199, 234, 202, 80, 83, 249, 4, 89, 117, 5, 245, 171, 34, 82, 125, 128, 79, 167, 34, 153, 39, 195,
  131, 87, 235, 156, 66, 135, 133, 13, 60, 45, 95, 17, 77, 239, 234, 64, 72, 28, 86, 27, 222, 153, 67, 234,
  219, 77, 237, 152, 99, 39, 94, 246, 107, 87, 213, 109, 55, 205, 66, 29, 85, 247, 40, 190, 159, 8, 238, 17,
  118, 251, 105, 56, 254, 46, 9, 1, 2, 39, 155, 144, 1, 97, 85, 242, 253, 76, 74, 250, 117, 249, 149, 59,
  102, 164, 16, 54, 167, 138, 74, 208, 192, 235, 242, 200, 171, 70, 16, 18, 0, 113, 239, 103, 50, 192, 221, 170,
  64, 148, 6, 255, 153, 64, 157, 105, 144, 121, 105, 11, 237, 172, 112, 102, 51, 57, 148, 98, 112, 103, 224, 93,
  37, 0, 113, 239, 103, 50, 192, 221, 170, 64, 148, 6, 255, 153, 64, 157, 105, 144, 121, 105, 11, 237, 172, 112,
  102, 51, 57, 148, 98, 112, 103, 224, 93, 37, 0, 1, 254, 34, 1, 254, 228, 27, 7, 254, 112, 8, 0, 252,
  128, 24, 169, 196, 142, 1, 0, 0]

/-- The CHILD block's `Protocol_state.Value.Stable.V2`, 1544 bytes, height 540222. Its first 32 bytes are the parent's identity, as the daemon computed it. -/
def devnetChild : List Nat := [
  76, 189, 100, 244, 186, 223, 88, 5, 204, 74, 247, 61, 83, 191, 224, 7, 245, 117, 214, 200, 227, 10, 239, 107,
  243, 12, 152, 117, 171, 88, 143, 18, 145, 168, 234, 178, 20, 192, 233, 236, 226, 167, 123, 12, 229, 92, 190, 144,
  63, 107, 76, 239, 59, 58, 122, 149, 210, 237, 217, 24, 167, 147, 38, 20, 99, 31, 7, 145, 71, 99, 43, 90,
  3, 67, 227, 132, 146, 135, 172, 157, 173, 133, 235, 15, 196, 166, 55, 237, 202, 120, 211, 184, 185, 134, 69, 11,
  32, 96, 59, 128, 253, 15, 169, 226, 116, 59, 82, 155, 248, 146, 79, 215, 242, 209, 172, 197, 158, 96, 212, 37,
  109, 178, 191, 11, 54, 38, 242, 111, 224, 32, 44, 113, 19, 125, 60, 191, 25, 152, 14, 21, 244, 100, 203, 219,
  242, 52, 125, 157, 36, 180, 178, 17, 132, 19, 240, 65, 15, 148, 239, 199, 133, 67, 99, 37, 21, 94, 73, 120,
  52, 91, 163, 189, 31, 210, 98, 28, 191, 144, 34, 21, 62, 174, 30, 9, 86, 100, 204, 8, 96, 145, 182, 229,
  0, 53, 252, 207, 248, 128, 20, 78, 119, 5, 89, 162, 155, 47, 112, 166, 125, 240, 178, 82, 236, 43, 2, 12,
  195, 185, 104, 102, 159, 184, 205, 94, 228, 57, 112, 252, 137, 254, 117, 202, 223, 88, 74, 184, 8, 249, 119, 60,
  89, 0, 101, 235, 201, 190, 38, 208, 251, 47, 41, 143, 74, 146, 90, 166, 91, 40, 51, 87, 186, 106, 4, 201,
  156, 73, 226, 219, 100, 71, 43, 216, 236, 237, 36, 56, 252, 81, 155, 31, 172, 146, 214, 239, 158, 172, 189, 78,
  80, 22, 53, 185, 213, 30, 93, 124, 116, 20, 86, 248, 103, 32, 115, 18, 65, 168, 40, 2, 115, 207, 198, 194,
  22, 104, 253, 123, 198, 197, 135, 208, 204, 29, 71, 25, 139, 13, 81, 154, 135, 47, 0, 89, 139, 241, 44, 233,
  243, 47, 47, 61, 116, 54, 239, 84, 253, 180, 195, 72, 118, 131, 216, 146, 15, 41, 71, 25, 139, 13, 81, 154,
  135, 47, 0, 89, 139, 241, 44, 233, 243, 47, 47, 61, 116, 54, 239, 84, 253, 180, 195, 72, 118, 131, 216, 146,
  15, 41, 108, 198, 112, 229, 38, 30, 251, 217, 204, 72, 197, 136, 205, 162, 244, 187, 41, 39, 208, 89, 192, 175,
  208, 112, 201, 142, 214, 148, 46, 102, 65, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
  0, 1, 108, 218, 104, 28, 205, 118, 139, 149, 136, 21, 26, 179, 165, 50, 164, 164, 234, 172, 82, 42, 186, 137,
  65, 116, 136, 89, 221, 40, 120, 15, 85, 20, 108, 218, 104, 28, 205, 118, 139, 149, 136, 21, 26, 179, 165, 50,
  164, 164, 234, 172, 82, 42, 186, 137, 65, 116, 136, 89, 221, 40, 120, 15, 85, 20, 196, 90, 191, 233, 216, 199,
  138, 47, 45, 193, 191, 14, 170, 62, 116, 63, 218, 24, 94, 13, 56, 10, 57, 12, 245, 65, 175, 14, 102, 203,
  239, 16, 71, 25, 139, 13, 81, 154, 135, 47, 0, 89, 139, 241, 44, 233, 243, 47, 47, 61, 116, 54, 239, 84,
  253, 180, 195, 72, 118, 131, 216, 146, 15, 41, 2, 195, 240, 72, 119, 27, 93, 59, 155, 206, 85, 147, 59, 210,
  81, 28, 114, 227, 177, 195, 25, 229, 80, 14, 159, 8, 246, 253, 28, 36, 6, 46, 108, 198, 112, 229, 38, 30,
  251, 217, 204, 72, 197, 136, 205, 162, 244, 187, 41, 39, 208, 89, 192, 175, 208, 112, 201, 142, 214, 148, 46, 102,
  65, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 51, 87, 186, 106, 4, 201,
  156, 73, 226, 219, 100, 71, 43, 216, 236, 237, 36, 56, 252, 81, 155, 31, 172, 146, 214, 239, 158, 172, 189, 78,
  80, 22, 108, 218, 104, 28, 205, 118, 139, 149, 136, 21, 26, 179, 165, 50, 164, 164, 234, 172, 82, 42, 186, 137,
  65, 116, 136, 89, 221, 40, 120, 15, 85, 20, 252, 0, 224, 171, 199, 76, 20, 0, 0, 0, 1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252, 0, 166, 244, 180, 159, 1,
  0, 0, 32, 237, 204, 242, 154, 152, 180, 124, 67, 27, 139, 164, 161, 13, 9, 210, 139, 59, 117, 180, 227, 230,
  160, 171, 123, 83, 230, 153, 71, 128, 50, 220, 172, 253, 62, 62, 8, 0, 56, 3, 11, 5, 3, 1, 2, 3,
  4, 6, 4, 4, 3, 3, 32, 250, 219, 252, 190, 247, 10, 43, 160, 97, 208, 246, 239, 69, 54, 142, 198, 120,
  175, 53, 44, 5, 23, 194, 134, 120, 200, 214, 62, 148, 99, 69, 0, 252, 232, 39, 206, 189, 208, 177, 253, 21,
  0, 253, 204, 42, 6, 0, 254, 228, 27, 0, 253, 112, 248, 12, 0, 22, 8, 72, 6, 84, 31, 0, 125, 80,
  152, 253, 225, 111, 201, 81, 195, 128, 148, 164, 245, 51, 228, 222, 208, 74, 70, 224, 51, 42, 91, 111, 58, 252,
  232, 113, 123, 52, 53, 145, 236, 21, 26, 4, 192, 233, 101, 239, 20, 130, 55, 39, 13, 11, 254, 199, 214, 158,
  24, 58, 192, 41, 19, 216, 78, 226, 234, 7, 180, 225, 235, 96, 108, 51, 244, 183, 202, 143, 227, 161, 134, 250,
  124, 215, 121, 247, 150, 66, 141, 196, 135, 236, 2, 127, 189, 164, 12, 139, 16, 96, 61, 115, 199, 73, 166, 24,
  20, 216, 235, 243, 194, 206, 70, 140, 229, 138, 159, 121, 58, 138, 223, 161, 12, 154, 225, 176, 244, 44, 208, 73,
  79, 195, 96, 180, 216, 169, 84, 33, 254, 184, 15, 197, 221, 10, 202, 10, 199, 91, 172, 218, 82, 79, 78, 68,
  197, 109, 145, 246, 90, 102, 233, 162, 37, 152, 174, 250, 3, 117, 231, 37, 52, 173, 58, 252, 232, 153, 235, 178,
  120, 134, 247, 21, 249, 18, 115, 98, 185, 173, 111, 85, 245, 206, 0, 203, 149, 84, 90, 62, 65, 230, 183, 154,
  23, 112, 26, 32, 19, 16, 73, 179, 71, 200, 185, 40, 245, 171, 34, 82, 125, 128, 79, 167, 34, 153, 39, 195,
  131, 87, 235, 156, 66, 135, 133, 13, 60, 45, 95, 17, 77, 239, 234, 64, 72, 28, 86, 27, 76, 189, 100, 244,
  186, 223, 88, 5, 204, 74, 247, 61, 83, 191, 224, 7, 245, 117, 214, 200, 227, 10, 239, 107, 243, 12, 152, 117,
  171, 88, 143, 18, 254, 47, 9, 1, 211, 189, 121, 165, 72, 235, 156, 119, 51, 141, 68, 251, 5, 52, 239, 33,
  36, 48, 5, 169, 136, 205, 166, 97, 9, 34, 38, 6, 237, 8, 104, 61, 1, 211, 189, 121, 165, 72, 235, 156,
  119, 51, 141, 68, 251, 5, 52, 239, 33, 36, 48, 5, 169, 136, 205, 166, 97, 9, 34, 38, 6, 237, 8, 104,
  61, 1, 211, 189, 121, 165, 72, 235, 156, 119, 51, 141, 68, 251, 5, 52, 239, 33, 36, 48, 5, 169, 136, 205,
  166, 97, 9, 34, 38, 6, 237, 8, 104, 61, 1, 1, 254, 34, 1, 254, 228, 27, 7, 254, 112, 8, 0, 252,
  128, 24, 169, 196, 142, 1, 0, 0]


/-- The child's `previous_state_hash`, as the daemon computed it. ⚑ This is the ORACLE and it is a
field of the wire, not a value anyone in this repo produced. -/
def childPreviousStateHash : Nat := 8394902380975589711861123145165826281573604591160422433563741797039332441420

/-- ⚑ **THE EQUATION.** The identity we compute for the parent, from the parent's bytes, IS the
identity the daemon put in the child's header. Nothing on either side is ours: the left is our
derivation over bytes a peer served, the right is a field of another block the same peer served.

This is the only claim in the tree that can REFUTE the ~1,400-bit order of `Body.to_input`. -/
theorem the_derived_state_hash_is_the_one_the_chain_recorded :
    deriveStateHash devnetParent = some childPreviousStateHash := by decide

/-- The child's own first 32 bytes really are that number, little-endian — so the oracle is read
off the wire and not asserted. -/
theorem the_oracle_is_the_childs_first_thirty_two_bytes :
    leNat (devnetChild.take 32) = childPreviousStateHash := by decide

/-- ⚑ **BOTH POLARITIES, ON REAL BYTES, FOR THE PRICE OF NEITHER.** The honest pair is accepted and
**every** other served hash is refused — a `∀`, not two sampled neighbours — by instantiating the
general guard theorem at the equation above. No second derivation, and a strictly stronger claim
than re-deriving twice would have bought. -/
theorem the_guard_discriminates_on_real_devnet_bytes :
    stateHashMatches devnetParent childPreviousStateHash = true
    ∧ ∀ x, x ≠ childPreviousStateHash → stateHashMatches devnetParent x = false :=
  the_guard_accepts_the_derived_and_refuses_the_rest devnetParent childPreviousStateHash
    the_derived_state_hash_is_the_one_the_chain_recorded

/-- ⚑ **AND IT IS REFUTABLE.** One flipped byte inside the `Blockchain_state` — the region the
fork-choice gate never reads — moves the derived identity.

This is the mutation that matters, and it is the one `MinaBinprotRealBlock` is structurally BLIND
to: the byte count is unchanged, so its exact-fit check passes, and `select` reads nothing there, so
every field assertion passes too. -/
theorem a_flipped_byte_in_the_blockchain_state_moves_the_identity :
    deriveStateHash (devnetParent.set 200 ((devnetParent.getD 200 0 + 1) % 128))
      ≠ some childPreviousStateHash := by decide

/-- And in `previous_state_hash` itself, which enters the OUTER Poseidon rather than the body. -/
theorem a_flipped_byte_in_the_parent_link_moves_the_identity :
    deriveStateHash (devnetParent.set 0 ((devnetParent.getD 0 0 + 1) % 128))
      ≠ some childPreviousStateHash := by decide

/-- A truncated protocol state is a REFUSAL, not a hash of what did arrive. -/
theorem a_truncated_protocol_state_is_refused :
    deriveStateHash (devnetParent.take (devnetParent.length - 1)) = none := by decide

/-- ⚑ **AND THE CHILD'S BYTES DO NOT HAVE THE PARENT'S IDENTITY.** Two real blocks, one real hash,
and the PAIRING is what is checked — the case an accepted-carrier design structurally cannot see. -/
theorem the_child_does_not_have_the_parents_identity :
    stateHashMatches devnetChild childPreviousStateHash = false := by decide

/-! ## axiom hygiene — ⚑ **ALL KERNEL.** No `native_decide`, no `sorry`, no axioms. -/

#assert_axioms the_derived_state_hash_is_the_one_the_chain_recorded
#assert_axioms the_oracle_is_the_childs_first_thirty_two_bytes
#assert_axioms the_guard_discriminates_on_real_devnet_bytes
#assert_axioms a_flipped_byte_in_the_blockchain_state_moves_the_identity
#assert_axioms a_flipped_byte_in_the_parent_link_moves_the_identity
#assert_axioms a_truncated_protocol_state_is_refused
#assert_axioms the_child_does_not_have_the_parents_identity

end Dregg2.Bridge.MinaStateHashRealBlock
