/-
# Dregg2.Bridge.MinaBinprotRealBlock — ⚑ **THE REALITY GATE: the Lean decoder reads a LIVE Mina
devnet block, byte-exactly.**

The bytes below are `Mina_state.Protocol_state.Value.Stable.V2` for **devnet block 540186**, captured
on 2026-07-30 from `seed-1.devnet.gcp.o1test.net:10003` over Mina's own peer-to-peer protocol —
`TCP → pnet(XSalsa20) → multistream-select → Noise_XX_25519_ChaChaPoly_SHA256 → /coda/yamux/1.0.0 →
coda/rpcs/0.0.1 → get_best_tip v2`. Not GraphQL. Not a fixture anyone wrote. What a Mina node hands a
peer that asks it for its best tip.

## Why this module is separate from `MinaBinprot`

`MinaForkChoiceGate` reaches `MinaBinprot`, and `MinaForkChoiceGate` is in `Dregg2/FFI.lean`'s import
closure — so anything `MinaBinprot` imports is spliced into `libdregg_lean.a`. 1,544 numerals of
fixture have no business in a shipped archive. This module imports the decoder rather than the other
way round, and is rooted only in `Dregg2.lean`.

## What this gate can catch that the hand-built vectors cannot

`MinaBinprot`'s own `#guard`s and theorems run on bytes assembled by a test encoder, and an encoder
written by the same hand as the decoder agrees with it by construction — it cannot catch a field
ORDER that is wrong in both. This can, and it did, twice, on the first run against real bytes:

  1. **`sok_digest : unit` is one `0x00` byte, not free.** OCaml's `bin_write_unit` writes a byte.
     Everything after it read one byte early — and the shift survived TWENTY canonical
     field-element checks before surfacing as a block timestamp of 0.
  2. **`body_reference` is a LENGTH-PREFIXED byte string, not a bare 32-byte digest.** It is a
     Blake2b hash and looks like a raw digest; the `Nat0` in front of it is easy to drop.

Neither was a reasoning error about the record layout — the layout was read correctly from the
daemon AND from openmina's machine-derived types. Both were LEAF ENCODING errors, which is the class
a structure-level cross-check is blind to. That is the argument for this file existing.

## The ground truth it is checked against

openmina (`~/dev/mina-rust`) decoded the SAME captured response with its own generated types and
reported: `blockchain_length 540186`, `epoch_count 56`, `min_window_density 3`,
`sub_window_densities [2, 5, 6, 6, 4, 5, 3, 3, 3, 2, 5]`, `curr_global_slot 404098`,
`slots_per_epoch 7140`, `global_slot_since_genesis 849958`, `total_currency 1584595834000001000`,
`previous_state_hash 3NKfM1WZF4TWBy5ZdoVdxjXzMRndmAhzoMvw1i5gbJFn6WZ1pyBw`, and a re-encoded
protocol state of exactly **1544 bytes**. Every one of those is asserted below.

⚑ **This is a differential against a DECODER, and that is a different thing from a differential
against a RULE.** `MinaChainSelectionDifferential` exists because openmina's chain-selection
*semantics* disagree with the daemon's — that disagreement is a proven theorem in this tree, and it
is why nothing here takes openmina's verdict about anything. But openmina's `p2p-messages` types are
MACHINE-DERIVED from the OCaml `.bin_prot` shapes, so on the question "which bytes are which field"
it is a transcription of the daemon, not a second opinion. Agreement on the parse is evidence;
agreement on a verdict would not have been.
-/
import Dregg2.Bridge.MinaForkChoiceGate

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaBinprotRealBlock

open Dregg2.Bridge.MinaChainSelection
open Dregg2.Bridge.MinaBinprot
open Dregg2.Bridge.MinaForkChoiceGate

/-- The 1,544 bytes of devnet block 540186's `Protocol_state.Value.Stable.V2`, exactly as the peer
served them. -/
def devnetBlock540186 : List Nat := [
  82, 197, 34, 244, 235, 28, 215, 231, 1, 111, 234, 66, 112, 156, 241, 229, 89, 228, 6, 192, 99, 202, 86, 120,
  106, 90, 73, 23, 66, 234, 160, 3, 145, 168, 234, 178, 20, 192, 233, 236, 226, 167, 123, 12, 229, 92, 190, 144,
  63, 107, 76, 239, 59, 58, 122, 149, 210, 237, 217, 24, 167, 147, 38, 20, 212, 230, 246, 113, 68, 172, 218, 202,
  59, 76, 239, 114, 224, 175, 208, 180, 119, 204, 161, 37, 64, 158, 42, 234, 199, 254, 157, 13, 141, 96, 117, 44,
  32, 130, 25, 20, 232, 133, 67, 201, 196, 183, 157, 176, 208, 151, 78, 194, 8, 141, 44, 74, 165, 69, 11, 114,
  251, 217, 185, 15, 144, 201, 161, 68, 208, 32, 95, 115, 46, 190, 14, 85, 144, 41, 72, 178, 129, 27, 216, 120,
  213, 87, 47, 218, 141, 32, 91, 38, 39, 140, 54, 180, 89, 140, 146, 236, 34, 232, 134, 139, 232, 64, 134, 234,
  202, 221, 117, 42, 186, 6, 107, 7, 216, 46, 243, 214, 111, 40, 205, 243, 10, 54, 186, 244, 104, 248, 85, 204,
  125, 35, 252, 207, 248, 128, 20, 78, 119, 5, 89, 162, 155, 47, 112, 166, 125, 240, 178, 82, 236, 43, 2, 12,
  195, 185, 104, 102, 159, 184, 205, 94, 228, 57, 108, 243, 66, 209, 121, 67, 203, 156, 130, 92, 201, 234, 59, 130,
  156, 108, 40, 79, 203, 3, 254, 30, 1, 164, 225, 221, 158, 177, 63, 124, 214, 34, 162, 19, 91, 47, 63, 21,
  29, 136, 51, 78, 182, 6, 217, 205, 118, 250, 87, 187, 212, 179, 195, 253, 7, 161, 106, 159, 253, 58, 55, 58,
  148, 2, 53, 185, 213, 30, 93, 124, 116, 20, 86, 248, 103, 32, 115, 18, 65, 168, 40, 2, 115, 207, 198, 194,
  22, 104, 253, 123, 198, 197, 135, 208, 204, 29, 70, 86, 61, 25, 182, 150, 163, 87, 26, 16, 1, 61, 148, 204,
  188, 18, 253, 122, 156, 228, 178, 6, 50, 81, 220, 44, 246, 42, 154, 213, 101, 16, 70, 86, 61, 25, 182, 150,
  163, 87, 26, 16, 1, 61, 148, 204, 188, 18, 253, 122, 156, 228, 178, 6, 50, 81, 220, 44, 246, 42, 154, 213,
  101, 16, 108, 198, 112, 229, 38, 30, 251, 217, 204, 72, 197, 136, 205, 162, 244, 187, 41, 39, 208, 89, 192, 175,
  208, 112, 201, 142, 214, 148, 46, 102, 65, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
  0, 1, 112, 252, 137, 254, 117, 202, 223, 88, 74, 184, 8, 249, 119, 60, 89, 0, 101, 235, 201, 190, 38, 208,
  251, 47, 41, 143, 74, 146, 90, 166, 91, 40, 51, 87, 186, 106, 4, 201, 156, 73, 226, 219, 100, 71, 43, 216,
  236, 237, 36, 56, 252, 81, 155, 31, 172, 146, 214, 239, 158, 172, 189, 78, 80, 22, 193, 157, 179, 112, 98, 217,
  171, 240, 89, 250, 72, 66, 216, 160, 143, 107, 1, 227, 247, 188, 148, 1, 194, 234, 167, 48, 240, 50, 113, 235,
  2, 49, 70, 86, 61, 25, 182, 150, 163, 87, 26, 16, 1, 61, 148, 204, 188, 18, 253, 122, 156, 228, 178, 6,
  50, 81, 220, 44, 246, 42, 154, 213, 101, 16, 199, 152, 215, 16, 134, 133, 149, 91, 203, 84, 228, 86, 51, 23,
  58, 132, 75, 4, 56, 52, 29, 243, 134, 36, 85, 183, 38, 42, 193, 94, 115, 30, 108, 198, 112, 229, 38, 30,
  251, 217, 204, 72, 197, 136, 205, 162, 244, 187, 41, 39, 208, 89, 192, 175, 208, 112, 201, 142, 214, 148, 46, 102,
  65, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 131, 43, 184, 108, 7, 155,
  193, 139, 128, 219, 13, 44, 91, 120, 9, 42, 145, 18, 55, 8, 6, 97, 24, 247, 165, 70, 74, 8, 46, 55,
  245, 55, 51, 87, 186, 106, 4, 201, 156, 73, 226, 219, 100, 71, 43, 216, 236, 237, 36, 56, 252, 81, 155, 31,
  172, 146, 214, 239, 158, 172, 189, 78, 80, 22, 252, 0, 76, 118, 80, 76, 20, 0, 0, 0, 1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252, 192, 102, 41, 180, 159, 1,
  0, 0, 32, 166, 223, 95, 45, 46, 125, 238, 248, 84, 197, 249, 121, 198, 85, 191, 87, 190, 184, 181, 134, 29,
  222, 93, 46, 61, 244, 139, 69, 81, 237, 57, 40, 253, 26, 62, 8, 0, 56, 3, 11, 2, 5, 6, 6, 4,
  5, 3, 3, 3, 2, 5, 32, 8, 135, 208, 50, 199, 213, 215, 72, 210, 43, 215, 30, 157, 38, 243, 254, 232,
  39, 96, 168, 69, 56, 67, 36, 111, 151, 174, 114, 56, 123, 7, 0, 252, 232, 71, 34, 246, 131, 157, 253, 21,
  0, 253, 130, 42, 6, 0, 254, 228, 27, 0, 253, 38, 248, 12, 0, 22, 8, 72, 6, 84, 31, 0, 125, 80,
  152, 253, 225, 111, 201, 81, 195, 128, 148, 164, 245, 51, 228, 222, 208, 74, 70, 224, 51, 42, 91, 111, 58, 252,
  232, 113, 123, 52, 53, 145, 236, 21, 26, 4, 192, 233, 101, 239, 20, 130, 55, 39, 13, 11, 254, 199, 214, 158,
  24, 58, 192, 41, 19, 216, 78, 226, 234, 7, 180, 225, 235, 96, 108, 51, 244, 183, 202, 143, 227, 161, 134, 250,
  124, 215, 121, 247, 150, 66, 141, 196, 135, 236, 2, 127, 189, 164, 12, 139, 16, 96, 61, 115, 199, 73, 166, 24,
  20, 216, 235, 243, 194, 206, 70, 140, 229, 138, 159, 121, 58, 138, 223, 161, 12, 154, 225, 176, 244, 44, 208, 73,
  79, 195, 96, 180, 216, 169, 84, 33, 254, 184, 15, 197, 221, 10, 202, 10, 199, 91, 172, 218, 82, 79, 78, 68,
  197, 109, 145, 246, 90, 102, 233, 162, 37, 152, 174, 250, 3, 117, 231, 37, 52, 173, 58, 252, 232, 153, 235, 178,
  120, 134, 247, 21, 143, 65, 11, 41, 37, 116, 255, 81, 112, 77, 160, 179, 209, 78, 39, 142, 211, 81, 79, 170,
  221, 2, 122, 143, 166, 123, 199, 53, 198, 220, 243, 10, 245, 171, 34, 82, 125, 128, 79, 167, 34, 153, 39, 195,
  131, 87, 235, 156, 66, 135, 133, 13, 60, 45, 95, 17, 77, 239, 234, 64, 72, 28, 86, 27, 82, 197, 34, 244,
  235, 28, 215, 231, 1, 111, 234, 66, 112, 156, 241, 229, 89, 228, 6, 192, 99, 202, 86, 120, 106, 90, 73, 23,
  66, 234, 160, 3, 254, 11, 9, 1, 67, 167, 86, 254, 37, 62, 19, 31, 106, 246, 98, 246, 86, 122, 87, 134,
  30, 132, 14, 213, 181, 156, 207, 178, 44, 235, 230, 206, 122, 195, 174, 30, 0, 67, 167, 86, 254, 37, 62, 19,
  31, 106, 246, 98, 246, 86, 122, 87, 134, 30, 132, 14, 213, 181, 156, 207, 178, 44, 235, 230, 206, 122, 195, 174,
  30, 0, 67, 167, 86, 254, 37, 62, 19, 31, 106, 246, 98, 246, 86, 122, 87, 134, 30, 132, 14, 213, 181, 156,
  207, 178, 44, 235, 230, 206, 122, 195, 174, 30, 0, 1, 254, 34, 1, 254, 228, 27, 7, 254, 112, 8, 0, 252,
  128, 24, 169, 196, 142, 1, 0, 0]

/-- `previous_state_hash` as its numeric field element — the `Fp` that Base58Checks to
`3NKfM1WZF4TWBy5ZdoVdxjXzMRndmAhzoMvw1i5gbJFn6WZ1pyBw`. -/
def prevStateHash540186 : Nat :=
  1641250866568328141017185150970871954161620886282563728353308725062058296658

/-- `staking_epoch_data.lock_checkpoint` — the field `is_short_range` keys on. -/
def stakingLock540186 : Nat :=
  15075911394166281270158530601176310268336451501613032608083680259022418335764

/-- Every claim, on the real bytes, through the CHECKED entry point (so the carried-constants and
density refusals are exercised on a genuine block rather than only on a mutation). -/
def realBlockCheck : Bool :=
  match decodeProtocolStateChecked mainnet devnetBlock540186 with
  | some (ps, rest) =>
      -- ⚑ EXACT FIT. openmina re-encoded this protocol state to 1544 bytes; the decoder lands on
      -- the last one. A field-order slip that happened to stay in-range would not.
      rest.isEmpty
      && ps.previousStateHash == prevStateHash540186
      && ps.consensus.blockchainLength == 540186
      && ps.consensus.epochCount == 56
      && ps.consensus.minWindowDensity == 3
      && ps.consensus.subWindowDensities == [2, 5, 6, 6, 4, 5, 3, 3, 3, 2, 5]
      && ps.consensus.currGlobalSlot == 404098
      && ps.consensus.slotsPerEpoch == 7140
      && ps.consensus.globalSlotSinceGenesis == 849958
      && ps.consensus.totalCurrency == 1584595834000001000
      && ps.consensus.stakingLockCheckpoint == stakingLock540186
      -- At this height the NEXT epoch's lock checkpoint IS the parent state hash.
      && ps.consensus.nextLockCheckpoint == prevStateHash540186
      && ps.consensus.hasAncestorInSameCheckpointWindow == true
      && ps.consensus.superchargeCoinbase == true
      && ps.consensus.lastVrfHash.length == 32
      && ps.constants.k == 290
      && ps.constants.slotsPerEpoch == 7140
      && ps.constants.slotsPerSubWindow == 7
      && ps.constants.gracePeriodSlots == 2160
      && ps.constants.delta == 0
  | none => false

/-- ⚑ **THE DECODER READS A REAL MINA BLOCK.** -/
theorem the_decoder_reads_a_real_devnet_block : realBlockCheck = true := by native_decide

/-- ⚑ **AND THIS IS THE ARRAY GRAPHQL CANNOT SERVE.** `sub_window_densities` is the input Samasika's
LONG-RANGE branch reads and the reason `MinaChainSelection` exported nothing for a day: it is not a
field of the public GraphQL `ConsensusState` at any endpoint. Here it is, off the wire, in the
structure `select` runs on.

The window is also worth looking at: eleven sub-windows summing to 44 with a `min_window_density` of
**3**. That is a real low-density era on devnet, the same regime `MinaSlidingWindow`'s 849-transition
replay walked through (34 → 14 → 8 → 3) — so the long-range branch is not a hypothetical here. -/
def densitiesCheck : Bool :=
  match decodeProtocolState devnetBlock540186 with
  | some (ps, _) =>
      (ps.consensus.subWindowDensities.length == 11)
      && (ps.consensus.subWindowDensities.foldl (· + ·) 0 == 44)
      && (ps.consensus.subWindowDensities.all (· ≤ 7))
      && (ps.consensus.minWindowDensity == 3)
  | none => false

theorem the_real_window_is_the_array_graphql_cannot_serve : densitiesCheck = true := by
  native_decide

/-- ⚑ **AND THE REAL STATE DRIVES FORK CHOICE.** The decoded tip does not displace itself; a rival at
the SAME staking lock checkpoint (hence short-range) and one block longer does; and a rival at the
same length with a WORSE window does not. No conversion sits between the parse and the verdict —
`decodeProtocolState` returns the very structure `beats_not_transitive` is stated over. -/
def forkChoiceOnRealStateCheck : Bool :=
  match decodeProtocolState devnetBlock540186 with
  | some (ps, _) =>
      let real := ps.consensus
      let longer := { real with blockchainLength := real.blockchainLength + 1 }
      -- ⚑ A rival at the SAME staking lock checkpoint is SHORT-range, so its window is never
      -- consulted — length decides. To reach the LONG-range branch the checkpoints must differ,
      -- which is exactly what `isShortRange` keys on.
      let rival := { real with stakingLockCheckpoint := real.stakingLockCheckpoint + 1,
                               subWindowDensities := List.replicate 11 0, minWindowDensity := 0 }
      (minaBetterTip mainnet real real 1 1 == false)
      && (isShortRange mainnet real longer == true)
      && (minaBetterTip mainnet real longer 1 2 == true)
      && (minaBetterTip mainnet longer real 2 1 == false)
      -- the LONG-range branch, genuinely taken, deciding on the window off the real wire
      && (isShortRange mainnet real rival == false)
      && (minaBetterTip mainnet real rival 1 2 == false)
      && (minaBetterTip mainnet rival real 2 1 == true)
  | none => false

theorem the_real_state_drives_fork_choice : forkChoiceOnRealStateCheck = true := by native_decide

/-- ⚑ **AND IT IS REFUTABLE.** Truncating the real bytes, and flipping the `sub_window_densities`
count byte on the real bytes, are both REFUSALS. A decoder that cannot go red on a real block is not
a check. (The count byte sits at offset 1074: `previous_state_hash` and the body walk to 1066,
`blockchain_length` is a 5-byte `0xfd` form, `epoch_count` and `min_window_density` one byte each.) -/
def refutabilityCheck : Bool :=
  (decodeProtocolState (devnetBlock540186.take 1543) == none)
  && (decodeProtocolState (devnetBlock540186.set 1074 10) == none)
  && (decodeProtocolState (devnetBlock540186.drop 1) == none)

theorem the_real_block_gate_can_go_red : refutabilityCheck = true := by native_decide

/-- The count byte really is where the comment says, so `refutabilityCheck` is not passing for an
unrelated reason. -/
theorem the_density_count_byte_is_eleven : devnetBlock540186.getD 1074 0 = 11 := by native_decide


/-! ## ⚑ THE WHOLE THING, END TO END, ON REAL BYTES.

Not the decoder in isolation and not the rule in isolation: the two `@[export]`ed gates, driven
through their STRING C-ABI wire, on the bytes a devnet peer actually served. -/

/-- A hex digit. -/
def hexDigitChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Bytes to lowercase hex — the form the gate wire carries. -/
def hexOf (bs : List Nat) : String :=
  String.mk (bs.flatMap (fun b => [hexDigitChar (b / 16), hexDigitChar (b % 16)]))

/-- The real block, one block longer. `blockchain_length` is the 5-byte `0xfd` form beginning at
offset 1067, so byte 1068 is its low byte: `0x1a` (540186) becomes `0x1b` (540187). Everything else
— including the staking lock checkpoint — is untouched, so the pair is SHORT-range and length
decides. -/
def devnetBlock540187 : List Nat := devnetBlock540186.set 1068 27

/-- ⚑ **THE EXPORTED FORK-CHOICE GATE, ON REAL DEVNET BYTES.** The real tip does not displace
itself; the one-longer sibling displaces it; and the reverse presentation does not. Every one of
these went in as hex over the same `String → String` C ABI `dregg-lean-ffi` calls. -/
def exportedGateOnRealBytes : Bool :=
  let e := hexOf devnetBlock540186
  let c := hexOf devnetBlock540187
  (minaBetterTipGate ("eh=1;ch=1;e=" ++ e ++ ";c=" ++ e) == "0")
  && (minaBetterTipGate ("eh=1;ch=2;e=" ++ e ++ ";c=" ++ c) == "1")
  && (minaBetterTipGate ("eh=2;ch=1;e=" ++ c ++ ";c=" ++ e) == "0")

theorem the_exported_gate_decides_on_real_devnet_bytes : exportedGateOnRealBytes = true := by
  native_decide

/-- ⚑ **AND THE HEAD ROLLS, ON REAL DEVNET BYTES.** With the anchored-segment gate accepting
(`sg=1`) the head advances and the finalized height ratchets to `540187 − k = 539897`. With it
REFUSING (`sg=0`) — which is what an unavailable source supplies — nothing advances and the
persisted finalized height comes back UNCHANGED. That second line is the fail-closed arm, exercised
on real bytes rather than on scalars. -/
def exportedRollOnRealBytes : Bool :=
  let e := hexOf devnetBlock540186
  let c := hexOf devnetBlock540187
  let tip := "eh=1;ch=2;e=" ++ e ++ ";c=" ++ c
  (minaHeadAdvanceGate ("sg=1;fz=0;" ++ tip) == "adv=1;fin=539897")
  && (minaHeadAdvanceGate ("sg=0;fz=0;" ++ tip) == "adv=0;fin=0")
  -- ⚑ THE RATCHET: a REFUSED advance does not drop an already-finalized height either.
  && (minaHeadAdvanceGate ("sg=0;fz=539897;" ++ tip) == "adv=0;fin=539897")
  -- and a SHORTER candidate cannot lower it
  && (minaHeadAdvanceGate ("sg=1;fz=539897;eh=2;ch=1;e=" ++ c ++ ";c=" ++ e) == "adv=0;fin=539897")

theorem the_head_rolls_on_real_devnet_bytes : exportedRollOnRealBytes = true := by native_decide

/-- The finalized height really is `blockchain_length − k` at the pinned `k`, so the number above is
not a coincidence of the fixture. -/
theorem the_ratchet_is_length_minus_k : 540187 - mainnet.k = 539897 := by decide

/-! ## axiom hygiene — these are `native_decide` (EXECUTION) results and carry `Lean.ofReduceBool`.
Stated, not hidden: a 1,544-byte parse is not a kernel reduction. -/

#print axioms the_decoder_reads_a_real_devnet_block
#print axioms the_real_state_drives_fork_choice
#print axioms the_real_block_gate_can_go_red
#print axioms the_exported_gate_decides_on_real_devnet_bytes
#print axioms the_head_rolls_on_real_devnet_bytes
#assert_axioms the_ratchet_is_length_minus_k

end Dregg2.Bridge.MinaBinprotRealBlock
