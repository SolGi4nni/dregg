/-
# Dregg2.Bridge.MinaStateHashDerive — **a Mina tip's identity, RE-DERIVED from the wire bytes.**

⚑ **SUBSTRATE, SAID OUT LOUD.** This file authors **NO AIR**. It is a HASH FUNCTION and a REFUSAL:
`List Nat → Option Nat`, no `Builder`, no gadget, no constraint. It is authored here rather than in
Rust for the same reason `MinaBinprot` is: what a Mina block's *identity* IS — which bytes are in the
preimage and in which order — is the content every downstream gate is anchored on, and rendered in
Rust it would be a MIRROR of openmina's `hashing.rs` whose correctness was a differential test.

## The hole this closes

Three separate lanes named the same soft spot and none closed it:

> **`state_hash` is re-derived nowhere.** The wire hashes are the peer's framing. `previous_state_hash`
> **is** decoded, so a *run* is checkable — but **a tip's identity is not.** We bind a proof to the
> header a peer *served*, not to a hash we computed.

`bridge/src/mina_head.rs` said so in a comment and `docs/MINA-LIGHT-CLIENT.md` carried it as an open
row. An earlier lane concluded the public GraphQL could not supply the preimage — true, and about the
**wrong wire**. We speak Mina's own p2p protocol now, and the binprot `Protocol_state.Value.Stable.V2`
carries **every field `state_hash` is a hash of, with nothing missing.** That is the finding: no gap
to name, so the derivation is the deliverable.

⚑ Note *why* it looked like a gap even on the right wire: `MinaBinprot` used to WALK the whole
`Blockchain_state` and throw it away. The preimage was arriving and being dropped one function call
before it was needed.

## What `state_hash` is, field by field

```text
state_hash      = Poseidon_Fp( salt "MinaProtoState"     )[ previous_state_hash ; state_body_hash ]
state_body_hash = Poseidon_Fp( salt "MinaProtoStateBody" )( pack_input (Body.to_input body) )
```
(`mina_state/protocol_state.ml:45-55, 176-179`; openmina `p2p-messages/src/v2/hashing.rs:408-413,
476-496`.)

`salt s` is `Random_oracle.update ~state:[0,0,0] [| prefix_to_field s |]` — one absorb, one
permutation (`random_oracle.ml:112`). `prefix_to_field` reads the prefix string **right-padded to 20
bytes with `'*'`** (`hash_prefixes.ml:1-24`) as a **little-endian** field element
(`Field.project (Fold.string_bits s)`, and `string_bits` emits each byte LSB-first). openmina spells
the same thing as 20 `'*'`-padded bytes plus 12 zeros read little-endian
(`poseidon/src/hash.rs:178-206`).

`Body.to_input` is **NOT** the binprot order, in four separate places, and each one is a way to hash
a different object while every byte still parses:

  1. **`constants` is absorbed FIRST**, before `genesis_state_hash`. In OCaml this is hidden in a
     `|>` pipeline (`protocol_state.ml:119-130`): `x |> append y` is `append y x`, so the pipeline
     PREPENDS. openmina writes it out flat (`hashing.rs:498-513`) and agrees.
  2. **Inside `constants`, `delta` is second** — `k, delta, slots_per_epoch, slots_per_sub_window,
     grace_period_slots, timestamp` — while the binprot record puts `delta` fifth
     (`protocol_constants_checked.ml:89-105`).
  3. **Inside `Epoch_data`, the order is `seed, start_checkpoint, epoch_length, ledger,
     lock_checkpoint`** while binprot is `ledger, seed, start_checkpoint, lock_checkpoint,
     epoch_length` (`proof_of_stake.ml:1007-1017`).
  4. **`has_ancestor_in_same_checkpoint_window` and `supercharge_coinbase` are absorbed BEFORE the
     two epoch-data blocks**, though `supercharge_coinbase` is the record's LAST field
     (`proof_of_stake.ml:1834-1873`). And inside `Local_state`, `account_update_index` comes before
     `success` (`local_state.ml:110-137`).

## ⚑ Two leaf facts a structure-level read gets wrong, and both were caught by cross-reading

  * **`last_vrf_output` contributes 253 bits, not 256.** `Vrf.Output.Truncated.length_in_bits =
    Int.min 256 (Field.size_in_bits - 2) = 253` (`consensus_vrf.ml:207`), and `to_bits` TAKES that
    many. openmina spells it as 31 whole bytes plus the low 5 bits of byte 31
    (`hashing.rs:641-652`). A 256-bit reading parses fine and hashes a different block.
  * **The `staged_ledger_hash` SHA-256 eats the ledger hash BIG-endian.** `Non_snark.digest` is
    `SHA256( Ledger_hash.to_bytes ‖ aux_hash ‖ pending_coinbase_aux )`
    (`staged_ledger_hash.ml:183-191`), and `Data_hash.to_bytes` is
    `Fold.bool_t_to_string (Field.unpack t)` — which conses its characters and **never reverses**
    (`fold.ml:116-129`), so the most significant byte comes out FIRST. openmina writes the field
    little-endian and then calls `.reverse()` (`hashing.rs:45-59`,
    `ledger/src/staged_ledger/hash.rs:148-178`). Two implementations, one endianness; the OCaml
    reads as little-endian until you notice the missing `List.rev`.

⚑ And it is SHA-256 there, not Blake2b. Blake2b in this arc is the VRF digest and the
`body_reference`; the staged-ledger non-snark digest is SHA-256, and the two are one line apart in
the same file.

## Primitives: all three already anchored to something outside this repo

  * **Poseidon** — `Circuit.Emit.PastaPoseidon.Ref`, Kimchi parameters, `#guard`-anchored to six real
    o1js `Poseidon.hash` gold vectors. Its absorb loop is the upstream `Absorbed n` state machine, so
    `absorbAll st xs` IS OCaml's `Random_oracle.update ~state:st xs`: both add into lanes `0..rate-1`
    and permute per full block, and both permute once on the way out.
  * **SHA-256** — `Circuit.Emit.Sha256Gadget.Ref.compressFrom`, FIPS-180-4 vectors. Multi-block
    chaining and the padding rule are added here; §2's `#guard`s are `hashlib` reference values on
    96-byte (two-block) messages, which is exactly the length `Non_snark.digest` hashes.
  * **The salts** — §3 pins both to openmina's own regression constants
    (`poseidon/tests/test_hash_params.rs:28-51`). That single pin exercises the `'*'` padding, the
    little-endian read, the round constants, the sponge's initial state and the absorb/squeeze
    schedule at once. It is the strongest external anchor in the file.

## What is NOT anchored by anything in this file, said plainly

Every PRIMITIVE above is checked against ground truth outside this repo. The **ORDER** — roughly 30
field elements and 1,400 packed bits, assembled in §4 — is transcribed from two independent
implementations that agree, and is checked against neither until it meets a real block. The reality
gate is `Bridge.MinaStateHashRealBlock`, and the honest form of it needs **no oracle at all**:
`state_hash` is not on Mina's p2p wire (every node computes it), so the check is
`derive(parent_bytes) = child.previous_state_hash` on a consecutive pair the peer itself served. If
any of the four order traps or two leaf facts above is wrong, that equation fails.

## Compiled, not kernel

`native_decide`/`#guard`-by-execution. A 55-round Poseidon over ~40 elements plus two SHA-256 blocks
is milliseconds compiled; the same object took a sibling 153 s of kernel reduction.
-/
import Dregg2.Bridge.MinaBinprot
import Dregg2.Circuit.Emit.PastaPoseidon

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaStateHashDerive

open Dregg2.Bridge.MinaBinprot

/-! ## §1 — `Random_oracle.Input.Chunked` and `pack_to_fields`.

Mina's random-oracle input is TWO streams, not one: whole field elements, and `(value, bit-width)`
chunks. `append` concatenates the two streams SEPARATELY, so the flattened input is *every field
element in append order* followed by *every packed chunk*, greedily concatenated
(`random_oracle_input.ml:18-76`). That separation is the reason `Body.to_input`'s reordering is
invisible to a reader who only tracks "which field comes next". -/

/-- `Random_oracle.Input.Chunked.t` — field elements, and `(value, bit width)` chunks. -/
structure Inp where
  /-- Whole field elements, in append order. -/
  fields : List Nat
  /-- `(value, bit width)` chunks, in append order; every `value < 2 ^ width`. -/
  packeds : List (Nat × Nat)
deriving Repr, DecidableEq

/-- `append` — ⚑ the two streams concatenate INDEPENDENTLY. -/
def Inp.app (a b : Inp) : Inp := ⟨a.fields ++ b.fields, a.packeds ++ b.packeds⟩

/-- The empty input. -/
def Inp.nil : Inp := ⟨[], []⟩

/-- `field x`. -/
def fieldI (x : Nat) : Inp := ⟨[x], []⟩

/-- `packed (x, n)`. -/
def packedI (x n : Nat) : Inp := ⟨[], [(x, n)]⟩

/-- `List.reduce_exn ~f:append` — left-associated, so plain append order. -/
def cat (xs : List Inp) : Inp := xs.foldl Inp.app Inp.nil

/-- A bool as a one-bit chunk. -/
def boolI (b : Bool) : Inp := packedI (if b then 1 else 0) 1

/-- `Field.size_in_bits` for the Pallas base field. ⚑ 255, and the chunk rule is `< 255`, so a chunk
holds at most **254** bits — and `2 ^ 254 < p`, so no packed chunk can ever need reduction. -/
def fieldSizeInBits : Nat := 255

/-- One step of `pack_to_fields`' fold: `(emitted, acc, acc_n)` (`random_oracle_input.ml:59-75`,
openmina `poseidon/src/hash.rs:139-163` — the same function, written twice).

`shift_left acc n + x` puts the FIRST-appended item in the HIGH bits of its chunk. The boundary test
is on `n + acc_n < 255`, evaluated BEFORE the item is placed, so an item that would reach 255 starts
a fresh chunk and is never split. -/
def packStep : (List Nat × Nat × Nat) → (Nat × Nat) → (List Nat × Nat × Nat)
  | (out, acc, accN), (x, n) =>
      let n' := n + accN
      if n' < fieldSizeInBits then (out, acc * 2 ^ n + x, n') else (out ++ [acc], x, n)

/-- **`packToFields`** — `Random_oracle.pack_input`. Field elements first, then the packed chunks. -/
def packToFields (c : Inp) : List Nat :=
  match c.packeds.foldl packStep ([], 0, 0) with
  | (out, acc, accN) => c.fields ++ (if accN > 0 then out ++ [acc] else out)

/-- `append_bytes` — each byte contributes 8 one-bit chunks, **LSB first**
(`Fold.string_bits`, `fold.ml:105-114`; openmina `BITS = [1,2,4,…,128]`). -/
def bytesI (bs : List Nat) : Inp :=
  ⟨[], bs.flatMap (fun b => (List.range 8).map (fun i => ((b >>> i) &&& 1, 1)))⟩

/-- The low `k` bits of one byte, LSB first — what the VRF output's 253rd..249th bits need. -/
def lowBitsI (b k : Nat) : Inp :=
  ⟨[], (List.range k).map (fun i => ((b >>> i) &&& 1, 1))⟩

/-! ## §2 — SHA-256 over a multi-block message, for `Non_snark.digest`.

`Sha256Gadget.Ref` supplies the compression function against FIPS vectors; the message schedule
around it (padding, chaining, the big-endian word/byte conventions) is here. The message
`Non_snark.digest` hashes is 96 bytes — three 32-byte pieces — so this is exercised at exactly two
blocks, which is the length the `#guard`s below pin. -/

/-- SHA-256 padding: `0x80`, zeros to 56 mod 64, then the bit length big-endian in 8 bytes. -/
def shaPad (msg : List Nat) : List Nat :=
  let l := msg.length
  let zeros := (55 + 64 - (l % 64)) % 64
  let bits := 8 * l
  msg ++ [0x80] ++ List.replicate zeros 0
      ++ (List.range 8).map (fun i => (bits / 256 ^ (7 - i)) % 256)

/-- 64 bytes → 16 BIG-endian 32-bit words. -/
def beWords (bs : List Nat) : List Nat :=
  (List.range 16).map (fun i =>
    let c := bs.drop (4 * i)
    ((c.getD 0 0) * 16777216 + (c.getD 1 0) * 65536 + (c.getD 2 0) * 256 + (c.getD 3 0)))

/-- Chunk into 64-byte blocks, `n` of them. Structural on the COUNT rather than well-founded on the
list: the padded length is always a multiple of 64, and a fuel argument keeps the whole file free of
well-founded recursion (which the kernel will not reduce at these sizes anyway). -/
def chunk64Aux : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | n + 1, bs => bs.take 64 :: chunk64Aux n (bs.drop 64)

/-- Chunk a padded message into its 64-byte blocks. -/
def chunk64 (bs : List Nat) : List (List Nat) := chunk64Aux ((bs.length + 63) / 64) bs

open Dregg2.Circuit.Emit.Sha256Gadget.Ref in
/-- **SHA-256** of a byte string → the 32 digest bytes, big-endian per word. -/
def sha256 (msg : List Nat) : List Nat :=
  let blocks := (chunk64 (shaPad msg)).map beWords
  let h := blocks.foldl (fun acc b => compressFrom acc b) IV
  h.flatMap (fun w => (List.range 4).map (fun i => (w / 256 ^ (3 - i)) % 256))

-- Reference anchors, against `hashlib.sha256`. The first two are the FIPS single-block vectors the
-- gadget already carries, re-run through the PADDING path (which the gadget's own `#guard`s hand-
-- assemble and therefore cannot check); the last two are TWO-BLOCK, 96-byte messages — the exact
-- shape and length `Non_snark.digest` hashes, so the chaining is anchored where it is used.
#guard sha256 [0x61, 0x62, 0x63] ==
  [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
   0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad]
#guard sha256 [] ==
  [0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
   0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55]
#guard sha256 (List.replicate 96 0) ==
  [0x2e, 0xa9, 0xab, 0x91, 0x98, 0xd1, 0x63, 0x80, 0x07, 0x40, 0x0c, 0xd2, 0xc3, 0xbe, 0xf1, 0xcc,
   0x74, 0x5b, 0x86, 0x4b, 0x76, 0x01, 0x1a, 0x0e, 0x1b, 0xc5, 0x21, 0x80, 0xac, 0x64, 0x52, 0xd4]
#guard sha256 (List.range 96) ==
  [0x08, 0x35, 0x9b, 0x10, 0x8f, 0xa5, 0x67, 0xf5, 0xdc, 0xf3, 0x19, 0xfa, 0x34, 0x34, 0xda, 0x6a,
   0xbb, 0xc1, 0xd5, 0x95, 0xf4, 0x26, 0x37, 0x26, 0x66, 0x44, 0x7f, 0x09, 0xcc, 0x5a, 0x87, 0xdc]

/-! ## §3 — The salted sponge, pinned to openmina's own regression constants. -/

open Dregg2.Circuit.Emit.PastaPoseidon.Ref in
/-- `Random_oracle.hash ~init:st xs` — absorb into the SALTED state, squeeze lane 0. -/
def hashFrom (st : List Nat) (xs : List Nat) : Nat := (absorbAll st xs).getD 0 0

/-- `Hash_prefixes.create` — right-pad to 20 bytes with `'*'`, or TRUNCATE to 20. -/
def prefixBytes (s : String) : List Nat :=
  ((s.toList.map Char.toNat) ++ List.replicate 20 0x2A).take 20

/-- `Random_oracle.prefix_to_field` — the padded prefix read LITTLE-endian. -/
def prefixField (s : String) : Nat := leNat (prefixBytes s)

open Dregg2.Circuit.Emit.PastaPoseidon.Ref in
/-- `Random_oracle.salt` — absorb the prefix field into `[0,0,0]` and permute once. -/
def saltOf (s : String) : List Nat := absorbAll [0, 0, 0] [prefixField s]

/-- The salt `state_hash` is taken under. -/
def saltProtoState : List Nat := saltOf "MinaProtoState"

/-- The salt `state_body_hash` is taken under. -/
def saltProtoStateBody : List Nat := saltOf "MinaProtoStateBody"

-- ⚑ THE EXTERNAL ANCHOR. These three-lane states are openmina's OWN pinned regression values
-- (`poseidon/tests/test_hash_params.rs:28-51`), which exist there for exactly this reason. Matching
-- them exercises, in one line each: the 20-byte `'*'` padding, the little-endian prefix read, the
-- Kimchi round constants and MDS, the `[0,0,0]` initial state, and the absorb-then-permute schedule.
-- A wrong padding character, a big-endian read, or an off-by-one in the absorb loop all move these.
#guard saltProtoState ==
  [5218970939948495870036503265499543025475317910763049867270287867667146978870,
   7663210626148314949787033187186036425676070286961909238040356477815169631084,
   19859188289320816036969227839574854326171440874550138016648548415357198703337]
#guard saltProtoStateBody ==
  [3548547909990922956559515810876765435326873020883079662683136168632773655275,
   134182536761489093478066959027928272525080293912190881939140820794450385287,
   18910449726094816833941350890285540874861148441082116020102338532207375519343]

-- And the prefixes really are the padded strings, not the bare ones: 20 bytes, `'*'`-filled.
#guard prefixBytes "MinaProtoState" ==
  [77, 105, 110, 97, 80, 114, 111, 116, 111, 83, 116, 97, 116, 101, 42, 42, 42, 42, 42, 42]
#guard prefixBytes "MinaProtoStateBody" ==
  [77, 105, 110, 97, 80, 114, 111, 116, 111, 83, 116, 97, 116, 101, 66, 111, 100, 121, 42, 42]

/-! ## §4 — `Body.to_input`, in the order the daemon absorbs it.

Every function below is a transcription of one OCaml `to_input`, cited. The widths are not
decoration: `Length`/`Index`/`Global_slot` are `Nat.Make32` (32 bits), `Amount`/`Fee`/`Block_time`
are 64, `Sgn` and every boolean are 1. A wrong width silently reshapes every chunk after it. -/

/-- `Amount.Signed.to_input` / `Fee.Signed.to_input` — magnitude (64 bits) then `sgn_to_bool`, where
`Pos ↦ true` (`currency.ml:494-502`). -/
def signedI (s : SignedAmt) : Inp := (packedI s.magnitude 64).app (boolI s.isPos)

/-- `Public_key.Compressed.to_input` — `x` as a field element, `is_odd` as one bit
(`non_zero_curve_point.ml:94-97`). -/
def pkI (k : Pk) : Inp := (fieldI k.x).app (boolI k.isOdd)

/-- `Local_state.to_input` (`local_state.ml:110-137`). ⚑ `account_update_index` before `success`,
and `failure_status_tbl` is excluded — it is decoded and never hashed. -/
def localI (l : LocalRaw) : Inp :=
  cat [fieldI l.stackFrame, fieldI l.callStack, fieldI l.txnCommitment, fieldI l.fullTxnCommitment,
       signedI l.excess, signedI l.supplyIncrease, fieldI l.ledger,
       packedI l.accountUpdateIndex 32, boolI l.success, boolI l.willSucceed]

/-- `Registers.to_input` (`registers.ml:30-41`), with `Pending_coinbase.Stack.to_input` inlined as
its three field elements: `data`, `state.init`, `state.curr` (`pending_coinbase.ml:273-276, 594-597`). -/
def registersI (r : RegistersRaw) : Inp :=
  cat [fieldI r.firstPassLedger, fieldI r.secondPassLedger, fieldI r.coinbaseStackData,
       fieldI r.coinbaseStackInit, fieldI r.coinbaseStackCurr, localI r.local_]

/-- `Fee_excess.to_input` (`fee_excess.ml:162-169`). -/
def feeI (f : FeeExcessRaw) : Inp :=
  cat [fieldI f.tokenL, signedI f.feeL, fieldI f.tokenR, signedI f.feeR]

/-- A field element as 32 BIG-endian bytes — `Data_hash.to_bytes`. ⚑ Big-endian: `bool_t_to_string`
conses its characters and never reverses them (`fold.ml:116-129`). -/
def fpBE (v : Nat) : List Nat := (List.range 32).map (fun i => (v / 256 ^ (31 - i)) % 256)

/-- `Staged_ledger_hash.Non_snark.digest` — `SHA256( BE(ledger_hash) ‖ aux_hash ‖
pending_coinbase_aux )` (`staged_ledger_hash.ml:183-191`). -/
def nonSnarkDigest (b : BlockchainRaw) : List Nat :=
  sha256 (fpBE b.slhLedgerHash ++ b.slhAuxHash ++ b.slhPendingCoinbaseAux)

/-- `Blockchain_state.to_input` (`blockchain_state.ml:140-155`) with `Staged_ledger_hash.to_input`
and `Snarked_ledger_state.to_input` inlined (`staged_ledger_hash.ml:318-322`,
`snarked_ledger_state.ml:263-288`). ⚑ `sok_digest` is excluded — it is a `unit` on the wire that
costs a byte and contributes nothing to the hash. -/
def blockchainI (b : BlockchainRaw) : Inp :=
  cat [bytesI (nonSnarkDigest b), fieldI b.slhPendingCoinbaseHash,
       fieldI b.genesisLedgerHash,
       registersI b.source, registersI b.target,
       fieldI b.connectingLeft, fieldI b.connectingRight,
       signedI b.supplyIncrease, feeI b.fee,
       packedI b.timestamp 64, bytesI b.bodyReference]

/-- `Epoch_data.to_input` (`proof_of_stake.ml:1007-1017`). ⚑ NOT the binprot order:
`seed, start_checkpoint, epoch_length, ledger, lock_checkpoint`. -/
def epochI (e : EpochRaw) : Inp :=
  cat [fieldI e.seed, fieldI e.startCheckpoint, packedI e.epochLength 32,
       fieldI e.ledgerHash, packedI e.ledgerTotalCurrency 64, fieldI e.lockCheckpoint]

/-- `Vrf.Output.Truncated.to_input` — ⚑ **253 bits**, not 256: 31 whole bytes and the low 5 bits of
byte 31 (`consensus_vrf.ml:207, 224-238`). -/
def vrfI (v : List Nat) : Inp := (bytesI (v.take 31)).app (lowBitsI (v.getD 31 0) 5)

/-- `Consensus_state.to_input` (`proof_of_stake.ml:1834-1873`). ⚑ `has_ancestor` and
`supercharge_coinbase` are absorbed BEFORE the epoch data, and `curr_global_slot_since_hard_fork`
contributes TWO `u32`s (`slot_number` and the value's own `slots_per_epoch`) while
`global_slot_since_genesis` contributes one. -/
def consensusI (c : ConsensusRaw) : Inp :=
  cat ([packedI c.blockchainLength 32, packedI c.epochCount 32, packedI c.minWindowDensity 32]
    ++ c.subWindowDensities.map (fun d => packedI d 32)
    ++ [vrfI c.lastVrfOutput, packedI c.totalCurrency 64,
        packedI c.currGlobalSlot 32, packedI c.slotsPerEpoch 32,
        packedI c.globalSlotSinceGenesis 32,
        boolI c.hasAncestor, boolI c.superchargeCoinbase,
        epochI c.staking, epochI c.next,
        pkI c.blockStakeWinner, pkI c.blockCreator, pkI c.coinbaseReceiver])

/-- `Protocol_constants_checked.to_input` (`protocol_constants_checked.ml:89-105`). ⚑ `delta` is
SECOND here and fifth in the binprot record. All six are packed; none is a field element. -/
def constantsI (k : CarriedConstants) : Inp :=
  cat [packedI k.k 32, packedI k.delta 32, packedI k.slotsPerEpoch 32,
       packedI k.slotsPerSubWindow 32, packedI k.gracePeriodSlots 32,
       packedI k.genesisStateTimestamp 64]

/-- **`bodyI`** — `Protocol_state.Body.to_input` (`protocol_state.ml:119-130`). ⚑ `constants` FIRST:
the OCaml is a `|>` pipeline and `x |> append y` is `append y x`, so each stage PREPENDS. openmina
writes the same order out flat (`hashing.rs:498-513`). -/
def bodyI (ps : ProtocolStateRaw) : Inp :=
  cat [constantsI ps.constants, fieldI ps.genesisStateHash,
       blockchainI ps.blockchain, consensusI ps.consensus]

/-! ## §5 — THE TWO HASHES, AND THE REFUSAL. -/

/-- `Protocol_state.Body.hash` (`protocol_state.ml:176-179`). -/
def stateBodyHash (ps : ProtocolStateRaw) : Nat :=
  hashFrom saltProtoStateBody (packToFields (bodyI ps))

/-- **`stateHash`** — `Protocol_state.hashes_abstract` (`protocol_state.ml:45-55`). This is a Mina
block's identity, computed from the bytes the peer served rather than taken from what it claimed. -/
def stateHash (ps : ProtocolStateRaw) : Nat :=
  hashFrom saltProtoState [ps.previousStateHash, stateBodyHash ps]

/-- **`deriveStateHash`** — protocol-state bytes → the tip's identity, or a REFUSAL. `none` is
every decode failure `MinaBinprot` already refuses (non-canonical width, non-canonical field element,
wrong density count, a VRF output that is not 32 bytes). -/
def deriveStateHash (bs : List Nat) : Option Nat :=
  match decodeProtocolStateRaw bs with
  | some (ps, _) => some (stateHash ps)
  | none => none

/-- **`stateHashMatches`** — ⚑ THE GUARD. `true` exactly when the bytes decode AND the identity we
computed is the one that was served. A served hash is now a CLAIM WE CHECK; before this it was an
input we accepted and then anchored the chain gate, the header binding and the fork-choice head on.

Fails closed: bytes that do not decode are `false`, never "unknown, proceed". -/
def stateHashMatches (bs : List Nat) (served : Nat) : Bool :=
  match deriveStateHash bs with
  | some h => h == served
  | none => false

/-! ## §6 — Structure, kernel-clean.

These do NOT need a real block: they are facts about the packing rule and the refusal, and they are
`decide`-able. The reality gate for the ORDER is `Bridge.MinaStateHashRealBlock`. -/

/-- ⚑ **A CHUNK HOLDS 254 BITS, NOT 255**, and the boundary is tested before the item is placed, so
no item is ever split across chunks. Two 127-bit items pack into one; a 128th bit starts a second. -/
theorem the_chunk_boundary_is_254_bits :
    packToFields ⟨[], [(1, 127), (1, 127)]⟩ = [2 ^ 127 + 1]
    ∧ packToFields ⟨[], [(1, 127), (1, 127), (1, 1)]⟩ = [2 ^ 127 + 1, 1] := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- ⚑ **THE FIRST-APPENDED ITEM LANDS IN THE HIGH BITS.** `[(x,64);(y,32);(z,16)]` packs to
`x·2^48 + y·2^16 + z` — the rule the OCaml docstring states and the code implements. A low-bits-first
reading agrees on every single-item input and disagrees on every real one. -/
theorem the_first_packed_item_is_most_significant :
    packToFields ⟨[], [(5, 64), (3, 32), (7, 16)]⟩ = [5 * 2 ^ 48 + 3 * 2 ^ 16 + 7] := by rfl

/-- ⚑ **FIELD ELEMENTS COME FIRST, ALWAYS** — however the two streams were interleaved by `append`.
This is what makes `Body.to_input`'s reordering invisible to a reader tracking only "next field". -/
theorem the_field_stream_precedes_the_packed_stream :
    packToFields (cat [packedI 1 8, fieldI 111, packedI 2 8, fieldI 222])
      = [111, 222, 1 * 256 + 2] := by rfl

/-- An empty input is an EMPTY field vector, not a zero — `acc_n = 0` appends nothing
(`random_oracle_input.ml:71-72`). -/
theorem an_empty_input_packs_to_nothing : packToFields Inp.nil = [] := by rfl

/-- ⚑ **253 BITS, AND THE THREE HIGH BITS OF THE LAST BYTE ARE NOT IN THE PREIMAGE.** The last byte
contributes its low 5 bits only: `0x80` and `0x00` are the same input, `0x10` and `0x00` are not.
That is a real (and upstream) truncation, and stating it is the difference between transcribing it
and assuming 256. -/
theorem the_vrf_contributes_253_bits :
    (vrfI (List.replicate 32 0)).packeds.length = 253
    ∧ lowBitsI 0x80 5 = lowBitsI 0 5
    ∧ lowBitsI 0x10 5 ≠ lowBitsI 0 5 := by
  refine ⟨by rfl, by rfl, by decide⟩

-- And on the whole 32-byte object, in the compiled evaluator: the top three bits of byte 31 are
-- invisible to the hash preimage, and bit 4 is not.
#guard vrfI (List.replicate 31 0 ++ [0xE0]) == vrfI (List.replicate 32 0)
#guard (vrfI (List.replicate 31 0 ++ [0x10]) == vrfI (List.replicate 32 0)) == false

/-- ⚑ **THE GUARD FAILS CLOSED.** A decode refusal is a REFUSAL for EVERY served hash — never an
"unknown" that proceeds. This is the arm a fail-open gate gets wrong. -/
theorem the_guard_refuses_when_the_decode_refuses (bs : List Nat) (served : Nat)
    (h : deriveStateHash bs = none) : stateHashMatches bs served = false := by
  simp [stateHashMatches, h]

/-- ⚑ **AND IT IS NOT A CONSTANT `false`.** When the bytes DO decode, the guard is exactly the
equality between the hash we computed and the hash we were handed — so it accepts the honest pair
and refuses every other served value, rather than refusing everything. A guard that only refuses is
indistinguishable from a function returning `false`. -/
theorem the_guard_is_the_derived_equality (bs : List Nat) (h served : Nat)
    (hd : deriveStateHash bs = some h) :
    stateHashMatches bs served = (h == served) := by
  simp [stateHashMatches, hd]

/-- Corollary, both polarities in one statement: it ACCEPTS the derived hash and REFUSES every
other. -/
theorem the_guard_accepts_the_derived_and_refuses_the_rest (bs : List Nat) (h : Nat)
    (hd : deriveStateHash bs = some h) :
    stateHashMatches bs h = true ∧ ∀ x, x ≠ h → stateHashMatches bs x = false := by
  refine ⟨by simp [the_guard_is_the_derived_equality bs h h hd], ?_⟩
  intro x hx
  rw [the_guard_is_the_derived_equality bs h x hd]
  simp [Ne.symm hx]

-- The refusal arm is inhabited by real bytes, in the compiled evaluator: an empty wire, and a
-- truncated one, are both `none` — so `the_guard_refuses_when_the_decode_refuses` has a premise
-- something actually satisfies.
#guard deriveStateHash [] == none
#guard deriveStateHash (List.replicate 100 0) == none

/-- The salts are DISTINCT, so a body hash can never be mistaken for a state hash. (Mina's whole
domain separation rests on this and it costs one line to say.) -/
theorem the_two_salts_differ : saltProtoState ≠ saltProtoStateBody := by native_decide

/-! ## §7 — axiom hygiene.

The `#guard`s in §2/§3 are the COMPILED evaluator against external reference values. §6 is kernel
`decide`/`rfl` except `the_two_salts_differ`, which reduces two 55-round permutations and is stated
as `native_decide` rather than pretended to be cheap. -/

#assert_axioms the_chunk_boundary_is_254_bits
#assert_axioms the_first_packed_item_is_most_significant
#assert_axioms the_field_stream_precedes_the_packed_stream
#assert_axioms an_empty_input_packs_to_nothing
#assert_axioms the_vrf_contributes_253_bits
#assert_axioms the_guard_refuses_when_the_decode_refuses
#assert_axioms the_guard_is_the_derived_equality
#assert_axioms the_guard_accepts_the_derived_and_refuses_the_rest

#print axioms the_two_salts_differ

end Dregg2.Bridge.MinaStateHashDerive
