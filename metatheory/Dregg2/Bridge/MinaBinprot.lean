/-
# Dregg2.Bridge.MinaBinprot — **Mina's binprot wire format, as a Lean function.**

⚑ **SUBSTRATE, SAID OUT LOUD.** This file authors **NO AIR**. It is a PARSER: pure
`List Nat → Option ConsensusState`, no `Builder`, no gadget, no constraint. But it is authored HERE
rather than in Rust for the reason that matters more than the substrate law — **a parser IS
semantics.** What a Mina consensus state *is* — which bytes are `min_window_density` and which are
`epoch_count` — is exactly the content the fork-choice rule operates on. Rendered in Rust it would be
a MIRROR of openmina's `p2p-messages`, and its correctness would be a DIFFERENTIAL TEST. Rendered
here it is the definition, and `select` consumes its output directly.

## The one thing this file buys

`Bridge.MinaChainSelection` proved Samasika's `select` and then exported nothing, because the
long-range branch reads `sub_window_densities` and **`subWindowDensities` is not a field of the
public GraphQL `ConsensusState`** — the resolver list is `proof_of_stake.ml:2449-2536` and it has no
arm for it. Three routes carry the array: the archive DB, the precomputed-block JSON, and **binprot**
— the encoding Mina's own peers speak. This file is binprot.

**And note what does NOT appear anywhere below: a second `ConsensusState`.** `decodeProtocolState`
returns `MinaChainSelection.ConsensusState`, the exact structure `select_reads_only_eight_fields`,
`beats_not_transitive` and `minaBetterTip_decides` are stated over. There is no intermediate type, no
conversion function, and therefore nothing to keep in agreement. Rust's entire remaining job is to
hand these bytes over.

## ⚑ Field ORDER is the whole correctness question

binprot is POSITIONAL: no tags, no names, no per-field lengths on a record. A decoder with the fields
in the wrong order does not fail — it silently reads `min_window_density` out of `epoch_count`. The
order below was read from the daemon (`src/lib/consensus/proof_of_stake.ml:1743-1758`;
`src/lib/mina_state/protocol_state.ml:37-41,62-73`; `src/lib/mina_base/epoch_data.ml:20-27`;
`src/lib/genesis_constants/genesis_constants.ml:246-252`) and independently confirmed against
openmina's generated types, which are machine-derived from the OCaml `.bin_prot` SHAPES
(`crates/p2p-messages/src/v2/generated.rs:148,197,3050,3208`). Three traps it contains, each of which
a from-prose reconstruction gets wrong:

  1. **`Epoch_data` is `ledger` FIRST, then `seed`** — not `seed` first, which is how the GraphQL
     surface and every doc page present it.
  2. **`Length` is a binprot SIGNED int** — not a `Nat0`, not a fixed four bytes
     (`Unsigned_extended.UInt32` writes through `bin_write_int`).
  3. **`Global_slot_since_hard_fork` / `..._since_genesis` are single-constructor VARIANTS**, so each
     costs a leading tag byte before its integer.

## Canonicality is enforced, not assumed

Every `Nat0` and every signed integer must arrive in its CANONICAL width (a `Length` of 3 written as
`0xfe 03 00` is a REFUSAL, not a 3), and every field element must be `< p`. The second one is not
hygiene: Poseidon's `absorbAt` enters every input through `(state + x) % p`, so `x` and `x + p` are
the same element at the digest, and a checkpoint admitted in two encodings is a checkpoint that
compares unequal to itself.

## What is decoded, and what is deliberately not

`Blockchain_state` is WALKED IN FULL and discarded — it has to be walked, because it sits between
`genesis_state_hash` and `consensus_state` and binprot has no length prefix a reader could jump. The
block BODY (a whole staged-ledger diff) and the header fields after the Wrap proof are not reached
by this file at all; `decodeProtocolState` is total on its prefix and says how many bytes it used.

**Not done here, and not done anywhere yet: re-deriving `state_hash` from the body.** That is
`Poseidon(prefix "MinaProtoState")[previous_state_hash, body_hash]` (`protocol_state.ml:45-55`), and
`Body.hash` absorbs `to_input` in an order that is NOT the binprot order
(`protocol_state.ml:119-130`). `previous_state_hash` below is the parent LINK; a tip's own identity
still comes from the peer's framing. That row is open in the table, stated as open.
-/
import Dregg2.Bridge.MinaChainSelection
import Dregg2.Circuit.Emit.Blake2bGadget

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaBinprot

open Dregg2.Bridge.MinaChainSelection

/-! ## §1 — The parser.

A byte cursor with `Option` failure. Bytes are `Nat`s below 256; consuming from the head of a `List`
keeps every step `O(1)`. There is no lenient mode and no recovery: any deviation is `none`, and every
caller treats `none` as a REFUSAL. -/

/-- The parser: consume a prefix of the cursor or fail. -/
def P (α : Type) : Type := List Nat → Option (α × List Nat)

instance : Monad P where
  pure a := fun s => some (a, s)
  bind m f := fun s =>
    match m s with
    | some (a, s') => f a s'
    | none => none

/-- Fail. -/
def pfail {α : Type} : P α := fun _ => none

/-- Succeed only if the condition holds — the shape every refusal below takes. -/
def guardP (b : Bool) : P Unit := fun s => if b then some ((), s) else none

/-- One byte. -/
def u8 : P Nat := fun s =>
  match s with
  | [] => none
  | b :: rest => if b < 256 then some (b, rest) else none

/-- Exactly `n` bytes. -/
def takeN : Nat → P (List Nat)
  | 0 => pure []
  | n + 1 => do
      let b ← u8
      let r ← takeN n
      pure (b :: r)

/-- Little-endian `Nat` from a byte list. -/
def leNat : List Nat → Nat
  | [] => 0
  | b :: rest => b + 256 * leNat rest

/-- **binprot `Nat0`** (list and string lengths), CANONICAL widths only.

Mirrors `mina_pickles`'s Rust reader byte-for-byte, and the reason both refuse a non-canonical width
is the same: a length is an input to a bound check, and two encodings of one length is a way to say
the same thing twice. -/
def nat0 : P Nat := do
  let c ← u8
  if c < 0x80 then pure c
  else if c == 0xfe then do
    let v ← takeN 2
    let n := leNat v
    if n < 0x80 then pfail else pure n
  else if c == 0xfd then do
    let v ← takeN 4
    let n := leNat v
    if n < 0x10000 then pfail else pure n
  else if c == 0xfc then do
    let v ← takeN 8
    let n := leNat v
    if n < 0x100000000 then pfail else pure n
  else pfail

/-- **binprot signed integer**, CANONICAL widths only, as an `Int`.

This is what `Length` / `Currency.Amount` / `Block_time` all ride on: OCaml's `bin_write_int` on the
`Unsigned_extended` representation. A `Length` therefore arrives as a small non-negative int; a large
`Amount` arrives with the sign bit set and is reinterpreted below. -/
def binInt : P Int := do
  let c ← u8
  if c < 0x80 then pure (Int.ofNat c)
  else if c == 0xff then do
    let v ← takeN 1
    let n := leNat v
    -- NEG_INT8: must actually be negative.
    if n < 0x80 then pfail else pure (Int.ofNat n - 256)
  else if c == 0xfe then do
    let v ← takeN 2
    let n := leNat v
    let i : Int := if n < 0x8000 then Int.ofNat n else Int.ofNat n - 65536
    if (0 ≤ i ∧ i < 0x80) ∨ (-0x80 ≤ i ∧ i < 0) then pfail else pure i
  else if c == 0xfd then do
    let v ← takeN 4
    let n := leNat v
    let i : Int := if n < 0x80000000 then Int.ofNat n else Int.ofNat n - 4294967296
    if -0x8000 ≤ i ∧ i < 0x8000 then pfail else pure i
  else if c == 0xfc then do
    let v ← takeN 8
    let n := leNat v
    let i : Int := if n < 0x8000000000000000 then Int.ofNat n else Int.ofNat n - 18446744073709551616
    if -0x80000000 ≤ i ∧ i < 0x80000000 then pfail else pure i
  else pfail

/-- A `Length` / `UInt32`: a binprot signed int that must land in `[0, 2^32)`. -/
def lengthU32 : P Nat := do
  let i ← binInt
  if 0 ≤ i ∧ i < 4294967296 then pure i.toNat else pfail

/-- A `Currency.Amount` / `Block_time` / `UInt64`: the same signed int REINTERPRETED as `u64` (an
amount above `2^63` legitimately arrives negative). -/
def amountU64 : P Nat := do
  let i ← binInt
  if 0 ≤ i then pure i.toNat
  else pure (i + 18446744073709551616).toNat

/-- binprot `unit` — one `0x00` byte. Load-bearing structure, not padding. -/
def unitB : P Unit := do
  let b ← u8
  if b == 0 then pure () else pfail

/-- binprot `bool`. -/
def boolB : P Bool := do
  let b ← u8
  if b == 0 then pure false else if b == 1 then pure true else pfail

/-- The **Pallas base field** prime `p` — the field every `State_hash`, `Ledger_hash`, `Epoch_seed`
and compressed-public-key `x` lives in (o1-labs `proof-systems`,
`curves/src/pasta/fields/fp.rs`; the same constant `Circuit.Emit.PastaField.pN` carries). -/
def pallasBaseModulus : Nat :=
  28948022309329048855892746252171976963363056481941560715954676764349967630337

/-- A field element: 32 LITTLE-ENDIAN bytes, REFUSED unless canonical (`< p`).

Returns its NUMERIC value, which is exactly the representation `ConsensusState`'s checkpoint fields
use — "the ordering the OCaml `compare` on `Snark_params.Tick.Field.t` uses". No conversion. -/
def fpLE : P Nat := do
  let bs ← takeN 32
  let v := leNat bs
  if v < pallasBaseModulus then pure v else pfail

/-- `Bounded_types.String.Stable.V1` — a `Nat0` length then raw bytes, bounded. -/
def byteString (cap : Nat) : P (List Nat) := do
  let n ← nat0
  if n > cap then pfail else takeN n

/-- A single-constructor OCaml variant (`Since_hard_fork of t`): one tag byte, which must be `0`. -/
def singleVariant {α : Type} (p : P α) : P α := do
  let t ← u8
  if t == 0 then p else pfail

/-- `Public_key.Compressed.Stable.V1 = { x : Fp; is_odd : bool }` — walked, value discarded (nothing
`select` reads is in it, but binprot has no way to skip what it has not parsed). -/
def compressedPk : P Unit := do
  let _ ← fpLE
  let _ ← boolB
  pure ()

/-! ## §2 — Blake2b-256, so the VRF digest is DERIVED and not a carrier.

Chain selection's second tie-break compares `Blake2b(last_vrf_output)` bytewise
(`proof_of_stake.ml:3026-3031`; openmina `consensus.rs:143`), while the WIRE carries the raw
truncated VRF output. Taking the digest as a bit supplied by Rust would put a hash — a piece of the
comparison's meaning — outside the semantics. `Circuit.Emit.Blake2bGadget.compress` is already here,
import-free, and already anchored against `hashlib.blake2b` reference vectors, so the digest is
computed instead. -/

open Dregg2.Circuit.Emit.Blake2bGadget.Ref in
/-- The Blake2b-256 parameter block: `IV[0] ^= 0x01010000 | (kk <<< 8) | nn` with key length `kk = 0`
and digest size `nn = 32`. (`h0Default` in the gadget is the `nn = 64` variant.) -/
def h0_256 : List Nat := IV.set 0 (xorw (IV.getD 0 0) 0x01010020)

/-- Pack up to 128 message bytes into the 16 little-endian 64-bit words of one Blake2b block. -/
def blockOfBytes (bs : List Nat) : List Nat :=
  (List.range 16).map (fun i => leNat (((bs.drop (i * 8)) ++ List.replicate 8 0).take 8))

/-- Split a 64-bit word into its 8 little-endian bytes. -/
def wordBytesLE (w : Nat) : List Nat := (List.range 8).map (fun i => (w / 256 ^ i) % 256)

open Dregg2.Circuit.Emit.Blake2bGadget.Ref in
/-- **`blake2b256`** for a SINGLE-BLOCK message (`‖m‖ ≤ 128`), which is all this file needs: the
truncated VRF output is 32 bytes. Returns the 32 digest bytes. -/
def blake2b256 (msg : List Nat) : List Nat :=
  let out := compress h0_256 (blockOfBytes msg) msg.length 0 FF 0
  ((out.take 4).flatMap wordBytesLE)

-- Reference anchors, against `hashlib.blake2b(…, digest_size=32)`. These are the same kind of
-- external ground truth the gadget's own `#guard`s use, and they are what makes the digest a
-- DERIVATION rather than a claim.
#guard blake2b256 (List.replicate 32 0) ==
  [137, 235, 13, 106, 138, 105, 29, 174, 44, 209, 94, 208, 54, 153, 49, 206,
   10, 148, 158, 202, 250, 92, 63, 147, 248, 18, 24, 51, 100, 110, 21, 195]
#guard blake2b256 (List.replicate 32 7) ==
  [23, 205, 199, 188, 163, 242, 160, 189, 166, 12, 109, 229, 185, 111, 130, 163,
   98, 57, 180, 75, 222, 57, 122, 56, 98, 213, 41, 186, 139, 61, 124, 98]
#guard blake2b256 [] ==
  [14, 87, 81, 192, 38, 229, 67, 178, 232, 171, 46, 176, 96, 153, 218, 161,
   209, 229, 223, 71, 119, 143, 119, 135, 250, 171, 69, 205, 241, 47, 227, 168]

/-! ## §3 — The protocol constants the block CARRIES.

⚑ These are PEER-SUPPLIED, so nothing that decides anything may read them. They are decoded in order
to be REFUSED when they disagree with the pin — `MinaForkChoiceGate` fixes `mainnet` in Lean, and if
a peer could supply both the states and the constants it could supply the ones that make its fork
win. -/

/-- `Genesis_constants.Protocol.Poly.Stable.V1` (`genesis_constants.ml:246-252`). -/
structure CarriedConstants where
  /-- `k`, the depth of finality. -/
  k : Nat
  /-- `slots_per_epoch`. -/
  slotsPerEpoch : Nat
  /-- `slots_per_sub_window`. -/
  slotsPerSubWindow : Nat
  /-- `grace_period_slots`. -/
  gracePeriodSlots : Nat
  /-- `delta`. -/
  delta : Nat
  /-- `genesis_state_timestamp`, milliseconds. Not consensus-relevant; a hard fork moves it. -/
  genesisStateTimestamp : Nat
deriving Repr, DecidableEq

/-- Whether a block's carried constants agree with a pinned `Constants` on every value `select`
depends on. `genesisStateTimestamp` is excluded deliberately: no rule reads it. -/
def CarriedConstants.agreesWith (c : CarriedConstants) (C : Constants) : Bool :=
  c.k == C.k && c.slotsPerEpoch == C.slotsPerEpoch
    && c.slotsPerSubWindow == C.slotsPerSubWindow
    && c.gracePeriodSlots == C.gracePeriodSlots && c.delta == C.delta

/-- `sub_windows_per_window`. ⚑ A CONSTRAINT constant (it sizes the in-circuit density window,
`genesis_constants.ml:46,91`), therefore NOT in `Protocol_constants_checked` and NOT peer-supplied. -/
def subWindowsPerWindow : Nat := 11

/-! ## §4 — The records, in binprot order. -/

/-- `Mina_base.Epoch_data.Poly.Stable.V1` — ⚑ `ledger` FIRST, then `seed`. Only `lock_checkpoint`
is read by `select`; the rest is walked because it must be. Returns the lock checkpoint. -/
def epochData : P Nat := do
  let _ledgerHash ← fpLE
  let _ledgerTotalCurrency ← amountU64
  let _seed ← fpLE
  let _startCheckpoint ← fpLE
  let lockCheckpoint ← fpLE
  let _epochLength ← lengthU32
  pure lockCheckpoint

/-- `(Amount, Sgn) Signed_poly.Stable.V1 = { magnitude; sgn }`. -/
def signedAmount : P Unit := do
  let _ ← amountU64
  let s ← u8
  if s == 0 ∨ s == 1 then pure () else pfail

/-- `Mina_transaction_logic.Zkapp_command_logic.Local_state.Stable.V1`. -/
def localState : P Unit := do
  let _stackFrame ← fpLE
  let _callStack ← fpLE
  let _txnCommitment ← fpLE
  let _fullTxnCommitment ← fpLE
  let _ ← signedAmount   -- excess
  let _ ← signedAmount   -- supply_increase
  let _ledger ← fpLE
  let _success ← boolB
  let _accountUpdateIndex ← lengthU32
  -- `failure_status_tbl : Failure.t list list`; every `Failure` constructor is nullary.
  let outer ← nat0
  let _ ← guardP (outer ≤ 1024)
  let _ ← forEachN outer (do
    let inner ← nat0
    let _ ← guardP (inner ≤ 1024)
    forEachN inner (do let _ ← u8; pure ()))
  let _willSucceed ← boolB
  pure ()
where
  /-- Run a unit parser `n` times. -/
  forEachN : Nat → P Unit → P Unit
    | 0, _ => pure ()
    | n + 1, p => do let _ ← p; forEachN n p

/-- `Registers.Stable.V1`. -/
def registers : P Unit := do
  let _firstPass ← fpLE
  let _secondPass ← fpLE
  let _coinbaseData ← fpLE
  let _stackInit ← fpLE
  let _stackCurr ← fpLE
  localState

/-- `Fee_excess.Stable.V1`. -/
def feeExcess : P Unit := do
  let _tokenL ← fpLE
  let _ ← signedAmount
  let _tokenR ← fpLE
  let _ ← signedAmount
  pure ()

/-- `Mina_state.Blockchain_state.Value.Stable.V2` — walked in full, discarded. It sits between
`genesis_state_hash` and `consensus_state`, and binprot gives no length to jump it by. -/
def blockchainState : P Unit := do
  let _stagedLedgerHash ← fpLE
  let _auxHash ← byteString 4096
  let _pendingCoinbaseAux ← byteString 4096
  let _pendingCoinbaseHash ← fpLE
  let _genesisLedgerHash ← fpLE
  let _ ← registers          -- ledger_proof_statement.source
  let _ ← registers          -- ledger_proof_statement.target
  let _connectingLeft ← fpLE
  let _connectingRight ← fpLE
  let _ ← signedAmount       -- supply_increase
  let _ ← feeExcess
  -- ⚑ `sok_digest : unit` — OCaml's `bin_write_unit` writes ONE `0x00` byte. It is not free, and
  -- assuming it was is what made this decoder REFUSE a real devnet block: everything after it read
  -- one byte early, and the shift survived twenty canonical field-element checks before surfacing
  -- as a timestamp of 0. (The same fact is why `mina_pickles`'s reader has a `unit` primitive: it
  -- terminates every OCaml fixed-length `Vector`.)
  let _ ← unitB
  let _timestamp ← amountU64
  -- ⚑ `body_reference : Consensus.Body_reference.Stable.V1 = Bounded_types.String` — a LENGTH-
  -- PREFIXED byte string, NOT a bare 32-byte digest. It is a Blake2b hash and it looks like a raw
  -- digest, which is exactly why the `Nat0` in front of it is easy to drop.
  let _bodyReference ← byteString 64
  pure ()

/-- Read exactly `n` `Length`s. -/
def lengths : Nat → P (List Nat)
  | 0 => pure []
  | n + 1 => do
      let x ← lengthU32
      let r ← lengths n
      pure (x :: r)

/-- **`consensusState`** — `Consensus.Data.Consensus_state.Value.Stable.V2`, all fifteen fields, in
binprot order, DIRECTLY into `MinaChainSelection.ConsensusState`.

There is no intermediate structure. The eight fields `select_reads_only_eight_fields` names land in
the eight fields it names; the other seven land in the fields that theorem proves cannot influence
the verdict — which is what makes decoding them safe as well as necessary. -/
def consensusState : P ConsensusState := do
  let blockchainLength ← lengthU32
  let epochCount ← lengthU32
  let minWindowDensity ← lengthU32
  -- `sub_window_densities : Length.t list`. HARD-bounded: the daemon builds it in-circuit as a
  -- `Typ.list ~length:sub_windows_per_window` (`proof_of_stake.ml:1818`), so any other count is
  -- not a Mina consensus state — and a mis-ordered decode lands here first.
  let n ← nat0
  let _ ← guardP (n == subWindowsPerWindow)
  let subWindowDensities ← lengths subWindowsPerWindow
  -- `Vrf.Output.Truncated.Stable.V1` — 32 bytes on every real block (`consensus_vrf.ml:164-168`).
  let vrf ← byteString 64
  let _ ← guardP (vrf.length == 32)
  let totalCurrency ← amountU64
  let currGlobalSlot ← singleVariant lengthU32
  let slotsPerEpoch ← lengthU32
  -- `Global_slot.epoch` divides by the VALUE's own copy (`global_slot.ml:79`), and Lean's `Nat`
  -- division by zero is `0` — which would silently collapse every state into epoch 0 and make
  -- every pair look same-epoch. Refuse instead.
  let _ ← guardP (slotsPerEpoch != 0)
  let globalSlotSinceGenesis ← singleVariant lengthU32
  let stakingLockCheckpoint ← epochData
  let nextLockCheckpoint ← epochData
  let hasAncestor ← boolB
  let _ ← compressedPk    -- block_stake_winner
  let _ ← compressedPk    -- block_creator
  let _ ← compressedPk    -- coinbase_receiver
  let supercharge ← boolB
  pure { blockchainLength, minWindowDensity, subWindowDensities,
         -- ⚑ DERIVED, not carried: chain selection compares the DIGEST.
         lastVrfHash := blake2b256 vrf,
         currGlobalSlot, slotsPerEpoch, stakingLockCheckpoint, nextLockCheckpoint,
         epochCount, totalCurrency, globalSlotSinceGenesis,
         -- Not on the wire in a form `select` reads, and proven not to matter; zeroed rather than
         -- invented. (`stakingSeed` etc. ARE on the wire and ARE walked above — they are dropped
         -- here because `select_reads_only_eight_fields` proves the verdict cannot see them.)
         stakingSeed := 0, stakingStartCheckpoint := 0, stakingEpochLength := 0,
         stakingLedgerHash := 0, nextSeed := 0, nextStartCheckpoint := 0, nextEpochLength := 0,
         nextLedgerHash := 0,
         hasAncestorInSameCheckpointWindow := hasAncestor,
         blockStakeWinner := 0, blockCreator := 0, coinbaseReceiver := 0,
         superchargeCoinbase := supercharge }

/-- `Genesis_constants.Protocol.Poly.Stable.V1`. -/
def carriedConstants : P CarriedConstants := do
  let k ← lengthU32
  let slotsPerEpoch ← lengthU32
  let slotsPerSubWindow ← lengthU32
  let gracePeriodSlots ← lengthU32
  let delta ← lengthU32
  let genesisStateTimestamp ← amountU64
  pure { k, slotsPerEpoch, slotsPerSubWindow, gracePeriodSlots, delta, genesisStateTimestamp }

/-- A decoded `Protocol_state.Value.Stable.V2`. -/
structure ProtocolState where
  /-- `previous_state_hash` — the parent LINK, as its numeric field element. -/
  previousStateHash : Nat
  /-- `body.genesis_state_hash`. -/
  genesisStateHash : Nat
  /-- `body.consensus_state` — the object `select` runs on, with no conversion. -/
  consensus : ConsensusState
  /-- `body.constants` — PEER-SUPPLIED. Only ever compared against the pin, never adopted. -/
  constants : CarriedConstants
deriving Repr, DecidableEq

/-- **`protocolState`** — `{ previous_state_hash; body }` with
`body = { genesis_state_hash; blockchain_state; consensus_state; constants }`. -/
def protocolState : P ProtocolState := do
  let previousStateHash ← fpLE
  let genesisStateHash ← fpLE
  let _ ← blockchainState
  let consensus ← consensusState
  let constants ← carriedConstants
  pure { previousStateHash, genesisStateHash, consensus, constants }

/-! ## §5 — The entry points, and what they REFUSE. -/

/-- **`decodeProtocolState`** — decode a `Protocol_state.Value.Stable.V2` from a byte prefix,
returning it and the UNCONSUMED remainder.

Deliberately a PREFIX decode: on the peer-to-peer wire the protocol state is followed by the Wrap
proof and then the whole block body, and this file's job ends at the consensus state. The remainder
is returned rather than ignored so a caller can say how many bytes were accounted for. -/
def decodeProtocolState (bs : List Nat) : Option (ProtocolState × List Nat) := protocolState bs

/-- **`decodeProtocolStateChecked`** — decode AND apply every structural refusal.

Each conjunct is something a field-order slip breaks immediately, which is what makes this a check
on the DECODE and not only on the block:

  * the carried constants agree with the PINNED ones (a peer cannot move `grace_period_end`),
  * every sub-window density is at most `slots_per_sub_window` (⚑ and this is NOT an invariant of
    the update function alone — `MinaSlidingWindow` proves `step` yields 8 at mainnet constants
    absent the strict slot increase block validity enforces — so checking the SERVED value is the
    right place for it),
  * `min_window_density ≤ slots_per_window`,
  * the value's own `slots_per_epoch` matches the pinned one.

The density-count and 32-byte-VRF refusals live in `consensusState` itself, because a wrong count is
what a mis-ordered decode produces and it must not survive to here. -/
def decodeProtocolStateChecked (C : Constants) (bs : List Nat) :
    Option (ProtocolState × List Nat) :=
  match decodeProtocolState bs with
  | none => none
  | some (ps, rest) =>
      if ps.constants.agreesWith C
        && ps.consensus.subWindowDensities.all (· ≤ C.slotsPerSubWindow)
        && ps.consensus.minWindowDensity ≤ C.slotsPerWindow
        && ps.consensus.slotsPerEpoch == C.slotsPerEpoch
      then some (ps, rest) else none

/-! ## §6 — NON-VACUITY: the decoder ACCEPTS a well-formed state and REFUSES each mutation.

Built by an encoder written for the tests only. ⚑ The encoder is NOT a second rendering to be kept
in agreement with the decoder — it exists so the refusals below can be exhibited on bytes that differ
from an accepted encoding in exactly ONE place. The ground truth for the FORMAT is the daemon and
openmina (cited in the header) plus the live wire; the ground truth for BLAKE2B is `hashlib`. -/

/-- Encode a small `Nat` (`< 0x80`) as a one-byte binprot int. -/
def e1 (n : Nat) : List Nat := [n]

/-- Encode a `Nat` below `2^16` in the canonical binprot int width. -/
def eInt (n : Nat) : List Nat :=
  if n < 0x80 then [n]
  else if n < 0x8000 then [0xfe, n % 256, (n / 256) % 256]
  else [0xfd, n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]

/-- Encode a field element as 32 little-endian bytes. -/
def eFp (v : Nat) : List Nat := (List.range 32).map (fun i => (v / 256 ^ i) % 256)

/-- A test consensus state's bytes: 11 densities, a 32-byte VRF output, two epoch datas. -/
def sampleConsensusBytes (densities : List Nat) (vrfLen : Nat) (spe : Nat) : List Nat :=
  eInt 1000 ++ eInt 3 ++ eInt 50
  ++ [densities.length] ++ densities.flatMap eInt
  ++ [vrfLen] ++ List.replicate vrfLen 7
  ++ eInt 1234
  ++ [0] ++ eInt 7212            -- curr_global_slot (Since_hard_fork)
  ++ eInt spe
  ++ [0] ++ eInt 7212            -- global_slot_since_genesis (Since_genesis)
  -- staking_epoch_data: ledger.hash, ledger.total_currency, seed, start, lock, epoch_length
  ++ eFp 1 ++ eInt 9 ++ eFp 2 ++ eFp 3 ++ eFp 1044 ++ eInt 11
  -- next_epoch_data
  ++ eFp 4 ++ eInt 9 ++ eFp 5 ++ eFp 6 ++ eFp 77 ++ eInt 12
  ++ [1]                          -- has_ancestor_in_same_checkpoint_window
  ++ eFp 7 ++ [0] ++ eFp 8 ++ [0] ++ eFp 9 ++ [0]   -- the three compressed public keys
  ++ [0]                          -- supercharge_coinbase

/-- The eleven real-looking densities. -/
def d11 : List Nat := [6, 5, 5, 5, 5, 5, 5, 6, 6, 6, 7]

/-- **THE DECODER ACCEPTS**, consumes every byte, and puts each field where it belongs — including
the two `lock_checkpoint`s, which are the FOURTH field element of their epoch data because `ledger`
comes first. -/
def wellformedDecodeCheck : Bool :=
  match consensusState (sampleConsensusBytes d11 32 7140) with
  | some (c, rest) =>
      c.blockchainLength == 1000 && c.epochCount == 3 && c.minWindowDensity == 50
      && c.subWindowDensities == d11 && c.currGlobalSlot == 7212 && c.slotsPerEpoch == 7140
      -- ⚑ the two `lock_checkpoint`s are the FOURTH field element of their epoch data, because
      -- `ledger` comes first. A `seed`-first decoder reads 2 and 5 here.
      && c.stakingLockCheckpoint == 1044 && c.nextLockCheckpoint == 77
      && rest.isEmpty
  | none => false

theorem consensus_decodes_a_wellformed_state : wellformedDecodeCheck = true := by native_decide

/-- ⚑ **TEN DENSITIES IS A REFUSAL**, not a shorter window. This is what the public GraphQL surface
can supply (nothing) and what a mis-ordered decode produces. -/
theorem ten_densities_is_refused :
    consensusState (sampleConsensusBytes (d11.take 10) 32 7140) = none := by native_decide

/-- A VRF output that is not 32 bytes is a REFUSAL — the digest's pre-image length is part of the
comparison's meaning, not a detail. -/
theorem a_short_vrf_output_is_refused :
    consensusState (sampleConsensusBytes d11 31 7140) = none := by native_decide

/-- ⚑ **`slots_per_epoch = 0` IS A REFUSAL.** Lean's `Nat` division by zero is `0`, so admitting it
would silently place every state in epoch 0 and make every pair look same-epoch — the short-range
branch would then decide every fork. -/
theorem zero_slots_per_epoch_is_refused :
    consensusState (sampleConsensusBytes d11 32 0) = none := by native_decide

/-- ⚑ **A NON-CANONICAL INTEGER WIDTH IS A REFUSAL.** `blockchain_length` written in the 16-bit form
when it fits in one byte is rejected rather than read as the same number. -/
theorem a_widened_length_is_refused :
    consensusState ([0xfe, 0x03, 0x00] ++ (sampleConsensusBytes d11 32 7140).drop 3) = none := by
  native_decide

/-- ⚑ **A NON-CANONICAL FIELD ELEMENT IS A REFUSAL.** `p` itself, little-endian, in the staking
epoch data's `ledger.hash` slot: `x` and `x + p` are one element at the digest and must not have two
encodings. -/
theorem a_non_canonical_field_element_is_refused :
    epochData (eFp pallasBaseModulus ++ eInt 9 ++ eFp 2 ++ eFp 3 ++ eFp 4 ++ eInt 11) = none := by
  native_decide

/-- The VRF digest really is the Blake2b of the wire bytes, not the wire bytes. -/
def vrfDigestCheck : Bool :=
  match consensusState (sampleConsensusBytes d11 32 7140) with
  | some (c, _) => c.lastVrfHash == blake2b256 (List.replicate 32 7)
                     && c.lastVrfHash != List.replicate 32 7
  | none => false

theorem the_vrf_digest_is_derived : vrfDigestCheck = true := by native_decide

/-- ⚑ **THE DECODED STATE FEEDS `select` WITH NO CONVERSION**, and the fork-choice verdict on two
decoded states is a real verdict: a decoded state does not displace itself, and a decoded state with
a strictly greater `blockchain_length` at the same staking lock checkpoint does.

This is the point of the whole file — the parser's output type IS the type the tournament theorems
are stated over. -/
def decodedPair : Option (ConsensusState × ConsensusState) :=
  -- The same bytes with `blockchain_length` 1000 replaced by 2000 (both encode to three bytes).
  match consensusState (sampleConsensusBytes d11 32 7140),
        consensusState (eInt 2000 ++ (sampleConsensusBytes d11 32 7140).drop 3) with
  | some (a, _), some (b, _) => some (a, b)
  | _, _ => none

def selectDrivenByDecodeCheck : Bool :=
  match decodedPair with
  | some (a, b) =>
      (minaBetterTip mainnet a a 1 1 == false) && (minaBetterTip mainnet a b 1 2 == true)
      && (minaBetterTip mainnet b a 2 1 == false)
  | none => false

theorem a_decoded_state_drives_select : selectDrivenByDecodeCheck = true := by native_decide

/-- ⚑ **A PEER CANNOT MOVE THE GRACE PERIOD.** Constants that disagree with the pin are refused
rather than adopted; `1363 + 77 = 1440` is exactly the wrong `grace_period_end` that both the spec
table and openmina carry, so this is the mutation that matters. -/
theorem carried_constants_that_disagree_are_refused :
    (CarriedConstants.agreesWith
      { k := 290, slotsPerEpoch := 7140, slotsPerSubWindow := 7, gracePeriodSlots := 2160,
        delta := 0, genesisStateTimestamp := 0 } mainnet = true)
    ∧ (CarriedConstants.agreesWith
      { k := 290, slotsPerEpoch := 7140, slotsPerSubWindow := 7, gracePeriodSlots := 1363,
        delta := 0, genesisStateTimestamp := 0 } mainnet = false) := by decide

/-- And the pinned constants really are the ones the derived grace-period end depends on. -/
theorem the_pin_is_the_daemons_grace_period :
    mainnet.gracePeriodEnd = 2237 ∧ mainnet.slotsPerWindow = 77
    ∧ subWindowsPerWindow = mainnet.subWindowsPerWindow := by decide

/-! ## §7 — axiom hygiene.

⚑ The decode theorems use `native_decide` and therefore carry `Lean.ofReduceBool` — they are
EXECUTION results, not kernel reductions, and that is stated rather than hidden. The parser uses
well-founded recursion over a byte list that the kernel will not reduce at these sizes. The
STRUCTURAL facts (`carried_constants_that_disagree_are_refused`,
`the_pin_is_the_daemons_grace_period`) are kernel `decide` and carry no such axiom. -/

#assert_axioms carried_constants_that_disagree_are_refused
#assert_axioms the_pin_is_the_daemons_grace_period

#print axioms consensus_decodes_a_wellformed_state
#print axioms a_decoded_state_drives_select
#print axioms carried_constants_that_disagree_are_refused

end Dregg2.Bridge.MinaBinprot
