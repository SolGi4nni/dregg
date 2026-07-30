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
     costs a leading tag byte before its integer — and the two are NOT the same shape.
     `curr_global_slot_since_hard_fork` is `Consensus.Global_slot = { slot_number; slots_per_epoch }`
     (`consensus/global_slot.ml:22-24`), a PAIR of `u32`s of which the second is the value's own
     `slots_per_epoch`; `global_slot_since_genesis` is a bare `Mina_numbers` wrapper, one `u32`.
     Both halves of the pair are absorbed by `Global_slot.to_input` (`global_slot.ml:50-52`), so a
     reader that assumes symmetry either drops a `u32` from the hash preimage or invents one.

## Canonicality is enforced, not assumed

Every `Nat0` and every signed integer must arrive in its CANONICAL width (a `Length` of 3 written as
`0xfe 03 00` is a REFUSAL, not a 3), and every field element must be `< p`. The second one is not
hygiene: Poseidon's `absorbAt` enters every input through `(state + x) % p`, so `x` and `x + p` are
the same element at the digest, and a checkpoint admitted in two encodings is a checkpoint that
compares unequal to itself.

## What is decoded, and what is deliberately not

`Protocol_state.Value.Stable.V2` is decoded ENTIRE — `Blockchain_state` included, down to
`aux_hash` and `pending_coinbase_aux`. The block BODY (a whole staged-ledger diff) and the header
fields after the Wrap proof are not reached by this file at all; `decodeProtocolStateRaw` is total on
its prefix and says how many bytes it used.

⚑ **2026-07-30: `Blockchain_state` stopped being discarded.** It used to be walked-and-dropped on
the grounds that `select` reads nothing in it. `select` still reads nothing in it — but `state_hash`
is `Poseidon(prefix "MinaProtoState")[previous_state_hash, Body.hash body]` and `Body.hash` absorbs
ALL of it, so dropping it was precisely why a tip's own identity could not be re-derived and had to
be taken from the peer's framing. `Bridge.MinaStateHashDerive` closes that; this file's job was to
stop throwing the preimage away.

**ONE PARSER, TWO VIEWS.** `protocolStateRaw` reads the bytes. `ProtocolStateRaw.view` projects the
fork-choice `ProtocolState` (and `ConsensusRaw.toSelection` the `ConsensusState` the tournament
theorems are stated over, applying `blake2b256` to the raw VRF bytes on the way). No byte is read
twice and there is no second structure to keep in agreement — the digest is what the RULE needs,
the raw bytes are what the HASH needs, and both come out of one decode.
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

/-- `Public_key.Compressed.Stable.V1 = { x : Fp; is_odd : bool }`. Nothing `select` reads is in it,
but `Body.to_input` absorbs both halves, so both are RETAINED. -/
structure Pk where
  /-- The compressed `x` coordinate. -/
  x : Nat
  /-- The parity bit. -/
  isOdd : Bool
deriving Repr, DecidableEq

/-- `Public_key.Compressed.Stable.V1`. -/
def compressedPk : P Pk := do
  let x ← fpLE
  let isOdd ← boolB
  pure { x, isOdd }

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
is read by `select`, but `Body.to_input` absorbs ALL SIX in a DIFFERENT order
(`proof_of_stake.ml:1007-1017`: seed, start, epoch_length, ledger, lock), so all six are retained. -/
structure EpochRaw where
  /-- `ledger.hash`. -/
  ledgerHash : Nat
  /-- `ledger.total_currency`. -/
  ledgerTotalCurrency : Nat
  /-- `seed`. -/
  seed : Nat
  /-- `start_checkpoint`. -/
  startCheckpoint : Nat
  /-- `lock_checkpoint` — the field `is_short_range` keys on. -/
  lockCheckpoint : Nat
  /-- `epoch_length`. -/
  epochLength : Nat
deriving Repr, DecidableEq

/-- `Mina_base.Epoch_data.Poly.Stable.V1`, in BINPROT order. -/
def epochData : P EpochRaw := do
  let ledgerHash ← fpLE
  let ledgerTotalCurrency ← amountU64
  let seed ← fpLE
  let startCheckpoint ← fpLE
  let lockCheckpoint ← fpLE
  let epochLength ← lengthU32
  pure { ledgerHash, ledgerTotalCurrency, seed, startCheckpoint, lockCheckpoint, epochLength }

/-- `(Amount, Sgn) Signed_poly.Stable.V1 = { magnitude; sgn }`. `Sgn.t = Pos | Neg` is a nullary
two-constructor variant, so its tag byte IS the value; `Amount.Signed.to_input` absorbs
`sgn_to_bool Pos = true` (`currency.ml:494`). -/
structure SignedAmt where
  /-- `magnitude`, a `u64`. -/
  magnitude : Nat
  /-- `sgn = Pos`. -/
  isPos : Bool
deriving Repr, DecidableEq

/-- `(Amount, Sgn) Signed_poly.Stable.V1`. -/
def signedAmount : P SignedAmt := do
  let magnitude ← amountU64
  let s ← u8
  if s == 0 then pure { magnitude, isPos := true }
  else if s == 1 then pure { magnitude, isPos := false }
  else pfail

/-- `Mina_transaction_logic.Zkapp_command_logic.Local_state.Stable.V1`. ⚑ `failure_status_tbl` is
walked and DROPPED — `local_state.ml:120` excludes it from `to_input` explicitly, so it is the one
decoded field that is genuinely not in the hash preimage. -/
structure LocalRaw where
  /-- `stack_frame`. -/
  stackFrame : Nat
  /-- `call_stack`. -/
  callStack : Nat
  /-- `transaction_commitment`. -/
  txnCommitment : Nat
  /-- `full_transaction_commitment`. -/
  fullTxnCommitment : Nat
  /-- `excess`. -/
  excess : SignedAmt
  /-- `supply_increase`. -/
  supplyIncrease : SignedAmt
  /-- `ledger`. -/
  ledger : Nat
  /-- `success`. -/
  success : Bool
  /-- `account_update_index`, a `u32`. -/
  accountUpdateIndex : Nat
  /-- `will_succeed`. -/
  willSucceed : Bool
deriving Repr, DecidableEq

/-- Run a unit parser `n` times. -/
def forEachN : Nat → P Unit → P Unit
  | 0, _ => pure ()
  | n + 1, p => do let _ ← p; forEachN n p

/-- `Mina_transaction_logic.Zkapp_command_logic.Local_state.Stable.V1`, in BINPROT order. -/
def localState : P LocalRaw := do
  let stackFrame ← fpLE
  let callStack ← fpLE
  let txnCommitment ← fpLE
  let fullTxnCommitment ← fpLE
  let excess ← signedAmount
  let supplyIncrease ← signedAmount
  let ledger ← fpLE
  let success ← boolB
  let accountUpdateIndex ← lengthU32
  -- `failure_status_tbl : Failure.t list list`; every `Failure` constructor is nullary.
  let outer ← nat0
  let _ ← guardP (outer ≤ 1024)
  let _ ← forEachN outer (do
    let inner ← nat0
    let _ ← guardP (inner ≤ 1024)
    forEachN inner (do let _ ← u8; pure ()))
  let willSucceed ← boolB
  pure { stackFrame, callStack, txnCommitment, fullTxnCommitment, excess, supplyIncrease,
         ledger, success, accountUpdateIndex, willSucceed }

/-- `Registers.Stable.V1` — `{ first_pass_ledger; second_pass_ledger; pending_coinbase_stack;
local_state }`, where the stack is `{ data; state = { init; curr } }` (three field elements). -/
structure RegistersRaw where
  /-- `first_pass_ledger`. -/
  firstPassLedger : Nat
  /-- `second_pass_ledger`. -/
  secondPassLedger : Nat
  /-- `pending_coinbase_stack.data`. -/
  coinbaseStackData : Nat
  /-- `pending_coinbase_stack.state.init`. -/
  coinbaseStackInit : Nat
  /-- `pending_coinbase_stack.state.curr`. -/
  coinbaseStackCurr : Nat
  /-- `local_state`. -/
  local_ : LocalRaw
deriving Repr, DecidableEq

/-- `Registers.Stable.V1`. -/
def registers : P RegistersRaw := do
  let firstPassLedger ← fpLE
  let secondPassLedger ← fpLE
  let coinbaseStackData ← fpLE
  let coinbaseStackInit ← fpLE
  let coinbaseStackCurr ← fpLE
  let local_ ← localState
  pure { firstPassLedger, secondPassLedger, coinbaseStackData, coinbaseStackInit,
         coinbaseStackCurr, local_ }

/-- `Fee_excess.Stable.V1`. -/
structure FeeExcessRaw where
  /-- `fee_token_l`. -/
  tokenL : Nat
  /-- `fee_excess_l`. -/
  feeL : SignedAmt
  /-- `fee_token_r`. -/
  tokenR : Nat
  /-- `fee_excess_r`. -/
  feeR : SignedAmt
deriving Repr, DecidableEq

/-- `Fee_excess.Stable.V1`. -/
def feeExcess : P FeeExcessRaw := do
  let tokenL ← fpLE
  let feeL ← signedAmount
  let tokenR ← fpLE
  let feeR ← signedAmount
  pure { tokenL, feeL, tokenR, feeR }

/-- `Mina_state.Blockchain_state.Value.Stable.V2` — ⚑ **RETAINED IN FULL.** Until 2026-07-30 this
was walked and discarded, on the grounds that `select` reads nothing in it. `select` still reads
nothing in it — but `state_hash` is a hash of ALL of it, so discarding it was exactly why a tip's
identity could not be re-derived. Every field below is in the `MinaProtoStateBody` preimage.

⚑ `aux_hash` and `pending_coinbase_aux` are RAW BYTES, not field elements: they enter the preimage
only through `SHA-256(BE(ledger_hash) ‖ aux_hash ‖ pending_coinbase_aux)`
(`staged_ledger_hash.ml:183-191`). They are the one place a `Fp` is hashed as BIG-endian bytes. -/
structure BlockchainRaw where
  /-- `staged_ledger_hash.non_snark.ledger_hash`. -/
  slhLedgerHash : Nat
  /-- `staged_ledger_hash.non_snark.aux_hash` — 32 raw bytes. -/
  slhAuxHash : List Nat
  /-- `staged_ledger_hash.non_snark.pending_coinbase_aux` — 32 raw bytes. -/
  slhPendingCoinbaseAux : List Nat
  /-- `staged_ledger_hash.pending_coinbase_hash`. -/
  slhPendingCoinbaseHash : Nat
  /-- `genesis_ledger_hash`. -/
  genesisLedgerHash : Nat
  /-- `ledger_proof_statement.source`. -/
  source : RegistersRaw
  /-- `ledger_proof_statement.target`. -/
  target : RegistersRaw
  /-- `ledger_proof_statement.connecting_ledger_left`. -/
  connectingLeft : Nat
  /-- `ledger_proof_statement.connecting_ledger_right`. -/
  connectingRight : Nat
  /-- `ledger_proof_statement.supply_increase`. -/
  supplyIncrease : SignedAmt
  /-- `ledger_proof_statement.fee_excess`. -/
  fee : FeeExcessRaw
  /-- `timestamp`, milliseconds. -/
  timestamp : Nat
  /-- `body_reference` — 32 raw bytes (a Blake2b digest of the block body). -/
  bodyReference : List Nat
deriving Repr, DecidableEq

/-- `Mina_state.Blockchain_state.Value.Stable.V2`, in BINPROT order. -/
def blockchainState : P BlockchainRaw := do
  let slhLedgerHash ← fpLE
  let slhAuxHash ← byteString 4096
  let slhPendingCoinbaseAux ← byteString 4096
  let slhPendingCoinbaseHash ← fpLE
  let genesisLedgerHash ← fpLE
  let source ← registers          -- ledger_proof_statement.source
  let target ← registers          -- ledger_proof_statement.target
  let connectingLeft ← fpLE
  let connectingRight ← fpLE
  let supplyIncrease ← signedAmount
  let fee ← feeExcess
  -- ⚑ `sok_digest : unit` — OCaml's `bin_write_unit` writes ONE `0x00` byte. It is not free, and
  -- assuming it was is what made this decoder REFUSE a real devnet block: everything after it read
  -- one byte early, and the shift survived twenty canonical field-element checks before surfacing
  -- as a timestamp of 0. (The same fact is why `mina_pickles`'s reader has a `unit` primitive: it
  -- terminates every OCaml fixed-length `Vector`.) `Snarked_ledger_state.to_input` DROPS it —
  -- `sok_digest = _` in the pattern — so it is decoded and never hashed.
  let _ ← unitB
  let timestamp ← amountU64
  -- ⚑ `body_reference : Consensus.Body_reference.Stable.V1 = Bounded_types.String` — a LENGTH-
  -- PREFIXED byte string, NOT a bare 32-byte digest. It is a Blake2b hash and it looks like a raw
  -- digest, which is exactly why the `Nat0` in front of it is easy to drop.
  let bodyReference ← byteString 64
  pure { slhLedgerHash, slhAuxHash, slhPendingCoinbaseAux, slhPendingCoinbaseHash,
         genesisLedgerHash, source, target, connectingLeft, connectingRight, supplyIncrease,
         fee, timestamp, bodyReference }

/-- Read exactly `n` `Length`s. -/
def lengths : Nat → P (List Nat)
  | 0 => pure []
  | n + 1 => do
      let x ← lengthU32
      let r ← lengths n
      pure (x :: r)

/-- `Consensus.Data.Consensus_state.Value.Stable.V2`, all fifteen fields, RETAINED.

⚑ `slotsPerEpoch` is not a fifteenth field of the record: `curr_global_slot_since_hard_fork` has type
`Consensus.Global_slot.Stable.V1 = { slot_number : Global_slot_since_hard_fork.t;
slots_per_epoch : Length.t }` (`consensus/global_slot.ml:22-24`), so the pair is ONE field on the
wire and `Global_slot.to_input` absorbs BOTH u32s (`global_slot.ml:50-52`). `global_slot_since_genesis`
is `Mina_numbers.Global_slot_since_genesis` — a bare `u32` behind its variant tag, one item. That
asymmetry is a trap: a reader who assumes both slots have the same shape either loses a `u32` from
the preimage or invents one. -/
structure ConsensusRaw where
  /-- `blockchain_length`. -/
  blockchainLength : Nat
  /-- `epoch_count`. -/
  epochCount : Nat
  /-- `min_window_density`. -/
  minWindowDensity : Nat
  /-- `sub_window_densities`, exactly `sub_windows_per_window` of them. -/
  subWindowDensities : List Nat
  /-- `last_vrf_output` — the 32 RAW truncated-VRF bytes. ⚑ NOT the Blake2b digest: `select`
  compares the digest, `Body.to_input` absorbs 253 bits of the RAW bytes, and conflating them is a
  way to hash the wrong preimage. -/
  lastVrfOutput : List Nat
  /-- `total_currency`. -/
  totalCurrency : Nat
  /-- `curr_global_slot_since_hard_fork.slot_number`. -/
  currGlobalSlot : Nat
  /-- `curr_global_slot_since_hard_fork.slots_per_epoch`. -/
  slotsPerEpoch : Nat
  /-- `global_slot_since_genesis`. -/
  globalSlotSinceGenesis : Nat
  /-- `staking_epoch_data`. -/
  staking : EpochRaw
  /-- `next_epoch_data`. -/
  next : EpochRaw
  /-- `has_ancestor_in_same_checkpoint_window`. -/
  hasAncestor : Bool
  /-- `block_stake_winner`. -/
  blockStakeWinner : Pk
  /-- `block_creator`. -/
  blockCreator : Pk
  /-- `coinbase_receiver`. -/
  coinbaseReceiver : Pk
  /-- `supercharge_coinbase`. -/
  superchargeCoinbase : Bool
deriving Repr, DecidableEq

/-- **`consensusStateRaw`** — `Consensus.Data.Consensus_state.Value.Stable.V2` in binprot order,
every field retained. -/
def consensusStateRaw : P ConsensusRaw := do
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
  let lastVrfOutput ← byteString 64
  let _ ← guardP (lastVrfOutput.length == 32)
  let totalCurrency ← amountU64
  let currGlobalSlot ← singleVariant lengthU32
  let slotsPerEpoch ← lengthU32
  -- `Global_slot.epoch` divides by the VALUE's own copy (`global_slot.ml:79`), and Lean's `Nat`
  -- division by zero is `0` — which would silently collapse every state into epoch 0 and make
  -- every pair look same-epoch. Refuse instead.
  let _ ← guardP (slotsPerEpoch != 0)
  let globalSlotSinceGenesis ← singleVariant lengthU32
  let staking ← epochData
  let next ← epochData
  let hasAncestor ← boolB
  let blockStakeWinner ← compressedPk
  let blockCreator ← compressedPk
  let coinbaseReceiver ← compressedPk
  let superchargeCoinbase ← boolB
  pure { blockchainLength, epochCount, minWindowDensity, subWindowDensities, lastVrfOutput,
         totalCurrency, currGlobalSlot, slotsPerEpoch, globalSlotSinceGenesis, staking, next,
         hasAncestor, blockStakeWinner, blockCreator, coinbaseReceiver, superchargeCoinbase }

/-- **The projection into `MinaChainSelection.ConsensusState`** — the structure
`select_reads_only_eight_fields`, `beats_not_transitive` and `minaBetterTip_decides` are stated over.

The eight fields that theorem names land in the eight fields it names. The `blake2b256` is applied
HERE and not at the parse, because the wire's raw bytes are what the HASH preimage needs and the
digest is what the RULE needs; one decode, two consumers, no second parser.

⚑ The three compressed public keys stay zeroed. `ConsensusState` types them as `Nat` and a
compressed key is `(x, is_odd)` — filling in `x` alone would put an unfaithful value into a
structure whose whole point is that `select` cannot see it. The faithful pair lives in
`ConsensusRaw` and is what `Body.to_input` absorbs. -/
def ConsensusRaw.toSelection (c : ConsensusRaw) : ConsensusState :=
  { blockchainLength := c.blockchainLength, minWindowDensity := c.minWindowDensity,
    subWindowDensities := c.subWindowDensities,
    -- ⚑ DERIVED, not carried: chain selection compares the DIGEST.
    lastVrfHash := blake2b256 c.lastVrfOutput,
    currGlobalSlot := c.currGlobalSlot, slotsPerEpoch := c.slotsPerEpoch,
    stakingLockCheckpoint := c.staking.lockCheckpoint,
    nextLockCheckpoint := c.next.lockCheckpoint,
    epochCount := c.epochCount, totalCurrency := c.totalCurrency,
    globalSlotSinceGenesis := c.globalSlotSinceGenesis,
    stakingSeed := c.staking.seed, stakingStartCheckpoint := c.staking.startCheckpoint,
    stakingEpochLength := c.staking.epochLength, stakingLedgerHash := c.staking.ledgerHash,
    nextSeed := c.next.seed, nextStartCheckpoint := c.next.startCheckpoint,
    nextEpochLength := c.next.epochLength, nextLedgerHash := c.next.ledgerHash,
    hasAncestorInSameCheckpointWindow := c.hasAncestor,
    blockStakeWinner := 0, blockCreator := 0, coinbaseReceiver := 0,
    superchargeCoinbase := c.superchargeCoinbase }

/-- **`consensusState`** — the decode, projected. -/
def consensusState : P ConsensusState := do
  let c ← consensusStateRaw
  pure c.toSelection

/-- `Genesis_constants.Protocol.Poly.Stable.V1`. -/
def carriedConstants : P CarriedConstants := do
  let k ← lengthU32
  let slotsPerEpoch ← lengthU32
  let slotsPerSubWindow ← lengthU32
  let gracePeriodSlots ← lengthU32
  let delta ← lengthU32
  let genesisStateTimestamp ← amountU64
  pure { k, slotsPerEpoch, slotsPerSubWindow, gracePeriodSlots, delta, genesisStateTimestamp }

/-- **A decoded `Protocol_state.Value.Stable.V2`, ENTIRE** — every field the wire carries, which is
exactly every field `state_hash` is a hash of. `Bridge.MinaStateHashDerive` consumes this. -/
structure ProtocolStateRaw where
  /-- `previous_state_hash` — the parent LINK, as its numeric field element. -/
  previousStateHash : Nat
  /-- `body.genesis_state_hash`. -/
  genesisStateHash : Nat
  /-- `body.blockchain_state`. -/
  blockchain : BlockchainRaw
  /-- `body.consensus_state`, unprojected. -/
  consensus : ConsensusRaw
  /-- `body.constants` — PEER-SUPPLIED. Only ever compared against the pin, never adopted. -/
  constants : CarriedConstants
deriving Repr, DecidableEq

/-- **`protocolStateRaw`** — `{ previous_state_hash; body }` with
`body = { genesis_state_hash; blockchain_state; consensus_state; constants }`. THE parser; every
other entry point below is a projection of this one, so there is no second reading of any byte. -/
def protocolStateRaw : P ProtocolStateRaw := do
  let previousStateHash ← fpLE
  let genesisStateHash ← fpLE
  let blockchain ← blockchainState
  let consensus ← consensusStateRaw
  let constants ← carriedConstants
  pure { previousStateHash, genesisStateHash, blockchain, consensus, constants }

/-- The FORK-CHOICE view of a decoded protocol state: what `select` and the head gate consume. -/
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

/-- The projection. -/
def ProtocolStateRaw.view (r : ProtocolStateRaw) : ProtocolState :=
  { previousStateHash := r.previousStateHash, genesisStateHash := r.genesisStateHash,
    consensus := r.consensus.toSelection, constants := r.constants }

/-- **`protocolState`** — the parse, projected to the fork-choice view. -/
def protocolState : P ProtocolState := do
  let r ← protocolStateRaw
  pure r.view

/-! ## §5 — The entry points, and what they REFUSE. -/

/-- **`decodeProtocolState`** — decode a `Protocol_state.Value.Stable.V2` from a byte prefix,
returning it and the UNCONSUMED remainder.

Deliberately a PREFIX decode: on the peer-to-peer wire the protocol state is followed by the Wrap
proof and then the whole block body, and this file's job ends at the consensus state. The remainder
is returned rather than ignored so a caller can say how many bytes were accounted for. -/
def decodeProtocolState (bs : List Nat) : Option (ProtocolState × List Nat) := protocolState bs

/-- **`decodeProtocolStateRaw`** — the same decode, undiscarded. -/
def decodeProtocolStateRaw (bs : List Nat) : Option (ProtocolStateRaw × List Nat) :=
  protocolStateRaw bs

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
def decodeProtocolStateRawChecked (C : Constants) (bs : List Nat) :
    Option (ProtocolStateRaw × List Nat) :=
  match decodeProtocolStateRaw bs with
  | none => none
  | some (ps, rest) =>
      if ps.constants.agreesWith C
        && ps.consensus.subWindowDensities.all (· ≤ C.slotsPerSubWindow)
        && ps.consensus.minWindowDensity ≤ C.slotsPerWindow
        && ps.consensus.slotsPerEpoch == C.slotsPerEpoch
      then some (ps, rest) else none

/-- **`decodeProtocolStateChecked`** — the checked decode, projected to the fork-choice view. -/
def decodeProtocolStateChecked (C : Constants) (bs : List Nat) :
    Option (ProtocolState × List Nat) :=
  match decodeProtocolStateRawChecked C bs with
  | none => none
  | some (ps, rest) => some (ps.view, rest)

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

theorem consensus_decodes_a_wellformed_state : wellformedDecodeCheck = true := by decide

/-- ⚑ **TEN DENSITIES IS A REFUSAL**, not a shorter window. This is what the public GraphQL surface
can supply (nothing) and what a mis-ordered decode produces. -/
theorem ten_densities_is_refused :
    consensusState (sampleConsensusBytes (d11.take 10) 32 7140) = none := by decide

/-- A VRF output that is not 32 bytes is a REFUSAL — the digest's pre-image length is part of the
comparison's meaning, not a detail. -/
theorem a_short_vrf_output_is_refused :
    consensusState (sampleConsensusBytes d11 31 7140) = none := by decide

/-- ⚑ **`slots_per_epoch = 0` IS A REFUSAL.** Lean's `Nat` division by zero is `0`, so admitting it
would silently place every state in epoch 0 and make every pair look same-epoch — the short-range
branch would then decide every fork. -/
theorem zero_slots_per_epoch_is_refused :
    consensusState (sampleConsensusBytes d11 32 0) = none := by decide

/-- ⚑ **A NON-CANONICAL INTEGER WIDTH IS A REFUSAL.** `blockchain_length` written in the 16-bit form
when it fits in one byte is rejected rather than read as the same number. -/
theorem a_widened_length_is_refused :
    consensusState ([0xfe, 0x03, 0x00] ++ (sampleConsensusBytes d11 32 7140).drop 3) = none := by
  decide

/-- ⚑ **A NON-CANONICAL FIELD ELEMENT IS A REFUSAL.** `p` itself, little-endian, in the staking
epoch data's `ledger.hash` slot: `x` and `x + p` are one element at the digest and must not have two
encodings. -/
theorem a_non_canonical_field_element_is_refused :
    epochData (eFp pallasBaseModulus ++ eInt 9 ++ eFp 2 ++ eFp 3 ++ eFp 4 ++ eInt 11) = none := by
  decide

/-- The VRF digest really is the Blake2b of the wire bytes, not the wire bytes. -/
def vrfDigestCheck : Bool :=
  match consensusState (sampleConsensusBytes d11 32 7140) with
  | some (c, _) => c.lastVrfHash == blake2b256 (List.replicate 32 7)
                     && c.lastVrfHash != List.replicate 32 7
  | none => false

theorem the_vrf_digest_is_derived : vrfDigestCheck = true := by decide

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

theorem a_decoded_state_drives_select : selectDrivenByDecodeCheck = true := by decide

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

/-! ## §7 — axiom hygiene. ⚑ **EVERYTHING BELOW IS KERNEL.**

This section used to read: *"the decode theorems use `native_decide` … the parser uses well-founded
recursion over a byte list that the kernel will not reduce at these sizes."*

**That was never measured, and it is false.** Measured 2026-07-30 with `lake env lean`, on the
laptop, ~1.2 s of each figure being process start plus olean load:

| kernel `decide` on | wall |
|---|---|
| all six of §6's decode/refusal vectors | 18.5 s |
| the two canonicality refusals | 9.8 s |
| (for scale) the REAL 1,544-byte devnet block's full parse | 4.3 s |

So the parser reduces in the kernel fine, at synthetic *and* at real-block sizes, and every theorem
in §6 is now `decide`. The reason this mattered is not the eight theorems: it is that a **stated
reason for reaching past the kernel had never been checked**, and a sibling module copied both the
tactic and this paragraph on its authority.

⚑ Where `native_decide` IS still required — measured, in `Bridge.MinaBinprotRealBlock` — is the
`String` C-ABI wire: `String.decEq` and `String.mk` do not reduce, and the kernel reports getting
*stuck*, not slow. That is a structural wall and it is a different claim from this one. -/

#assert_axioms consensus_decodes_a_wellformed_state
#assert_axioms ten_densities_is_refused
#assert_axioms a_short_vrf_output_is_refused
#assert_axioms zero_slots_per_epoch_is_refused
#assert_axioms a_widened_length_is_refused
#assert_axioms a_non_canonical_field_element_is_refused
#assert_axioms the_vrf_digest_is_derived
#assert_axioms a_decoded_state_drives_select
#assert_axioms carried_constants_that_disagree_are_refused
#assert_axioms the_pin_is_the_daemons_grace_period

end Dregg2.Bridge.MinaBinprot
