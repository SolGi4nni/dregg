/-
# Dregg2.Circuit.Emit.LightClientTendermintAir — the Cosmos/Tendermint light-client VERIFY-DECISION,
EMITTED AS AN AIR (the SECOND target-chain lightclient STARK-ified, mirroring `LightClientEthAir`).

## What this file IS (the "STARK-ify the Cosmos lightclient" slice)

`Dregg2.Bridge.LightClientTendermint` proves `tmNoForgery` over `tmVerify` — the STAKE-WEIGHTED
Tendermint header-acceptance rules — and `Dregg2.Bridge.LightClientTendermintGate` collapses that
decision to the eleven scalar/boolean projections a deployed node computes (`tmVerifyDecision`) and
`@[export]`s it as `dregg_tm_lc_verify`. That gives a node a Lean-PROVEN accept/reject — but the
verdict is rendered by *running Lean code on the node's own machine*. A peer (or an on-chain
contract) that wants to trust "this dregg node saw Cosmos chain C finalize app-state A" must
RE-TRUST that node's execution. There is no portable object.

This file emits `tmVerifyDecision` AS A DESCRIPTOR-IR-v2 AIR (`tmLcVerifyDesc`), so a dregg node can
PROVE the verify-decision as a STARK: the proof is a portable artifact any peer verifies without
re-running the node, and (via the gnark FRI-wrap → Groth16, the on-chain hook below) an on-chain
contract verifies. That is what makes dregg + a Cosmos chain TRUE PEERS: this AIR turns dregg's view
of the Cosmos chain into the SAME kind of portable proof the ETH lane produces (`ethLcVerifyDesc`).

## The on-chain wrap hook (the named residual — identical to the ETH lane's, none wired in THIS slice)

The portable STARK over `tmLcVerifyDesc` feeds the SAME settlement path the ETH light-client AIR
does: the FRI proof is wrapped to Groth16 by the gnark `SettlementCircuit` (`chain/gnark/
settlement_circuit.go`), the Tendermint public statement (the three PIs: trusted next-vals root /
committed app-hash / chain-id domain) is added to the exposed settlement lanes, and the on-chain
`DreggPeerRegistry` (`chain/contracts/DreggPeerRegistry.sol`) verifies the wrapped proof — the
Cosmos peer becoming an on-chain-verifiable TRUE PEER exactly as Base did. Like the ETH lane's
landing (commit `3884100013`, which added ONLY its Lean file), NONE of that wiring is in THIS slice:
the descriptor is not in the `EmitByName` aggregator, the carriers are asserted-not-in-circuit, and
the anchor PIs are published-not-bound. This file lands the Lean-authored, axiom-clean AIR + its
refinement; the Rust/gnark/Sol wrap is the named follow-up.

HOUSE LAW #1: the AIR is LEAN-AUTHORED. Rust only ingests the emitted `emitVmJson2` descriptor and
runs the generic multi-table prover over it; it never hand-writes these constraints. The refinement
`tmLcAir_sound` / `tmLcAir_no_forgery` is a machine-checked theorem over the EMITTED object
(`airAccepts` reads the descriptor's own gate bodies), tying acceptance to `tmVerifyDecision` and
hence (via `tmVerifyDecision_no_forgery` → `tmNoForgery`) to Tendermint foreign-validity — so a
STARK that satisfies this AIR CARRIES the no-forgery guarantee, modulo the named crypto carriers.

## The crypto boundary: IN-AIR logic vs NAMED verified carriers (the pragmatic first cut)

Tendermint verify is not pure logic — it invokes per-validator Ed25519 commit-signature checks and
SHA-256 validator-set hashing. This AIR draws the boundary EXACTLY where `LightClientTendermintGate`
already draws it (the carrier model): the pure `Nat`/`Bool` STAKE-WEIGHTED VERIFY-LOGIC goes IN-AIR
as arithmetic gates; the heavy crypto results ride as WITNESSED CARRIERS the logic constrains.

  * IN-AIR (arithmetic gates over the trace):
      - the chain-id match (`CHAIN_ID − TS_CHAIN_ID = 0`) and the adjacent-height advance
        (`HEIGHT − TS_HEIGHT − 1 = 0`),
      - the 3-check TIME WINDOW as three range-checked non-negative slacks: monotonic advance
        (`TW_MONO = TIME − HEADER_TIME − 1 ≥ 0`, strict), not-from-the-future under clock drift
        (`TW_DRIFT = NOW + CLOCK_DRIFT − TIME ≥ 0`), trusted header still inside the trusting period
        (`TW_TRUST = HEADER_TIME + TRUSTING_PERIOD − NOW − 1 ≥ 0`, strict),
      - the load-bearing consensus arithmetic — the STRICT `> 2/3` stake threshold in multiply form
        `2·totalPow < 3·signedPow` — as the range-checked non-negative slack
        `TDIFF = 3·signedPow − 2·totalPow − 1 ≥ 0` (the exactly-2/3 boundary gives `TDIFF = −1`,
        UNSAT — Tendermint's strict threshold, in-circuit).
  * NAMED verified CARRIERS (witnessed columns, forced `= 1` for accept — the SAME opaque results
    `tmVerifyDecision` composes over):
      - `EPOCH_OK` — the SHA-256 next-validators epoch binding (`decide (hash(enc valset) =
        ts.nextValidatorsHash)`): the untrusted set is EXACTLY the set the trusted header committed
        to (the adjacent-advance / next_validators overlap rule). CONSUMED by the decision.
      - `VSET_OK` — the SHA-256 header self-binding (`decide (hash(enc valset) =
        header.validatorsHash)`): the quorum is over the set the header names. CONSUMED by the
        decision.
      - `ED_OK` — the Ed25519 batch-verify result. In the Tendermint decision the Ed25519 outcome
        is folded into `SIGNED_POW` (the summed VERIFIED stake, `signedPower`), so `ED_OK` names
        that provenance in the trace — forced `= 1`, attesting `SIGNED_POW` is the genuine
        Ed25519-verified stake sum. NOT read by the scalar decision (which trusts `SIGNED_POW` as a
        `Nat`); the load-bearing Ed25519 soundness is consumed inside `tmNoForgery` via `sigSound`.

The residual is HONEST and NAMED: in THIS slice the carriers are asserted, not re-derived in-circuit,
so the STARK proves the STAKE-WEIGHTED / TIME / BINDING LOGIC is correct GIVEN the crypto results —
precisely the guarantee `tmVerifyDecision` gives, now portable. Putting Ed25519/SHA in-AIR (or as
their own verified sub-proofs the AIR `ProofBind`s against) is the next iteration; the public-input
anchors below are the hook it attaches to.

## Public inputs (the addressing layer — what the proof is ABOUT)

`PI[0]    = TRUSTED_NEXT_VALS_ROOT`  — the TRUSTED `next_validators_hash` (the WS-checkpoint anchor
                                    the EPOCH_OK carrier is a verify against). The trust root the
                                    proof is relative to.
`PI[1..9] = COMMITTED_APP_HASH[0..8]`— the claimed committed app_hash / state root A: the FULL 256-bit
                                    application-state root (what ICS-23 membership later opens
                                    against) exposed as its NINE radix-`2^31`, MOST-SIGNIFICANT-limb-
                                    first limbs (`⌈256/31⌉ = 9`; the top limb carries the residual 8
                                    bits). FELT-WIDTH CLOSE: the earlier single anchor felt bound only
                                    a 31-bit PROJECTION of the app-hash, so two 256-bit roots agreeing
                                    in 31 bits both verified — a soundness gap at the peer-wrap
                                    boundary. Nine PI-bound limbs bind the WHOLE root; the peer-wrap's
                                    radix-`2^31` MSB-first pack over `PI[1..9]` recomposes it before
                                    its 128-bit split.
`PI[10]   = CHAIN_ID_DOMAIN`         — the chain-id + epoch/height domain the proof speaks for.

These ride as published witness columns pinned to the public inputs (`.piBinding`), so a verifier
sees WHICH trust root and WHICH (full 256-bit) app-hash the proof is about. NOT-YET-CLOSED (named
residual, UNCHANGED by this widening): in this carrier slice the anchors are published but not yet
arithmetically bound to the carrier bits (that binding IS the in-AIR-crypto iteration — `EPOCH_OK`
derived from `TRUSTED_NEXT_VALS_ROOT`, the app hash opened against `COMMITTED_APP_HASH`). So
`airAccepts` (the LOGIC refinement) is stated over the eleven projections; the anchor pins are the
addressing layer around it — this change widens the APP-HASH anchor from 31 bits to the full 256,
orthogonal to (and leaving untouched) the logic refinement.

## Witness (the update)

The hidden trace columns are the update's projections: the nine time/chain/height scalars, the two
power sums `TOTAL_POW`/`SIGNED_POW`, the four range slacks (`TDIFF` + the three time-window slacks),
and the three carrier bits `ED_OK`/`VSET_OK`/`EPOCH_OK`. An honest prover fills the slacks with the
true differences and the carrier bits with the true Ed25519/SHA-256 results; a forger who sets a
carrier it cannot justify, or claims a `SIGNED_POW` above the true verified stake, is refused by the
SAME no-forgery theorem the gate carries (the carriers are the `CryptoLeaf` fields under `hcr`).

## Constraint map

| statement                                   | decision conjunct                          | IR-v2 constraint                              |
|---------------------------------------------|--------------------------------------------|-----------------------------------------------|
| chain-id match                              | `decide (chainId = tsChainId)`             | `.gate (CHAIN_ID − TS_CHAIN_ID)`              |
| adjacent-height advance                     | `decide (height = tsHeight + 1)`           | `.gate (HEIGHT − TS_HEIGHT − 1)`              |
| strict >2/3, LIMBED (see below)             | `decide (2·totalPow < 3·signedPow)`        | 5 GENERATED chain gates + 17 per-limb lookups |
| monotonic-advance slack definition          | (bridges `headerTime < time`)              | `.gate (TW_MONO − TIME + HEADER_TIME + 1)`    |
| monotonic advance (slack non-negative)      | `decide (headerTime < time)`               | `.lookup ⟨range, [TW_MONO]⟩`                  |
| drift-bound slack definition                | (bridges `time ≤ now + clockDrift`)        | `.gate (TW_DRIFT − NOW − CLOCK_DRIFT + TIME)` |
| not-from-the-future (slack non-negative)    | `decide (time ≤ now + clockDrift)`         | `.lookup ⟨range, [TW_DRIFT]⟩`                 |
| trusting-period slack definition            | (bridges `now < headerTime+trustingPeriod`)| `.gate (TW_TRUST − HEADER_TIME − TP + NOW+1)` |
| still in trusting period (slack non-neg)    | `decide (now < headerTime + trustingP)`    | `.lookup ⟨range, [TW_TRUST]⟩`                 |
| Ed25519 batch verify (carrier)             | (folded into `signedPow`)                  | `.gate (ED_OK − 1)`                           |
| header self-binds valset (carrier)         | `selfBindOk`                               | `.gate (VSET_OK − 1)`                         |
| next-validators epoch binding (carrier)    | `epochBindOk`                              | `.gate (EPOCH_OK − 1)`                        |
| trusted next-vals root is public           | (addressing)                               | `.piBinding first TRUSTED_NEXT_VALS_ROOT 0`   |
| committed app-hash (full 256b) is public   | (addressing; nine limbs)                   | `.piBinding first (COMMITTED_APP_HASH i) (1+i)`, `i<9` |
| chain-id / epoch domain is public          | (addressing)                               | `.piBinding first CHAIN_ID_DOMAIN 10`         |

The three TIME lookups are `∈ [0, 2^TM_BITS)` teeth: each slack is non-negative iff its inequality
holds with no field-wrap escape. **The threshold is no longer one of them** — see below.

## ⚑ TWO REPAIRS, 2026-08-03, AND THE SECOND ONE IS THE CAPABILITY

### (1) THE WIDTH REPAIR — `TM_BITS` was 64, and 64 BITS OVER BABYBEAR IS VACUOUS

This descriptor shipped `bits: 64` on its range table. `p = 2013265921 < 2^31 < 2^64`, so **every
field element was already in the declared interval** and all four lookups refused NOTHING
(`RangeFieldContainment.range_vacuous_at_or_above_31`, over all widths `≥ 31` and all field
elements). Concretely, at the exact boundary this AIR exists to enforce — the strict `>2/3` threshold
at EXACTLY 2/3 — the slack filled to `−1`, which on the wire is `p − 1 = 2013265920 < 2^64`. **A
Tendermint sub-quorum passed as a supermajority.** `TM_BITS` became **29**, the MAXIMUM wrap-free
width (`Wrapfree b ↔ 2^(b+1) ≤ p`, true at 29 and FALSE at 30). The three TIME teeth still ride that
repair, and both directions are theorems here (`tm_range_is_inside_the_field`,
`tm_wrapped_slack_is_outside_the_range`).

### ⚑ (2) THE TALLY REPAIR — what the vacuous width was HIDING

The 29-bit narrowing was correct and it bought a client that **cannot hold a real validator set.**
Completeness needed `3·signedPow < 2^29`, i.e. voting power below ~1.8e8. CometBFT allows
`MaxTotalVotingPower = int64(math.MaxInt64) / 8 = 2^60 − 1 = 1152921504606846975`
(`cometbft/types/validator_set.go:27`). Cosmos Hub carries 328,774,071 live (measured 2026-08-03 at
height 32,325,597, 180 validators) — **already past 2^29 once tripled.**

And no range width was ever going to fix it: `TOTAL_POW` was ONE COLUMN, a column is one BabyBear
felt, and a felt holds 30.9 bits. `MaxTotalVotingPower` is 572 MILLION field moduli. The 64-bit
declaration did not make it fit; it made the shortfall INVISIBLE.

**The tally is now a LIMB VECTOR** — four 16-bit limbs each for `TOTAL_POW` and `SIGNED_POW`, exactly
a `u64`, exactly CometBFT's own wire type — with the strict-`>2/3` comparison decided by an OFFSET
CARRY CHAIN whose five-limb difference vector is itself range-checked
(`Dregg2.Circuit.LimbTally`). The AIR is GENERATED by `LimbTally.chainBodies`, not transcribed.

⚑ **AND THE TOOTH GOT STRONGER, NOT WEAKER.** The old refusal of the exactly-2/3 sub-quorum rested on
`p − 1 ∉ [0, 2^29)` — a fact about the FIELD SIZE, false at 30 and catastrophically false at the 64
that shipped, and the whole reason a 404-width census had to happen. The limbed refusal rests on
"a limb vector of non-negative limbs denotes a non-negative value, and the difference is `−1`", which
holds at every width in every field (`tm_threshold_refusal_is_field_independent`). §7 exhibits both
poles ONE UNIT APART at the protocol maximum: `signedPow = 768614336404564651` of
`1152921504606846975` ACCEPTS, and `768614336404564650` — exactly 2/3 — has no satisfying assignment.

⚠ **WHAT IS STILL NARROW, said out loud.** The three TIME slacks are still single felts at 29 bits.
At second resolution that is four orders of headroom (a 14-day trusting period is 1.21e6; the modal
live `max_clock_drift` across 401 Cosmos Hub IBC clients is 40s). ⚠ **At CometBFT's NATIVE nanosecond
resolution they do not fit** — header time is `google.protobuf.Timestamp`
(`proto/tendermint/types/types.proto:52`), where 14 days is 1.2096e15 (50.1 bits) — so the caller
must supply SECONDS. That is a real narrowing of the honest domain, it is visible in
`tmLcAir_complete`'s remaining `< 2^TM_BITS` hypotheses, and **the same limb machinery closes it**
(the time window is `1·X − 1·Y − γ ≥ 0`, the identical shape at `α = β = 1`). NOT DONE, named.

## The mod-p ↔ ℤ reading (the shared field-soundness residual)

`airAccepts` reads the emitted gate bodies as ℤ equalities and the range lookups as ℤ intervals (the
strong reading, exactly as `LightClientEthAir.airAccepts` does). The deployed denotation is mod-`p`
(`VmConstraint.holdsVm`) and the range is realized by nibble-limb decomposition, not a literal table;
bridging the two needs full-wire range decomposition, the same field-soundness residual every Emit
descriptor carries. That residual is UNCHANGED for the chain-id, height, time and carrier gates.

⚑ **It is DISCHARGED for the five tally-chain gates.** Those are the ones that could actually alias —
each multiplies a carry by `2^16` — so `LimbTally.rung_value_bounds` bounds their ℤ image on any
assignment respecting the DECLARED ranges, and `rung_no_alias_at_deployed_constants` measures that
interval against `p`: reachably `[−8519806, 8585339]`, **236× inside**. A tally gate that is `0 mod p`
on a range-respecting row IS `0` over `ℤ`, so the recomposition identity transfers to the deployed
denotation rather than being asserted over it. `rung_alias_reachable_at_24_bits` is the refutation
three bits up.

## Axiom hygiene

Definitional descriptor + non-vacuous per-gate `iff` lemmas (`omega`) + the load-bearing
`tmLcAir_sound` / `tmLcAir_no_forgery` refinement to `tmVerifyDecision` / `TmForeignValid`.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.RangeFieldContainment
import Dregg2.Circuit.LimbTally
import Dregg2.Bridge.LightClientTendermintGate

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Dregg2.Circuit.Emit.LightClientTendermintAir

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Bridge.VerifiedLightClient
open Dregg2.Bridge.LightClientTendermint
open Dregg2.Bridge.LightClientTendermintGate

/-! ## §1 — the trace column layout (one logical row).

Columns 0..17 are the eleven VERIFY-LOGIC projections `tmVerifyDecision` composes over (three of
them crypto carriers), plus the four range slacks. Columns 18..28 are the published PUBLIC anchors:
`TRUSTED_NEXT_VALS_ROOT` (18), the NINE app-hash limbs `COMMITTED_APP_HASH 0..8` (cols 19..27 — the
full 256-bit app-hash, radix-`2^31`, MSB-first), and `CHAIN_ID_DOMAIN` (28). -/

/-- Untrusted header chain-id. Witness. -/
def CHAIN_ID : Nat := 0
/-- Trusted chain-id (`ts.chainId`). Witness. -/
def TS_CHAIN_ID : Nat := 1
/-- Untrusted header height. Witness. -/
def HEIGHT : Nat := 2
/-- Trusted height (`ts.height`). Witness. -/
def TS_HEIGHT : Nat := 3
/-- Trusted header time (`ts.headerTime`). Witness. -/
def HEADER_TIME : Nat := 4
/-- Untrusted header time (`u.header.time`). Witness. -/
def TIME : Nat := 5
/-- The verifier's clock (`ts.now`). Witness. -/
def NOW : Nat := 6
/-- The clock-drift allowance (`ts.clockDrift`). Witness. -/
def CLOCK_DRIFT : Nat := 7
/-- The trusting period (`ts.trustingPeriod`). Witness. -/
def TRUSTING_PERIOD : Nat := 8
/-- Monotonic-advance slack `TIME − HEADER_TIME − 1`; range-forced `≥ 0`, i.e. `headerTime < time`. -/
def TW_MONO : Nat := 9
/-- Not-from-the-future slack `NOW + CLOCK_DRIFT − TIME`; range-forced `≥ 0`, i.e.
`time ≤ now + clockDrift`. -/
def TW_DRIFT : Nat := 10
/-- Trusting-period slack `HEADER_TIME + TRUSTING_PERIOD − NOW − 1`; range-forced `≥ 0`, i.e.
`now < headerTime + trustingPeriod`. -/
def TW_TRUST : Nat := 11
/-- **CARRIER** — the Ed25519 batch-verify RESULT (attests the signed power is the genuine verified
stake); forced `= 1`. NAMED verified-FFI carrier, not re-derived in-AIR (this slice). Witness. -/
def ED_OK : Nat := 12
/-- **CARRIER** — the SHA-256 header self-binding compare RESULT (`hash(enc valset) =
header.validatorsHash`); forced `= 1`. NAMED carrier. Witness. -/
def VSET_OK : Nat := 13
/-- **CARRIER** — the SHA-256 next-validators epoch-binding compare RESULT (`hash(enc valset) =
ts.nextValidatorsHash`); forced `= 1`. NAMED carrier. Witness. -/
def EPOCH_OK : Nat := 14

/-! ### ⚑ THE TALLY, AS A LIMB VECTOR — the capability this AIR did not have.

`TOTAL_POW` and `SIGNED_POW` used to be ONE COLUMN EACH. A column is one BabyBear felt and a felt
holds 30.9 bits, so the deployed client could not represent a Cosmos Hub validator set at all —
never mind CometBFT's `MaxTotalVotingPower = int64(math.MaxInt64)/8 = 2^60 − 1`
(`cometbft/types/validator_set.go:27`). The 64-bit range declaration did not make that fit; it made
the shortfall invisible, and the 29-bit repair that closed the vacuity made it VISIBLE and no
smaller.

They are now **four 16-bit limbs each, LEAST-significant first — exactly a `u64`**, which is exactly
CometBFT's own wire type for voting power. The arithmetic and its soundness live in
`Dregg2.Circuit.LimbTally`. -/

/-- The tally limb width. `TALLY_LIMBS · TM_LIMB_BITS = 64`. -/
def TM_LIMB_BITS : Nat := LimbTally.TALLY_LIMB_BITS
/-- The number of tally limbs — four 16-bit limbs are a `u64`. -/
def TM_TALLY_LIMBS : Nat := LimbTally.TALLY_LIMBS
/-- The carry width for the difference chain (the prover's own byte bus). -/
def TM_CARRY_BITS : Nat := LimbTally.TALLY_CARRY_BITS

/-- **Limb `i` of the total voting power** (`totalPower`), LSB-first. Columns 15..18. Witness. -/
def TOTAL_POW_LIMB (i : Nat) : Nat := 15 + i
/-- **Limb `i` of the Ed25519-VERIFIED signed power** (`signedPower`), LSB-first. Columns 19..22.
Its Ed25519 provenance is the `ED_OK` carrier. Witness. -/
def SIGNED_POW_LIMB (i : Nat) : Nat := 19 + i
/-- **Limb `i` of the strict `>2/3` threshold DIFFERENCE `3·signedPow − 2·totalPow − 1`**, LSB-first.
FIVE limbs (columns 23..27), one more than the operands: `3·A` needs two bits beyond `A`. Every limb
carries its own 16-bit range lookup, and THAT is the threshold tooth — a limb vector of non-negative
limbs denotes a non-negative value, so a sub-quorum (whose difference is negative) has no
representation at all. -/
def TDIFF_LIMB (i : Nat) : Nat := 23 + i
/-- **Offset carry `i` of the difference chain** (columns 28..31); denotes `col − 128`, since a
difference chain BORROWS and a field wire has no sign. Range-checked at 8 bits for the mod-`p`
bridge ONLY — `LimbTally.chain_recomposes` needs no bound on it whatsoever. -/
def TDIFF_CARRY (i : Nat) : Nat := 28 + i

/-- **PUBLIC ANCHOR** — the TRUSTED `next_validators_hash` (the WS-checkpoint trust anchor). PI-bound. -/
def TRUSTED_NEXT_VALS_ROOT : Nat := 32

/-- The number of ~31-bit limbs the FULL 256-bit committed app-hash is exposed as: `⌈256 / 31⌉ = 9`.
Eight 31-bit limbs cover 248 bits; the ninth (most-significant) limb carries the remaining 8 bits.
This is the felt-width close — a SINGLE anchor felt bound only a 31-bit PROJECTION of the 256-bit
app-hash (two roots agreeing in 31 bits both verified); nine limbs bind the WHOLE root. -/
def COMMITTED_APP_HASH_LIMBS : Nat := 9

/-- **PUBLIC ANCHOR (limb `i`)** — the claimed committed app_hash / state root A as its radix-`2^31`,
MOST-SIGNIFICANT-limb-first decomposition. Limb `i` is trace column `19 + i` (cols 19..27); limb `0`
is the MSB (its top carries only 8 bits). PI-bound to slot `1 + i`, so the peer-wrap's radix-`2^31`
MSB-first pack over `PI[1..9]` recomposes the 256-bit app-hash exactly before its 128-bit split. -/
def COMMITTED_APP_HASH (i : Nat) : Nat := 33 + i

/-- **PUBLIC ANCHOR** — the chain-id + epoch/height domain. PI-bound. -/
def CHAIN_ID_DOMAIN : Nat := 33 + COMMITTED_APP_HASH_LIMBS

/-- Total main-trace width: 15 scalar/carrier logic columns + 4 total-power limbs + 4 signed-power
limbs + 5 difference limbs + 4 chain carries + 1 next-vals anchor + 9 app-hash limbs + 1 domain
anchor = 43.

⚑ It was 29. The +14 is the tally becoming REPRESENTABLE: two `u64` operands, their difference, and
the borrow chain that ties them. That is what a real validator set costs in columns, and it is the
honest price of the capability — the previous 29 bought a client that could not hold one. -/
def TM_LC_WIDTH : Nat := 43

/-- PI slot 0: the trusted next-validators root. -/
def PI_TRUSTED_NEXT_VALS_ROOT : Nat := 0
/-- PI slot of app-hash limb `i` (slots 1..9), MSB-first. -/
def PI_COMMITTED_APP_HASH (i : Nat) : Nat := 1 + i
/-- PI slot of the chain-id / epoch domain (slot 10). -/
def PI_CHAIN_ID_DOMAIN : Nat := 1 + COMMITTED_APP_HASH_LIMBS
/-- Number of public inputs: next-vals root + 9 app-hash limbs + chain-id domain. -/
def PI_COUNT : Nat := 11

/-- The range-slack width. ⚑ **29, AND THE CEILING IS THE FIELD, NOT THE WIRE.**

This was `64` — a u64-timestamp-shaped number that describes the WIRE and says nothing about the
domain the constraint is evaluated in. Over BabyBear (`p = 2013265921 < 2^31`) a 64-bit interval
contains the whole field, so all four lookups were satisfied by every assignment
(`RangeFieldContainment.range_vacuous_at_or_above_31`). 29 is the largest width for which a wrapped
negative slack lands OUTSIDE the interval (`wrap_free_iff_le_29`); 30 already fails. See the module
header for what the narrowing costs and what it exposes about `EffectAirIR`. -/
def TM_BITS : Nat := 29

/-! ## §2 — the emitted gate bodies (the descriptor's OWN constraint polynomials). -/

/-- `CHAIN_ID − TS_CHAIN_ID` — zero iff the header's chain-id matches the trusted chain-id. -/
def chainMatchBody : EmittedExpr :=
  .add (.var CHAIN_ID) (.mul (.const (-1)) (.var TS_CHAIN_ID))
/-- `HEIGHT − TS_HEIGHT − 1` — zero iff the header is the adjacent next height. -/
def heightAdjBody : EmittedExpr :=
  .add (.add (.var HEIGHT) (.mul (.const (-1)) (.var TS_HEIGHT))) (.const (-1))
/-! ### ⚑ The strict `>2/3` threshold, GENERATED rather than transcribed.

`LightClientMinaAir` set the bar — `EffectLower.lowerAir`-authored, no hand-written `VmConstraint2`.
The threshold used to be ONE hand-written gate body (`TDIFF − 3·SIGNED_POW + 2·TOTAL_POW + 1`) plus
ONE lookup, because a single-felt slack is one gate. A limbed comparison is five gates and thirteen
lookups, and hand-writing those would be exactly the drift this repo's House Law #1 exists to stop.

`LimbTally.chainBodies` GENERATES them from the rung list, and `LimbTally.chainBodies_zero_iff` ties
what it generates back to `ChainOk` — so §5's soundness is about the bodies that ship. -/

/-- **The four rungs of the threshold difference chain**, LSB-first: at radix position `i` the
signed-power limb, the total-power limb, the difference limb and the offset carry out.

Written as an explicit literal (rather than `List.range`-mapped) so the byte-golden `#guard` reduces
to the exact wire string with no fold — the same discipline `appHashPins` follows. -/
def tdiffRungs : List LimbTally.Rung :=
  [ ⟨SIGNED_POW_LIMB 0, TOTAL_POW_LIMB 0, TDIFF_LIMB 0, TDIFF_CARRY 0⟩
  , ⟨SIGNED_POW_LIMB 1, TOTAL_POW_LIMB 1, TDIFF_LIMB 1, TDIFF_CARRY 1⟩
  , ⟨SIGNED_POW_LIMB 2, TOTAL_POW_LIMB 2, TDIFF_LIMB 2, TDIFF_CARRY 2⟩
  , ⟨SIGNED_POW_LIMB 3, TOTAL_POW_LIMB 3, TDIFF_LIMB 3, TDIFF_CARRY 3⟩ ]

/-- The difference vector's TOP limb — the chain's closure column. -/
def TDIFF_TOP : Nat := TDIFF_LIMB 4

/-- The emitted threshold gate bodies: `α = 3` on signed power, `β = 2` on total power, `γ = 1` for
the STRICT inequality. Five bodies from four rungs (one per rung plus the closure gate). -/
def tdiffChainBodies : List EmittedExpr :=
  LimbTally.chainBodies TM_LIMB_BITS 3 2 1 LimbTally.TALLY_CARRY_OFF TDIFF_TOP tdiffRungs

/-- `TW_MONO − TIME + HEADER_TIME + 1` — zero iff `TW_MONO = TIME − HEADER_TIME − 1`. -/
def twMonoBody : EmittedExpr :=
  .add (.add (.add (.var TW_MONO) (.mul (.const (-1)) (.var TIME))) (.var HEADER_TIME)) (.const 1)
/-- `TW_DRIFT − NOW − CLOCK_DRIFT + TIME` — zero iff `TW_DRIFT = NOW + CLOCK_DRIFT − TIME`. -/
def twDriftBody : EmittedExpr :=
  .add (.add (.add (.var TW_DRIFT) (.mul (.const (-1)) (.var NOW)))
    (.mul (.const (-1)) (.var CLOCK_DRIFT))) (.var TIME)
/-- `TW_TRUST − HEADER_TIME − TRUSTING_PERIOD + NOW + 1` — zero iff
`TW_TRUST = HEADER_TIME + TRUSTING_PERIOD − NOW − 1`. -/
def twTrustBody : EmittedExpr :=
  .add (.add (.add (.add (.var TW_TRUST) (.mul (.const (-1)) (.var HEADER_TIME)))
    (.mul (.const (-1)) (.var TRUSTING_PERIOD))) (.var NOW)) (.const 1)
/-- `ED_OK − 1` — zero iff the Ed25519 carrier bit is set. -/
def edBody : EmittedExpr := .add (.var ED_OK) (.const (-1))
/-- `VSET_OK − 1` — zero iff the self-binding carrier bit is set. -/
def vsetBody : EmittedExpr := .add (.var VSET_OK) (.const (-1))
/-- `EPOCH_OK − 1` — zero iff the epoch-binding carrier bit is set. -/
def epochBody : EmittedExpr := .add (.var EPOCH_OK) (.const (-1))

/-! ## §3 — the constraint list + descriptor. -/

def chainMatchGate : VmConstraint2 := .base (.gate chainMatchBody)
def heightAdjGate : VmConstraint2 := .base (.gate heightAdjBody)

/-! ### The two ADDITIONAL range tables, and why a second width is not a complication.

The three time-window slacks stay on the shared `.range` table at 29 bits — the maximum wrap-free
width, and four orders above any second-resolution deployment. The tally rides at 16 and its carries
at 8, on WIDTH-TAGGED CUSTOM tables (`rangeTidW b = .custom (RANGE_W_TID_BASE + b)`, `RANGE_W_TID_BASE
= 64`), which is the mechanism the deployed availability-weld already uses for its 15-bit borrow
limbs. The Rust side resolves each lookup's width from the DECLARED table
(`descriptor_ir2.rs` `range_bits_for`), realizes every width as the same byte-limb decomposition, and
shares ONE byte table across all of them — so three widths are three relations and one instance. -/

/-- The tally-limb range table: wire id `5 + 64 + 16 = 85`. -/
def TID_TALLY_LIMB : TableId := .custom (64 + TM_LIMB_BITS)
/-- The chain-carry range table: wire id `5 + 64 + 8 = 77`. -/
def TID_TALLY_CARRY : TableId := .custom (64 + TM_CARRY_BITS)

/-! ### ⚑ The four LIMBED QUANTITIES, as `EffectAirIR` legs — and the teeth are the COMPILER's output.

`EffectAirIR` gained a `LimbsLeg` today for exactly this: a `RangeLeg` is `⟨wire, bits⟩` — ONE column,
ONE width, one felt's worth of magnitude — and a tally is a LIST. Declaring the four quantities as
legs and letting `EffectLower.lowerLimbsLeg` emit their lookups means there is ONE path from source
to constraints, not a source language plus a hand-written transcription that agree today.

⚑ And it makes the IR's width verdict LOAD-BEARING on this deployed descriptor:
`LimbsLeg.mainRailOk` refuses an empty limb vector (which would denote `0` and check nothing) and any
limb width above the wrap-free ceiling 29 — the class `RangeFieldContainment` found three shipped
light clients sitting in. `tm_tally_legs_are_expressible` is that verdict, `decide`d. -/

/-- The total voting power as a limbed quantity: four 16-bit limbs, LSB-first. -/
def totalPowLeg : EffectAirIR.LimbsLeg :=
  { cols := [TOTAL_POW_LIMB 0, TOTAL_POW_LIMB 1, TOTAL_POW_LIMB 2, TOTAL_POW_LIMB 3]
  , bits := TM_LIMB_BITS, table := TID_TALLY_LIMB }

/-- The Ed25519-verified signed power as a limbed quantity. -/
def signedPowLeg : EffectAirIR.LimbsLeg :=
  { cols := [SIGNED_POW_LIMB 0, SIGNED_POW_LIMB 1, SIGNED_POW_LIMB 2, SIGNED_POW_LIMB 3]
  , bits := TM_LIMB_BITS, table := TID_TALLY_LIMB }

/-- ⚑ The THRESHOLD DIFFERENCE as a limbed quantity — FIVE limbs, and the load-bearing one. Its
containment is what forces `3·signedPow − 2·totalPow − 1 ≥ 0`, because a limb vector of non-negative
limbs denotes a non-negative value (`LimbTally.limbValue_nonneg`). -/
def tdiffLeg : EffectAirIR.LimbsLeg :=
  { cols := [TDIFF_LIMB 0, TDIFF_LIMB 1, TDIFF_LIMB 2, TDIFF_LIMB 3, TDIFF_LIMB 4]
  , bits := TM_LIMB_BITS, table := TID_TALLY_LIMB }

/-- The chain's offset carries, at the narrow width. ⚠ NOT part of the threshold argument —
`LimbTally.chain_recomposes` needs no carry bound at all. These exist solely for the mod-`p` ↔ `ℤ`
bridge (`LimbTally.rung_no_alias_at_deployed_constants`). Two different jobs, said apart. -/
def tdiffCarryLeg : EffectAirIR.LimbsLeg :=
  { cols := [TDIFF_CARRY 0, TDIFF_CARRY 1, TDIFF_CARRY 2, TDIFF_CARRY 3]
  , bits := TM_CARRY_BITS, table := TID_TALLY_CARRY }

/-- **THE THRESHOLD TEETH — one range lookup per limb, EMITTED BY THE COMPILER.**
Thirteen 16-bit lookups (four total-power, four signed-power, five difference) and four 8-bit carry
lookups, all of them `EffectLower.lowerLimbsLeg` output. -/
def tallyRangeLookups : List VmConstraint2 :=
  EffectLower.lowerLimbsLeg totalPowLeg ++ EffectLower.lowerLimbsLeg signedPowLeg
    ++ EffectLower.lowerLimbsLeg tdiffLeg ++ EffectLower.lowerLimbsLeg tdiffCarryLeg

/-- The generated threshold gates, wrapped into the target's constraint constructor. GENERATED —
there is no hand-written `VmConstraint2` in this block. -/
def tdiffChainGates : List VmConstraint2 :=
  tdiffChainBodies.map (fun b => .base (.gate b))

def twMonoGate : VmConstraint2 := .base (.gate twMonoBody)
/-- Monotonic advance range tooth: `TW_MONO ∈ [0, 2^TM_BITS)`. -/
def twMonoRange : VmConstraint2 := .lookup ⟨TableId.range, [.var TW_MONO]⟩
def twDriftGate : VmConstraint2 := .base (.gate twDriftBody)
/-- Not-from-the-future range tooth: `TW_DRIFT ∈ [0, 2^TM_BITS)`. -/
def twDriftRange : VmConstraint2 := .lookup ⟨TableId.range, [.var TW_DRIFT]⟩
def twTrustGate : VmConstraint2 := .base (.gate twTrustBody)
/-- Trusting-period range tooth: `TW_TRUST ∈ [0, 2^TM_BITS)`. -/
def twTrustRange : VmConstraint2 := .lookup ⟨TableId.range, [.var TW_TRUST]⟩
def edGate : VmConstraint2 := .base (.gate edBody)
def vsetGate : VmConstraint2 := .base (.gate vsetBody)
def epochGate : VmConstraint2 := .base (.gate epochBody)
/-- Published-anchor pin: the trusted next-validators root is `PI[0]`. -/
def nextValsRootPin : VmConstraint2 :=
  .base (.piBinding VmRow.first TRUSTED_NEXT_VALS_ROOT PI_TRUSTED_NEXT_VALS_ROOT)
/-- Published-anchor pins: the NINE committed-app-hash limbs are `PI[1..9]` (MSB-first). Each limb
rides its own PI slot, so the peer-wrap's radix-`2^31` pack over `PI[1..9]` recovers the FULL 256-bit
app-hash — not a 31-bit projection. Written as an explicit literal (limb `i` → col `19+i` → PI `1+i`)
so the byte-golden `#guard` reduces to the exact wire string with no fold. -/
def appHashPins : List VmConstraint2 :=
  [ .base (.piBinding VmRow.first (COMMITTED_APP_HASH 0) (PI_COMMITTED_APP_HASH 0))
  , .base (.piBinding VmRow.first (COMMITTED_APP_HASH 1) (PI_COMMITTED_APP_HASH 1))
  , .base (.piBinding VmRow.first (COMMITTED_APP_HASH 2) (PI_COMMITTED_APP_HASH 2))
  , .base (.piBinding VmRow.first (COMMITTED_APP_HASH 3) (PI_COMMITTED_APP_HASH 3))
  , .base (.piBinding VmRow.first (COMMITTED_APP_HASH 4) (PI_COMMITTED_APP_HASH 4))
  , .base (.piBinding VmRow.first (COMMITTED_APP_HASH 5) (PI_COMMITTED_APP_HASH 5))
  , .base (.piBinding VmRow.first (COMMITTED_APP_HASH 6) (PI_COMMITTED_APP_HASH 6))
  , .base (.piBinding VmRow.first (COMMITTED_APP_HASH 7) (PI_COMMITTED_APP_HASH 7))
  , .base (.piBinding VmRow.first (COMMITTED_APP_HASH 8) (PI_COMMITTED_APP_HASH 8)) ]
/-- Published-anchor pin: the chain-id / epoch domain is `PI[10]`. -/
def chainDomainPin : VmConstraint2 :=
  .base (.piBinding VmRow.first CHAIN_ID_DOMAIN PI_CHAIN_ID_DOMAIN)

/-- **`tmLcVerifyDesc`** — the Cosmos/Tendermint light-client verify-decision as an emitted IR-v2
AIR. PIs `[trusted_next_vals_root, committed_app_hash[0..8], chain_id_domain]` (11 total — the
committed app-hash is the FULL 256-bit value as nine radix-`2^31` MSB-first limbs, not a 31-bit
projection); the eleven verify-logic projections + four range slacks as hidden witnesses, the three
crypto results as carrier bits. The range table (`TID_range`) carries the strict-threshold and
time-window teeth. -/
def tmLcVerifyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-tm-lightclient-verify::v1"
  , traceWidth  := TM_LC_WIDTH
  , piCount     := PI_COUNT
  , tables      := [rangeTableDef TM_BITS
                   , ⟨TID_TALLY_LIMB,  "range_w16", 1, .rangeLimb TM_LIMB_BITS⟩
                   , ⟨TID_TALLY_CARRY, "range_w8",  1, .rangeLimb TM_CARRY_BITS⟩]
  , constraints := [chainMatchGate, heightAdjGate, twMonoGate, twMonoRange,
                    twDriftGate, twDriftRange, twTrustGate, twTrustRange]
                   ++ tallyRangeLookups ++ tdiffChainGates
                   ++ [edGate, vsetGate, epochGate, nextValsRootPin] ++ appHashPins
                   ++ [chainDomainPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3b — ⚑ THE WIDTH IS NOT A CONSTANT: containment + wrapped-slack, both as theorems.

A narrowed constant is a constant. What makes a range tooth an `≤` relation is exactly this pair:
the interval sits strictly INSIDE the field, and a slack the prover wanted to be negative lands
OUTSIDE it. Both were FALSE at `TM_BITS = 64`, and the third theorem exhibits the value that proves
it — the field encoding of the exactly-2/3 threshold slack, which the old table admitted. -/

/-- **THE INTERVAL IS INSIDE THE FIELD.** `2^29 = 536870912 < p = 2013265921`, so there are field
elements the table refuses at all — the precondition for it being a check. -/
theorem tm_range_is_inside_the_field :
    (2 : ℤ) ^ TM_BITS < Dregg2.Circuit.Emit.EffectLower.P := by
  norm_num [TM_BITS, Dregg2.Circuit.Emit.EffectLower.P]

/-- ⚑ **AND THE WRAP IS REFUSED.** A slack the prover wanted to be `−k`, for any magnitude
`0 < k ≤ 2^29` the interval can itself reach, is in the deployed mod-`p` reading the element
`p − k ≥ p − 2^29 = 1476395009` — nearly three times the interval ceiling. So each of the four
teeth is the inequality it is named for, with no field-wrap escape.

⚠ This statement is FALSE at `TM_BITS = 30` (`p − 2^30 = 939524097 < 2^30`) and catastrophically
false at the shipped `TM_BITS = 64`, where `p − 1` sits inside and EVERY negative slack was
admitted. -/
theorem tm_wrapped_slack_is_outside_the_range (k : ℤ) (hk : 0 < k)
    (hk' : k ≤ (2 : ℤ) ^ TM_BITS) :
    ¬ (0 ≤ Dregg2.Circuit.Emit.EffectLower.P - k
        ∧ Dregg2.Circuit.Emit.EffectLower.P - k < (2 : ℤ) ^ TM_BITS) := by
  rintro ⟨_, hlt⟩
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  have hb : ((2 : ℤ) ^ TM_BITS) = 536870912 := by norm_num [TM_BITS]
  rw [hp, hb] at hlt
  rw [hb] at hk'
  omega

/-- ⚑ **THE ADMITTED VALUE, EXHIBITED — the HISTORICAL record of the vacuity repair.** `2013265920`
is `p − 1`, the deployed encoding of the single-felt threshold slack `−1` that `signedPow = 2,
totalPow = 3` filled (exactly 2/3 — the sub-quorum Tendermint's STRICT threshold must reject). The
shipped 64-bit table CONTAINED it. Kept because the time-window teeth still ride a `rangeRows`
interval and the same reasoning governs them. -/
theorem tm_exactly_two_thirds_was_admitted_at_64 :
    ([2013265920] : List ℤ) ∈ rangeRows 64 := by
  rw [range_row_mem_iff]; norm_num

/-- …and the 29-bit table REFUSES it. The pair — one value, admitted then refused — is what made the
narrowing a repair rather than a renumbering. -/
theorem tm_exactly_two_thirds_is_refused :
    ([2013265920] : List ℤ) ∉ rangeRows TM_BITS := by
  rw [range_row_mem_iff]; norm_num [TM_BITS]

/-- The honest side was untouched: a genuine supermajority (`signedPow = 3` of `totalPow = 3`) fills
slack `2`, which the 29-bit table admits. -/
theorem tm_honest_supermajority_slack_is_admitted :
    ([2] : List ℤ) ∈ rangeRows TM_BITS := by
  rw [range_row_mem_iff]; norm_num [TM_BITS]

/-- **THE RANGE TOOTH IS THE EMITTED ONE.** The interval `airAccepts` reads for the three TIME
slacks (§5) is exactly membership in the declared table's rows — not a second, private notion of "in
range" that could be narrowed here while the descriptor keeps shipping the old one. -/
theorem tm_inRange_iff_mem_rangeRows (v : ℤ) :
    (0 ≤ v ∧ v < (2 : ℤ) ^ TM_BITS) ↔ [v] ∈ rangeRows TM_BITS :=
  (range_row_mem_iff v TM_BITS).symm

/-- …and the tables the descriptor DECLARES are the three the teeth query, by `rfl` on the emitted
object: the 29-bit time-slack table, the 16-bit tally-limb table, the 8-bit chain-carry table. -/
theorem tm_declared_tables :
    tmLcVerifyDesc.tables = [rangeTableDef TM_BITS
      , ⟨TID_TALLY_LIMB, "range_w16", 1, .rangeLimb TM_LIMB_BITS⟩
      , ⟨TID_TALLY_CARRY, "range_w8", 1, .rangeLimb TM_CARRY_BITS⟩] := rfl

/-- The width-tagged wire ids the Rust decoder reads, pinned: `.custom n` serializes as `5 + n`, so
the 16-bit table is id 85 and the 8-bit table is id 77, and `range_bits_for` recovers each width from
its own declaration. A drift in either id changes the descriptor bytes and therefore the VK. -/
theorem tm_tally_table_wire_ids :
    TID_TALLY_LIMB.wireId = 85 ∧ TID_TALLY_CARRY.wireId = 77 := by decide

/-! ### ⚑ §3c — THE LIMBED THRESHOLD: the capability, and the tooth that survived it.

Everything above is about a `rangeRows` interval over ONE felt. The threshold no longer lives there.
These are the facts about the LIMBED comparison, and the second one is the reason widening the
representable tally by 2^33× did not re-admit anything. -/

/-- ⚑ **THE CAPABILITY, ON THE EMITTED OBJECT.** The tally is four 16-bit limbs, so it represents
every value in `[0, 2^64)` — which contains CometBFT's `MaxTotalVotingPower = 2^60 − 1`
(`types/validator_set.go:27`) with four bits to spare, and Cosmos Hub's live total voting power
(328,774,071 at height 32,325,597, measured 2026-08-03) with 35.

The column it replaces held `[0, p) ⊂ [0, 2^31)`, and after the wrap-free repair the honest
threshold slack had to fit `[0, 2^29)`. -/
theorem tm_tally_capacity_holds_max_total_voting_power :
    (1152921504606846975 : ℤ) < (2 : ℤ) ^ (TM_LIMB_BITS * TM_TALLY_LIMBS) := by
  norm_num [TM_LIMB_BITS, TM_TALLY_LIMBS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_LIMBS]

/-- …and the SAME value does not fit one felt, at any declared width. This is the pair that makes the
widening a capability and not a preference: 572 million field moduli. -/
theorem tm_max_total_voting_power_does_not_fit_a_felt :
    (572000000 : ℤ) * Dregg2.Circuit.Emit.EffectLower.P < 1152921504606846975 := by
  norm_num [Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- ⚑ **AND THE REFUSAL NO LONGER MENTIONS THE FIELD.** If the true tallies fail the strict `>2/3`
threshold, NO assignment satisfies the emitted chain together with the difference-limb containment —
for EVERY limb width, including the widths at which the old single-felt tooth was vacuous.

The old tooth refused the exactly-2/3 sub-quorum because `p − 1 ∉ [0, 2^29)`: a fact about the FIELD
SIZE, false at 30 and catastrophically false at the 64 that shipped, and the entire reason a 404-width
census had to happen. This one refuses it because a limb vector of non-negative limbs denotes a
non-negative value and the difference is `−1`. -/
theorem tm_threshold_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 3 * LimbTally.limbValue bits a (LimbTally.aCols tdiffRungs)
      - 2 * LimbTally.limbValue bits a (LimbTally.bCols tdiffRungs) < 1) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 3 2 1 LimbTally.TALLY_CARRY_OFF TDIFF_TOP tdiffRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols tdiffRungs TDIFF_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-! ## §4 — non-vacuous per-gate lemmas (the emitted bodies bite, both directions). -/

/-- `chainMatchBody = 0 ↔ CHAIN_ID = TS_CHAIN_ID`. -/
theorem chainMatch_body_zero_iff (a : Assignment) :
    chainMatchBody.eval a = 0 ↔ a CHAIN_ID = a TS_CHAIN_ID := by
  simp only [chainMatchBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `heightAdjBody = 0 ↔ HEIGHT = TS_HEIGHT + 1`. -/
theorem heightAdj_body_zero_iff (a : Assignment) :
    heightAdjBody.eval a = 0 ↔ a HEIGHT = a TS_HEIGHT + 1 := by
  simp only [heightAdjBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `twMonoBody = 0 ↔ TW_MONO = TIME − HEADER_TIME − 1`. -/
theorem twMono_body_zero_iff (a : Assignment) :
    twMonoBody.eval a = 0 ↔ a TW_MONO = a TIME - a HEADER_TIME - 1 := by
  simp only [twMonoBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `twDriftBody = 0 ↔ TW_DRIFT = NOW + CLOCK_DRIFT − TIME`. -/
theorem twDrift_body_zero_iff (a : Assignment) :
    twDriftBody.eval a = 0 ↔ a TW_DRIFT = a NOW + a CLOCK_DRIFT - a TIME := by
  simp only [twDriftBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `twTrustBody = 0 ↔ TW_TRUST = HEADER_TIME + TRUSTING_PERIOD − NOW − 1`. -/
theorem twTrust_body_zero_iff (a : Assignment) :
    twTrustBody.eval a = 0 ↔ a TW_TRUST = a HEADER_TIME + a TRUSTING_PERIOD - a NOW - 1 := by
  simp only [twTrustBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `edBody = 0 ↔ ED_OK = 1`. -/
theorem ed_body_zero_iff (a : Assignment) : edBody.eval a = 0 ↔ a ED_OK = 1 := by
  simp only [edBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `vsetBody = 0 ↔ VSET_OK = 1`. -/
theorem vset_body_zero_iff (a : Assignment) : vsetBody.eval a = 0 ↔ a VSET_OK = 1 := by
  simp only [vsetBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `epochBody = 0 ↔ EPOCH_OK = 1`. -/
theorem epoch_body_zero_iff (a : Assignment) : epochBody.eval a = 0 ↔ a EPOCH_OK = 1 := by
  simp only [epochBody, EmittedExpr.eval]; constructor <;> intro h <;> omega

/-! ## §5 — `airAccepts`: the descriptor's LOGIC-acceptance predicate (the ℤ reading of its gate
bodies + the four range intervals), and the REFINEMENT to `tmVerifyDecision`. -/

/-- **`airAccepts a`** — the emitted verify-logic gates all vanish on row `a`, and each of the four
range slacks lies in the interval `[0, 2^TM_BITS)` (the denotation `range_row_mem_iff` connects the
emitted lookups to). This is "the descriptor accepts the logic of row `a`" (the published-anchor
pins are the addressing layer, orthogonal to the logic). -/
def airAccepts (a : Assignment) : Prop :=
  chainMatchBody.eval a = 0
  ∧ heightAdjBody.eval a = 0
  -- ⚑ THE LIMBED THRESHOLD, in the two pieces the emitted object has: the five generated chain
  -- gates vanish, and every one of the five difference limbs sits in `[0, 2^16)`. Together these
  -- are `3·signedPow − 2·totalPow − 1 ≥ 0` at ANY tally magnitude — see `LimbTally.cmp_sound`.
  ∧ LimbTally.BodiesVanish a tdiffChainBodies
  ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tdiffRungs TDIFF_TOP)
  ∧ twMonoBody.eval a = 0
  ∧ (0 ≤ a TW_MONO ∧ a TW_MONO < (2 : ℤ) ^ TM_BITS)
  ∧ twDriftBody.eval a = 0
  ∧ (0 ≤ a TW_DRIFT ∧ a TW_DRIFT < (2 : ℤ) ^ TM_BITS)
  ∧ twTrustBody.eval a = 0
  ∧ (0 ≤ a TW_TRUST ∧ a TW_TRUST < (2 : ℤ) ^ TM_BITS)
  ∧ edBody.eval a = 0
  ∧ vsetBody.eval a = 0
  ∧ epochBody.eval a = 0

/-- **THE REFINEMENT (soundness): a satisfying AIR witness ENTAILS `tmVerifyDecision` accept.**
Fed a row `a` whose columns read the update's true projections (the honest-witness relation — the
scalars as felts, the carrier bits as `if · then 1 else 0`), if the emitted verify-logic gates
accept, then the exported scalar decision `tmVerifyDecision` accepts those projections. This is the
load-bearing tie: a STARK that satisfies `tmLcVerifyDesc` proves the object `tmNoForgery` is stated
over. The four range floors discharge the strict `>2/3` threshold and the three time-window legs.
(`ED_OK = 1` is required for acceptance — it names the Ed25519 provenance of `SIGNED_POW` in the
trace — but is not itself read by the scalar decision, which trusts `SIGNED_POW` as a `Nat`.) -/
theorem tmLcAir_sound (a : Assignment)
    (chainId tsChainId height tsHeight headerTime time now clockDrift trustingPeriod : Nat)
    (epochBindOk selfBindOk : Bool) (totalPow signedPow : Nat)
    (hChainId : a CHAIN_ID = (chainId : ℤ)) (hTsChainId : a TS_CHAIN_ID = (tsChainId : ℤ))
    (hHeight : a HEIGHT = (height : ℤ)) (hTsHeight : a TS_HEIGHT = (tsHeight : ℤ))
    (hHeaderTime : a HEADER_TIME = (headerTime : ℤ)) (hTime : a TIME = (time : ℤ))
    (hNow : a NOW = (now : ℤ)) (hClockDrift : a CLOCK_DRIFT = (clockDrift : ℤ))
    (hTrustingPeriod : a TRUSTING_PERIOD = (trustingPeriod : ℤ))
    (hTotalPow : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs) = (totalPow : ℤ))
    (hSignedPow : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs) = (signedPow : ℤ))
    (hEpoch : a EPOCH_OK = (if epochBindOk then (1 : ℤ) else 0))
    (hVset : a VSET_OK = (if selfBindOk then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    tmVerifyDecision chainId tsChainId height tsHeight headerTime time now clockDrift trustingPeriod
      epochBindOk selfBindOk totalPow signedPow = true := by
  obtain ⟨hchainB, hheightB, htdiffBodies, htdiffLimbs, htwmB, ⟨htwm0, _⟩, htwdB, ⟨htwd0, _⟩,
    htwtB, ⟨htwt0, _⟩, _hedB, hvsetB, hepochB⟩ := hacc
  -- chain-id match.
  have hchainP : chainId = tsChainId := by
    have h := (chainMatch_body_zero_iff a).mp hchainB
    rw [hChainId, hTsChainId] at h; exact_mod_cast h
  -- adjacent height.
  have hheightP : height = tsHeight + 1 := by
    have h := (heightAdj_body_zero_iff a).mp hheightB
    rw [hHeight, hTsHeight] at h; exact_mod_cast h
  -- monotonic advance: headerTime < time.
  have htmono : headerTime < time := by
    have hid := (twMono_body_zero_iff a).mp htwmB
    have h0 : (0 : ℤ) ≤ a TW_MONO := htwm0
    rw [hid, hTime, hHeaderTime] at h0
    have : (headerTime : ℤ) < (time : ℤ) := by linarith
    exact_mod_cast this
  -- not-from-the-future: time ≤ now + clockDrift.
  have htdrift : time ≤ now + clockDrift := by
    have hid := (twDrift_body_zero_iff a).mp htwdB
    have h0 : (0 : ℤ) ≤ a TW_DRIFT := htwd0
    rw [hid, hNow, hClockDrift, hTime] at h0
    have : (time : ℤ) ≤ (now : ℤ) + (clockDrift : ℤ) := by linarith
    exact_mod_cast this
  -- still in trusting period: now < headerTime + trustingPeriod.
  have httrust : now < headerTime + trustingPeriod := by
    have hid := (twTrust_body_zero_iff a).mp htwtB
    have h0 : (0 : ℤ) ≤ a TW_TRUST := htwt0
    rw [hid, hHeaderTime, hTrustingPeriod, hNow] at h0
    have : (now : ℤ) < (headerTime : ℤ) + (trustingPeriod : ℤ) := by linarith
    exact_mod_cast this
  -- ⚑ strict >2/3 threshold: `2·totalPow < 3·signedPow`, AT ANY TALLY MAGNITUDE.
  -- `LimbTally.emitted_chain_sound` reads the five generated chain gates and the five
  -- difference-limb containments and returns `1 ≤ 3·A − 2·B` over the LIMB VALUES; the two
  -- hypotheses above say those values are the true `signedPow` / `totalPow`. Nothing here bounds
  -- either tally — that bound was the whole capability limit, and it is gone.
  have hthresh : 2 * totalPow < 3 * signedPow := by
    have hcmp := LimbTally.emitted_chain_sound htdiffBodies htdiffLimbs
    rw [hSignedPow, hTotalPow] at hcmp
    have : 2 * (totalPow : ℤ) < 3 * (signedPow : ℤ) := by linarith
    exact_mod_cast this
  -- epoch-binding carrier.
  have hepochOk : epochBindOk = true := by
    have h : a EPOCH_OK = 1 := (epoch_body_zero_iff a).mp hepochB
    rw [hEpoch] at h; cases epochBindOk with | true => rfl | false => simp at h
  -- self-binding carrier.
  have hvsetOk : selfBindOk = true := by
    have h : a VSET_OK = 1 := (vset_body_zero_iff a).mp hvsetB
    rw [hVset] at h; cases selfBindOk with | true => rfl | false => simp at h
  -- assemble the eight-conjunct decision.
  simp only [tmVerifyDecision, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨hchainP, hheightP⟩, htmono⟩, htdrift⟩, httrust⟩, hepochOk⟩, hvsetOk⟩, hthresh⟩

/-- **THE PAYOFF: a satisfying AIR witness ENTAILS Tendermint foreign-validity (no-forgery, routed
through the emitted AIR).** GIVEN the named SHA-256 CR carrier (`hcr : L.hashCR`), if a row `a` reads
update `u`'s true projections under trusted state `ts` (the power sums, the two SHA-256 binding
results as carrier bits, the Ed25519 carrier set) and the emitted verify-logic gates accept, then `u`
is Tendermint-VALID relative to `ts` — its `validatorsHash` genuinely commits its validator set, that
commitment BINDS (uniqueness via `noCollision`), and a sub-list carrying strictly more than 2/3 of
the total power GENUINELY signed the header's sign-bytes (via `sigSound`). So a STARK proving
`tmLcVerifyDesc` carries `tmNoForgery`: the portable, trustless proof of Cosmos finality. -/
theorem tmLcAir_no_forgery (L : CryptoLeaf) [DecidableEq L.Digest]
    (sb : TmHeader L.Digest → L.Msg) (enc : List (TmValidator L.PubKey) → L.Msg)
    (hcr : L.hashCR) (ts : TmTrustedState L) (u : TmUpdate L) (a : Assignment)
    (hChainId : a CHAIN_ID = (u.header.chainId : ℤ)) (hTsChainId : a TS_CHAIN_ID = (ts.chainId : ℤ))
    (hHeight : a HEIGHT = (u.header.height : ℤ)) (hTsHeight : a TS_HEIGHT = (ts.height : ℤ))
    (hHeaderTime : a HEADER_TIME = (ts.headerTime : ℤ)) (hTime : a TIME = (u.header.time : ℤ))
    (hNow : a NOW = (ts.now : ℤ)) (hClockDrift : a CLOCK_DRIFT = (ts.clockDrift : ℤ))
    (hTrustingPeriod : a TRUSTING_PERIOD = (ts.trustingPeriod : ℤ))
    (hTotalPow : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs)
      = (totalPower u.validators : ℤ))
    (hSignedPow : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs)
      = (signedPower L (sb u.header) u.validators u.commit : ℤ))
    (hEpoch : a EPOCH_OK =
      (if (decide (L.hash (enc u.validators) = ts.nextValidatorsHash)) then (1 : ℤ) else 0))
    (hVset : a VSET_OK =
      (if (decide (L.hash (enc u.validators) = u.header.validatorsHash)) then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    TmForeignValid L sb enc u := by
  -- `tmLcAir_sound` at `u`'s projections yields exactly `tmProjectedDecision L sb enc ts u = true`.
  have hdec := tmLcAir_sound a u.header.chainId ts.chainId u.header.height ts.height
      ts.headerTime u.header.time ts.now ts.clockDrift ts.trustingPeriod
      (decide (L.hash (enc u.validators) = ts.nextValidatorsHash))
      (decide (L.hash (enc u.validators) = u.header.validatorsHash))
      (totalPower u.validators) (signedPower L (sb u.header) u.validators u.commit)
      hChainId hTsChainId hHeight hTsHeight hHeaderTime hTime hNow hClockDrift hTrustingPeriod
      hTotalPow hSignedPow hEpoch hVset hacc
  have hproj : tmProjectedDecision L sb enc ts u = true := hdec
  exact tmVerifyDecision_no_forgery L sb enc hcr ts u hproj

/-- **Completeness (the honest prover CAN fill the row).** For any decision-accepting projections, an
honest row that fills the three time slacks with the true differences, the tally difference chain
with its true limbs and carries, and the carrier bits with the true results, is accepted by the
emitted logic. This is the non-vacuity partner of soundness: the AIR is satisfiable EXACTLY on
accepted updates, not vacuously empty.

⚑ **WHAT IS NO LONGER A HYPOTHESIS, AND IT IS THE POINT OF THIS WHOLE CHANGE.** The previous version
required `3·signedPow − 2·totalPow − 1 < 2^TM_BITS` — a bound on the TALLY, at 2^29 — because the
threshold slack was one felt. CometBFT's `MaxTotalVotingPower` is `2^60 − 1` and Solana's live stake
is 2^58.6; neither ever satisfied it, at 29 bits or at the 64 that shipped, because a felt holds 30.9
bits either way. **That hypothesis is gone.** What replaces it is the honest chain itself
(`hTdiffChain`/`hTdiffLimbs`), which an honest prover constructs by `LimbTally.fillDigit` /
`LimbTally.fillCarry` at ANY tally magnitude a `u64` holds — and `tmLcAir_accepts_at_max_total_voting_power`
(§7) exhibits exactly that at `MaxTotalVotingPower`.

⚠ The three TIME hypotheses remain at `2^29`, and that is a REAL residual, not an oversight: CometBFT
header times are `google.protobuf.Timestamp` with nanoseconds (`proto/tendermint/types/types.proto:52`),
where a 14-day trusting period is `1.2096e15` (50.1 bits) and does NOT fit. The caller must supply
SECONDS. The same limb machinery closes it — the time window is `1·X − 1·Y − γ ≥ 0`, the identical
shape at `α = β = 1` — and that is named, measured, and NOT DONE here. -/
theorem tmLcAir_complete (a : Assignment)
    (chainId tsChainId height tsHeight headerTime time now clockDrift trustingPeriod : Nat)
    (epochBindOk selfBindOk : Bool) (totalPow signedPow : Nat)
    (hChainId : a CHAIN_ID = (chainId : ℤ)) (hTsChainId : a TS_CHAIN_ID = (tsChainId : ℤ))
    (hHeight : a HEIGHT = (height : ℤ)) (hTsHeight : a TS_HEIGHT = (tsHeight : ℤ))
    (hHeaderTime : a HEADER_TIME = (headerTime : ℤ)) (hTime : a TIME = (time : ℤ))
    (hNow : a NOW = (now : ℤ)) (hClockDrift : a CLOCK_DRIFT = (clockDrift : ℤ))
    (hTrustingPeriod : a TRUSTING_PERIOD = (trustingPeriod : ℤ))
    (hEpoch : a EPOCH_OK = (if epochBindOk then (1 : ℤ) else 0))
    (hVset : a VSET_OK = (if selfBindOk then (1 : ℤ) else 0))
    (hEd : a ED_OK = 1)
    (hTdiffChain : LimbTally.BodiesVanish a tdiffChainBodies)
    (hTdiffLimbs : LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tdiffRungs TDIFF_TOP))
    (hTwMono : a TW_MONO = (time : ℤ) - (headerTime : ℤ) - 1)
    (hTwDrift : a TW_DRIFT = (now : ℤ) + (clockDrift : ℤ) - (time : ℤ))
    (hTwTrust : a TW_TRUST = (headerTime : ℤ) + (trustingPeriod : ℤ) - (now : ℤ) - 1)
    (hTwMonoLt : (time : ℤ) - (headerTime : ℤ) - 1 < (2 : ℤ) ^ TM_BITS)
    (hTwDriftLt : (now : ℤ) + (clockDrift : ℤ) - (time : ℤ) < (2 : ℤ) ^ TM_BITS)
    (hTwTrustLt : (headerTime : ℤ) + (trustingPeriod : ℤ) - (now : ℤ) - 1 < (2 : ℤ) ^ TM_BITS)
    (hdec : tmVerifyDecision chainId tsChainId height tsHeight headerTime time now clockDrift
      trustingPeriod epochBindOk selfBindOk totalPow signedPow = true) :
    airAccepts a := by
  simp only [tmVerifyDecision, Bool.and_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨⟨⟨⟨⟨⟨hchainP, hheightP⟩, htmono⟩, htdrift⟩, httrust⟩, hepochOk⟩, hvsetOk⟩, hthresh⟩ := hdec
  refine ⟨?_, ?_, hTdiffChain, hTdiffLimbs, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [chainMatch_body_zero_iff, hChainId, hTsChainId]; exact_mod_cast hchainP
  · rw [heightAdj_body_zero_iff, hHeight, hTsHeight]; exact_mod_cast hheightP
  · rw [twMono_body_zero_iff, hTwMono, hTime, hHeaderTime]
  · rw [hTwMono]
    have : (headerTime : ℤ) < (time : ℤ) := by exact_mod_cast htmono
    linarith
  · rw [hTwMono]; exact hTwMonoLt
  · rw [twDrift_body_zero_iff, hTwDrift, hNow, hClockDrift, hTime]
  · rw [hTwDrift]
    have : (time : ℤ) ≤ (now : ℤ) + (clockDrift : ℤ) := by exact_mod_cast htdrift
    linarith
  · rw [hTwDrift]; exact hTwDriftLt
  · rw [twTrust_body_zero_iff, hTwTrust, hHeaderTime, hTrustingPeriod, hNow]
  · rw [hTwTrust]
    have : (now : ℤ) < (headerTime : ℤ) + (trustingPeriod : ℤ) := by exact_mod_cast httrust
    linarith
  · rw [hTwTrust]; exact hTwTrustLt
  · rw [ed_body_zero_iff]; exact hEd
  · rw [vset_body_zero_iff, hVset]; simp [hvsetOk]
  · rw [epoch_body_zero_iff, hEpoch]; simp [hepochOk]

/-! ## §6 — the emitted wire JSON (byte-pinned golden) + shape pins. -/

-- The Rust decoder ingests THIS string (`parse_vm_descriptor2`); byte-pinned golden (a drift on
-- either side breaks this `#guard`). ⚑ RE-EMITTED 2026-08-03 for the limbed tally: trace width
-- 29 → 43, three declared range tables (29 / 16 / 8) where there was one, and the single
-- threshold gate + single lookup replaced by five GENERATED chain gates and seventeen per-limb
-- lookups. Captured from this module's own `emitVmJson2`.
#guard emitVmJson2 tmLcVerifyDesc ==
  "{\"name\":\"dregg-tm-lightclient-verify::v1\",\"ir\":2,\"trace_width\":43,\"public_input_count\":11,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29},{\"id\":85,\"name\":\"range_w16\",\"arity\":1,\"sem\":\"range\",\"bits\":16},{\"id\":77,\"name\":\"range_w8\",\"arity\":1,\"sem\":\"range\",\"bits\":8}],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":9}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}}},\"r\":{\"t\":\"var\",\"v\":5}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":10}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":11}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":15}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":17}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":18}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":19}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":20}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":21}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":22}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":23}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":24}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":25}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":26}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":27}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":28}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":29}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":30}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":31}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":23}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"const\",\"v\":8388607}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":29}}},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":17}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":30}}},\"r\":{\"t\":\"var\",\"v\":29}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":18}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":31}}},\"r\":{\"t\":\"var\",\"v\":30}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}},\"r\":{\"t\":\"const\",\"v\":-128}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":32,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":33,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":34,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":35,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":36,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":37,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":38,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":39,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":40,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":41,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":42,\"pi_index\":10}],\"hash_sites\":[],\"ranges\":[]}"

-- Shape pins (robust; a layout drift moves these).
theorem tm_shape_pins :
    tmLcVerifyDesc.traceWidth = TM_LC_WIDTH
      ∧ tmLcVerifyDesc.piCount = PI_COUNT
      ∧ tmLcVerifyDesc.constraints.length = 44
      ∧ tmLcVerifyDesc.tables.length = 3 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  decide

/-- ⚑ **THE TALLY IS SEVENTEEN LOOKUPS, NOT ONE.** Thirteen 16-bit limb checks plus four 8-bit carry
checks, where the single-felt threshold carried exactly ONE. A re-emission that dropped a limb moves
this number; the old shape had no number to move. -/
theorem tm_tally_lookup_count : tallyRangeLookups.length = 17 := by decide

/-- ⚑ **THE IR'S WIDTH VERDICT IS LOAD-BEARING ON THIS DEPLOYED DESCRIPTOR.** All four limbed
quantities pass `EffectAirIR.LimbsLeg.mainRailOk`, which REFUSES an empty limb vector and any limb
width above the wrap-free ceiling 29 — the exact class this descriptor shipped in at 64 bits. The
teeth in `tallyRangeLookups` are `EffectLower.lowerLimbsLeg`'s output, so the verdict gates the
emitted object rather than commenting on it. -/
theorem tm_tally_legs_are_expressible :
    totalPowLeg.mainRailOk = true ∧ signedPowLeg.mainRailOk = true
      ∧ tdiffLeg.mainRailOk = true ∧ tdiffCarryLeg.mainRailOk = true := by decide

/-- …and the width this AIR SHIPPED is one the IR now refuses outright. A verdict that could not go
red would be decoration; this is the red, on the actual historical constant. -/
theorem tm_the_shipped_width_is_refused_by_the_ir :
    ({ totalPowLeg with bits := 64 } : EffectAirIR.LimbsLeg).mainRailOk = false
      ∧ ({ totalPowLeg with bits := 30 } : EffectAirIR.LimbsLeg).mainRailOk = false := by decide

/-- ⚑ **THE CAPACITY, READ OFF THE IR.** The operands carry 64 bits — a `u64`, CometBFT's own type
for voting power — and the difference carries 80, because `3·A − 2·B − 1` needs two bits beyond `A`.
The `RangeLeg` these replace carried ONE column, i.e. 30.9 bits, whatever width it declared. -/
theorem tm_tally_leg_capacities :
    totalPowLeg.capacityBits = 64 ∧ signedPowLeg.capacityBits = 64
      ∧ tdiffLeg.capacityBits = 80 := by decide

/-! ### ⚑ The mod-`p` bridge's PREMISE, stated where it can be checked.

`airAccepts` conjoins only the DIFFERENCE-limb containment, because that is the only containment the
threshold argument uses (`LimbTally.cmp_sound` takes no operand or carry bound — see
`chain_recomposes`). The mod-`p` ↔ `ℤ` transfer needs MORE: every operand limb in `[0, 2^16)` and
every carry in `[0, 2^8)`.

⚠ Those live in the descriptor's own lookups rather than in `airAccepts`, and a premise that lives in
an emitted artifact but is never written down is exactly the kind of thing that reads as discharged
when it is only assumed. So it is written down. -/

/-- Everything `tallyRangeLookups` enforces, as one predicate: the operand limbs and the carries, at
their own declared widths. The difference limbs are already in `airAccepts`. -/
def tallyOperandsContained (a : Assignment) : Prop :=
  LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.aCols tdiffRungs)
  ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.bCols tdiffRungs)
  ∧ LimbTally.LimbsInRange TM_CARRY_BITS a (LimbTally.carryCols tdiffRungs)

/-- ⚑ **NO ALIAS ON THE FIRST RUNG, FROM THE DESCRIPTOR'S OWN LOOKUPS.** Given exactly what
`tallyRangeLookups` enforces, the least-significant threshold gate's `ℤ` value lies strictly inside
`(−p, p)` — so `≡ 0 (mod p)` IS `= 0` over `ℤ` there, and `LimbTally.chain_recomposes` transfers to
the deployed denotation instead of being asserted over it.

The rung shown is rung 0, the one carrying the `γ = 1` strictness constant and therefore the widest
`ℤ` image of the five. -/
theorem tm_first_rung_has_no_alias (a : Assignment)
    (hd : LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tdiffRungs TDIFF_TOP))
    (hops : tallyOperandsContained a) :
    -Dregg2.Circuit.Emit.EffectLower.P
        < 3 * a (SIGNED_POW_LIMB 0) - 2 * a (TOTAL_POW_LIMB 0) - 1
          + (0 - LimbTally.TALLY_CARRY_OFF) - a (TDIFF_LIMB 0)
          - (a (TDIFF_CARRY 0) - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ TM_LIMB_BITS
      ∧ 3 * a (SIGNED_POW_LIMB 0) - 2 * a (TOTAL_POW_LIMB 0) - 1
          + (0 - LimbTally.TALLY_CARRY_OFF) - a (TDIFF_LIMB 0)
          - (a (TDIFF_CARRY 0) - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ TM_LIMB_BITS
        < Dregg2.Circuit.Emit.EffectLower.P := by
  obtain ⟨⟨hs, _⟩, ⟨ht, _⟩, ⟨hc, _⟩⟩ := hops
  obtain ⟨hdl, _⟩ := hd
  exact LimbTally.rung_no_alias_at_deployed_constants _ _ _ 0 _
    hs ht hdl ⟨le_rfl, by norm_num [LimbTally.TALLY_CARRY_BITS]⟩ hc

/-- …and the chain is FIVE generated gates for four rungs — one per rung plus the closure gate that
forces the final carry into the top difference limb. Without the closure gate the prover could dump
a residue into a carry nothing reads, and the recomposition would be off by `2^64`. -/
theorem tm_chain_gate_count : tdiffChainGates.length = 5 := by decide

/-- The three crypto carriers are real trace columns and none is PI-bound (the results ride hidden). -/
theorem tm_carriers_are_hidden_columns :
    ED_OK < TM_LC_WIDTH ∧ VSET_OK < TM_LC_WIDTH ∧ EPOCH_OK < TM_LC_WIDTH := by decide

/-- The tally block occupies columns 15..31 contiguously, below the published anchors: four
total-power limbs, four signed-power limbs, five difference limbs, four carries. -/
theorem tm_tally_block_layout :
    TOTAL_POW_LIMB 0 = 15 ∧ TOTAL_POW_LIMB 3 = 18
      ∧ SIGNED_POW_LIMB 0 = 19 ∧ SIGNED_POW_LIMB 3 = 22
      ∧ TDIFF_LIMB 0 = 23 ∧ TDIFF_TOP = 27
      ∧ TDIFF_CARRY 0 = 28 ∧ TDIFF_CARRY 3 = 31
      ∧ TDIFF_CARRY 3 < TRUSTED_NEXT_VALS_ROOT := by decide

/-- The widened committed-app-hash anchor is unchanged by the tally work, only shifted: nine limbs,
contiguous cols 33..41 → PI 1..9, MSB-first, `⌈256/31⌉ = 9` covering the full 256 bits. -/
theorem tm_app_hash_anchor_layout :
    COMMITTED_APP_HASH_LIMBS = 9 ∧ appHashPins.length = COMMITTED_APP_HASH_LIMBS
      ∧ COMMITTED_APP_HASH 0 = 33 ∧ COMMITTED_APP_HASH 8 = 41
      ∧ CHAIN_ID_DOMAIN = 42 ∧ PI_CHAIN_ID_DOMAIN = 10
      ∧ COMMITTED_APP_HASH 8 < CHAIN_ID_DOMAIN
      ∧ 31 * COMMITTED_APP_HASH_LIMBS ≥ 256 := by decide

/-! ## §7 — ⚑ THE MEASUREMENT: A REAL VALIDATOR SET, AT COMETBFT'S PROTOCOL MAXIMUM.

This is the section the whole change exists for. Everything below is a NAMED THEOREM over an explicit
row of the emitted descriptor — the same row, cell for cell, that
`circuit/tests/tendermint_lightclient_proves.rs` hands the deployed prover.

`totalPow = 1152921504606846975` is CometBFT's `MaxTotalVotingPower`, `int64(math.MaxInt64) / 8`
(`cometbft/types/validator_set.go:27`) — the largest voting power the protocol permits, exactly
`2^60 − 1`. It is 572 million times the BabyBear modulus and it never fit a column.

⚑ And the two rows below differ by **ONE UNIT OF VOTING POWER OUT OF 2^60**:
`signedPow = 768614336404564651` is the SMALLEST value satisfying CometBFT's strict `3·S > 2·T`
(`tendermint-rs/tendermint/src/trust_threshold.rs:98`); `768614336404564650` is exactly 2/3 and must
be REJECTED. The first ACCEPTS, the second has no satisfying assignment. -/

/-- The honest row at protocol maximum, as the cell vector the Rust harness fills. Written as a LIST
so the Lean row and the Rust trace row are literally the same 43 numbers in the same order — a
divergence between the two is a diff on one object, not a comparison of two readings. -/
def tmMaxScaleCells : List ℤ :=
  [ 7, 7                            -- CHAIN_ID, TS_CHAIN_ID
  , 32325598, 32325597              -- HEIGHT, TS_HEIGHT (Cosmos Hub height, live 2026-08-03)
  , 1785734519, 1785734619          -- HEADER_TIME, TIME (seconds; see the ns residual below)
  , 1785734624, 40, 1209600         -- NOW, CLOCK_DRIFT (modal live: 40s), TRUSTING_PERIOD (14d)
  , 99, 45, 1209494                 -- TW_MONO, TW_DRIFT, TW_TRUST
  , 1, 1, 1                         -- ED_OK, VSET_OK, EPOCH_OK
  , 65535, 65535, 65535, 4095       -- TOTAL_POW  limbs = 1152921504606846975 = 2^60 − 1
  , 43691, 43690, 43690, 2730       -- SIGNED_POW limbs = 768614336404564651
  , 2, 0, 0, 0, 0                   -- TDIFF      limbs = 3·S − 2·T − 1 = 2
  , 128, 128, 128, 128              -- TDIFF carries, offset (honest carry 0 rides as 128)
  , 11111                           -- TRUSTED_NEXT_VALS_ROOT
  , 1, 2, 3, 4, 5, 6, 7, 8, 9       -- COMMITTED_APP_HASH limbs 0..8
  , 22222 ]                         -- CHAIN_ID_DOMAIN

/-- The row is exactly as wide as the descriptor. -/
theorem tmMaxScaleCells_width : tmMaxScaleCells.length = TM_LC_WIDTH := by decide

/-- The row as an `Assignment`. -/
def tmMaxScaleRow : Assignment := fun i => tmMaxScaleCells.getD i 0

/-- ⚑ **THE TALLY THE ROW DENOTES IS CometBFT's `MaxTotalVotingPower`.** Four 16-bit limbs, read by
`limbValue`, recompose to `2^60 − 1` exactly. -/
theorem tmMaxScaleRow_total_is_max_voting_power :
    LimbTally.limbValue TM_LIMB_BITS tmMaxScaleRow (LimbTally.bCols tdiffRungs)
      = 1152921504606846975 := by decide

/-- …and the signed power is the SMALLEST strict supermajority of it. -/
theorem tmMaxScaleRow_signed_is_minimal_supermajority :
    LimbTally.limbValue TM_LIMB_BITS tmMaxScaleRow (LimbTally.aCols tdiffRungs)
      = 768614336404564651 := by decide

/-- …which really is minimal: `3·S > 2·T` holds at `S`, and FAILS one unit below. -/
theorem minimal_supermajority_is_minimal :
    2 * 1152921504606846975 < 3 * 768614336404564651
      ∧ ¬ (2 * 1152921504606846975 < 3 * 768614336404564650) := by decide

/-- ⚑⚑ **THE DELIVERABLE: THE EMITTED AIR ACCEPTS A VALIDATOR SET AT COMETBFT'S PROTOCOL MAXIMUM.**

Every gate of `tmLcVerifyDesc` vanishes on this row and every range tooth admits it. At a single felt
this update could not be REPRESENTED, let alone accepted: `3·signedPow = 2305843009213693953` is
1.14 billion times the BabyBear modulus, so no declared width — 29, 30, 64, or 128 — ever made it
provable. -/
theorem tmLcAir_accepts_at_max_total_voting_power : airAccepts tmMaxScaleRow := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide,
    ⟨by decide, by decide⟩, by decide, ⟨by decide, by decide⟩, by decide, by decide, by decide⟩
  · decide
  · decide

/-- ⚑ **AND THE TOOTH SURVIVED THE WIDENING, AT THE SAME SCALE.** The exactly-2/3 sub-quorum
(`signedPow = 768614336404564650`, ONE unit below the row above) makes the true difference `−1`, and
`LimbTally.emitted_chain_refuses` gives: NO assignment of difference limbs and carries satisfies the
chain together with the containments. Not "the wrapped value lands outside an interval" — there is no
limb vector of non-negative limbs denoting `−1`.

⚠ This is the exact failure mode the goal warned about — a wider representation re-admitting the
sub-quorum. It does not, and the reason is structural rather than arithmetic-on-`p`. -/
theorem tmLcAir_refuses_exactly_two_thirds_at_max_voting_power (a : Assignment)
    (hTotal : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs)
      = 1152921504606846975)
    (hSigned : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs)
      = 768614336404564650) :
    ¬ (LimbTally.BodiesVanish a tdiffChainBodies
        ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tdiffRungs TDIFF_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal, hSigned]; norm_num

/-- ⚑ **THE EMPTY VALIDATOR SET IS REFUSED TOO**, and by the same tooth: at `totalPow = signedPow = 0`
the difference is `−1`. -/
theorem tmLcAir_refuses_the_empty_validator_set (a : Assignment)
    (hTotal : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs) = 0)
    (hSigned : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs) = 0) :
    ¬ (LimbTally.BodiesVanish a tdiffChainBodies
        ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tdiffRungs TDIFF_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal, hSigned]; norm_num

/-- ⚑⚑ **AND THE CLAIM THAT USED TO SIT ON THAT THEOREM IS FALSE — REFUTED, not softened.**

The docstring above read *"Tendermint's strict threshold subsumes the empty-set floor its Solana and
Midnight siblings carry as a separate `TPOS` slack."* That is true at `signedPow = 0` and **FALSE
everywhere else on the empty set.** This descriptor has NO positivity floor (one `chainBodies` call,
`tm_chain_gate_count`), `tmVerifyDecision` has no `0 < totalPow` conjunct
(`LightClientTendermintGate.lean:104-113`), and nothing anywhere forces `signedPow ≤ totalPow` —
both are independent witnessed limb vectors carrying only their own 16-bit lookups.

So at `totalPow = 0, signedPow = 1` the strict difference is `3·1 − 2·0 − 1 = 2 ≥ 0`: an honest,
in-range, **ACCEPTING** fill. A validator set with NO voting power and a claimed one unit of signed
power satisfies this AIR's threshold. `cmp_sound`'s conclusion is `γ ≤ α·A − β·B`, which bounds the
DIFFERENCE and says nothing about the denominator being real.

⚑ This is the same shape as the Solana empty-stake finding it was written to contrast with, and it is
why Solana keeps its `TPOS` floor even now that its quorum is strict: a strict quorum refuses `(0,0)`
and NOTHING ELSE at `total = 0`. Solana's floor refuses `total = 0` at EVERY `rooted`
(`LightClientSolanaAir.sol_two_teeth_are_independent`); Tendermint has no such gate.

⚠ NOT FIXED HERE — a floor chain is a new five-gate chain, five difference limbs, four carries, a
width bump and a VK rotation, i.e. the same size as the Solana strictness repair. What is landed is
the REFUTATION, so the claim cannot be cited again while it is false. -/
theorem tm_strict_threshold_does_not_subsume_an_emptiness_floor :
    -- the exhibited empty-set-with-signed-power point SATISFIES the strict threshold…
    (1 : ℤ) ≤ 3 * 1 - 2 * 0
    -- …while the SAME point fails the positivity floor Solana and Midnight carry separately.
    ∧ ¬ ((1 : ℤ) ≤ 1 * 0 - 0 * 0)
    -- And the only case the strict threshold does catch on the empty set is `signed = 0`.
    ∧ ¬ ((1 : ℤ) ≤ 3 * 0 - 2 * 0) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- …and the DECISION-level statement of the same refutation: `tmVerifyDecision` accepts an update
whose total voting power is ZERO, given the scalar/carrier conjuncts. The threshold conjunct is the
only one that reads the tally, and `2·0 < 3·1` holds. -/
theorem tm_decision_accepts_a_zero_power_validator_set :
    Dregg2.Bridge.LightClientTendermintGate.tmVerifyDecision
      7 7 11 10 5 6 6 1 100 true true 0 1 = true := by decide

/-- Chain-id: a matching pair accepts, a mismatch is refused (cross-chain replay fail-closure). -/
theorem tm_chain_id_discriminates :
    chainMatchBody.eval (fun i => if i = CHAIN_ID then 5 else if i = TS_CHAIN_ID then 5 else 0) = 0
      ∧ chainMatchBody.eval
          (fun i => if i = CHAIN_ID then 6 else if i = TS_CHAIN_ID then 5 else 0) ≠ 0 := by
  refine ⟨by decide, by decide⟩

/-- Adjacent height: `h = th + 1` accepts, a non-adjacent height is refused. -/
theorem tm_height_adjacency_discriminates :
    heightAdjBody.eval (fun i => if i = HEIGHT then 11 else if i = TS_HEIGHT then 10 else 0) = 0
      ∧ heightAdjBody.eval
          (fun i => if i = HEIGHT then 12 else if i = TS_HEIGHT then 10 else 0) ≠ 0 := by
  refine ⟨by decide, by decide⟩

/-- The three TIME teeth, both polarities, at the 29-bit width they still ride: an honest slack is
admitted, a negative one is refused. -/
theorem tm_time_window_teeth_discriminate :
    ([99] : List ℤ) ∈ rangeRows TM_BITS ∧ ¬ (([-6] : List ℤ) ∈ rangeRows TM_BITS)
      ∧ ([1209494] : List ℤ) ∈ rangeRows TM_BITS := by
  refine ⟨?_, ?_, ?_⟩
  · rw [range_row_mem_iff]; norm_num [TM_BITS]
  · rw [range_row_mem_iff]; norm_num
  · rw [range_row_mem_iff]; norm_num [TM_BITS]

/-- Carriers: a set bit accepts, a cleared (forged) bit is refused. -/
theorem tm_carrier_bits_discriminate :
    (edBody.eval (fun i => if i = ED_OK then 1 else 0) = 0 ∧ edBody.eval (fun _ => 0) ≠ 0)
      ∧ (vsetBody.eval (fun i => if i = VSET_OK then 1 else 0) = 0
          ∧ vsetBody.eval (fun _ => 0) ≠ 0)
      ∧ (epochBody.eval (fun i => if i = EPOCH_OK then 1 else 0) = 0
          ∧ epochBody.eval (fun _ => 0) ≠ 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## §8 — axiom hygiene. -/

#assert_axioms chainMatch_body_zero_iff
#assert_axioms twTrust_body_zero_iff
#assert_axioms tmLcAir_sound
#assert_axioms tmLcAir_no_forgery
-- The 29-bit width repair (the TIME teeth still ride it).
#assert_axioms tm_range_is_inside_the_field
#assert_axioms tm_wrapped_slack_is_outside_the_range
#assert_axioms tm_exactly_two_thirds_was_admitted_at_64
#assert_axioms tm_exactly_two_thirds_is_refused
-- ⚑ The limbed tally: capability, the field-free refusal, the emitted shape.
#assert_axioms tm_tally_capacity_holds_max_total_voting_power
#assert_axioms tm_max_total_voting_power_does_not_fit_a_felt
#assert_axioms tm_threshold_refusal_is_field_independent
#assert_axioms tm_tally_table_wire_ids
#assert_axioms tm_declared_tables
#assert_axioms tm_shape_pins
#assert_axioms tm_tally_lookup_count
#assert_axioms tm_tally_legs_are_expressible
#assert_axioms tm_the_shipped_width_is_refused_by_the_ir
#assert_axioms tm_tally_leg_capacities
#assert_axioms tm_first_rung_has_no_alias
#assert_axioms tm_chain_gate_count
-- ⚑ THE MEASUREMENT.
#assert_axioms tmMaxScaleRow_total_is_max_voting_power
#assert_axioms tmMaxScaleRow_signed_is_minimal_supermajority
#assert_axioms minimal_supermajority_is_minimal
#assert_axioms tmLcAir_accepts_at_max_total_voting_power
#assert_axioms tmLcAir_refuses_exactly_two_thirds_at_max_voting_power
#assert_axioms tmLcAir_refuses_the_empty_validator_set
-- ⚑⚑ THE REFUTATION of the "strict subsumes the floor" claim: `total = 0, signed = 1` is an
-- ACCEPTING fill for the only tally gate this descriptor has.
#assert_axioms tm_strict_threshold_does_not_subsume_an_emptiness_floor
#assert_axioms tm_decision_accepts_a_zero_power_validator_set

#print axioms tmLcAir_complete
#print axioms tmLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientTendermintAir
