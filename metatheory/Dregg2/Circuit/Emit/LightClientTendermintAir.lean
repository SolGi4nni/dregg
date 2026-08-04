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
| strict >2/3, LIMBED (see below)             | `decide (2·totalPow < 3·signedPow)`        | 5 GENERATED chain gates + 13 per-limb lookups |
| ⚑ `signedPow ≤ totalPow`  (2026-08-03)      | **NONE — the decision does not require it**| 5 GENERATED chain gates + 9 per-limb lookups  |
| ⚑ `totalPow ≥ 1`  (2026-08-03)              | **NONE — the decision does not require it**| 5 GENERATED chain gates + 9 per-limb lookups  |
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

## ⚑⚑ THE THIRD REPAIR, 2026-08-03 — A RELATION **NO GATE FORCED**, AND A FLOOR THAT WAS NOT THERE

The two repairs below made the tally SOUND (a wrap-free width) and REPRESENTABLE (a limb vector).
Neither made it RELATED. Read the leg list as it stood: ONE comparison chain, `3·signedPow −
2·totalPow − 1 ≥ 0`. Two consequences, both live on the deployed descriptor:

  1. **`signedPow ≤ totalPow` was forced by NOTHING.** The two tallies were independent witnessed
     limb vectors carrying only their own 16-bit lookups, and the quorum tooth gets *easier* as
     `signedPow` grows. A row claiming a signed voting power ABOVE the total satisfied every emitted
     constraint — the Tendermint shape of the ETH client's `PC = 1023` against a 512-key committee
     (`dfa434d46`). CLOSED by a second `LimbTally` chain at `α = 1, β = 1, γ = 0`.
  2. **There was NO EMPTINESS FLOOR, and a theorem's NAME said otherwise.**
     `tmLcAir_refuses_the_empty_validator_set` took `totalPow = 0` **and** `signedPow = 0`, while
     `totalPow = 0, signedPow = 1` fills the quorum difference to `2` — an honest, in-range,
     ACCEPTING row. CLOSED by a third chain at `α = 1, β = 0, γ = 1`, and the theorem now states
     what its name says (one hypothesis, and the refusal comes from the floor).

Trace width **43 → 61**; constraints **44 → 72**; seventeen tally lookups → **thirty-five**. The two
new chains are INDEPENDENT in the sense that matters — their own difference limbs, their own carries,
disjoint from each other and from the quorum's (`tm_the_three_slacks_are_disjoint`) — so
`tm_three_teeth_are_independent` can exhibit a `(total, signed)` pair for each one where it is the
ONLY tooth that fires. And they cannot refuse an honest prover: `signedPower_le_totalPower` is a
theorem over the MODEL (verified stake is a sub-sum of total stake), not a check on a chosen row.

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

Columns 0..14 are the nine scalar VERIFY-LOGIC projections `tmVerifyDecision` composes over, the
three TIME slacks and the three crypto carriers. Columns 15..49 are the TALLY BLOCK: the two `u64`
operands as four 16-bit limbs each, then THREE comparison chains of five difference limbs + four
offset carries — quorum (23..31), `signed ≤ total` (32..40), emptiness floor (41..49). Columns
50..60 are the published PUBLIC anchors: `TRUSTED_NEXT_VALS_ROOT` (50), the NINE app-hash limbs
`COMMITTED_APP_HASH 0..8` (cols 51..59 — the full 256-bit app-hash, radix-`2^31`, MSB-first), and
`CHAIN_ID_DOMAIN` (60). -/

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

/-! ### ⚑⚑ THE TWO CHAINS ADDED 2026-08-03 — a relation NO GATE FORCED, and a floor that was NOT THERE.

Everything above forces `3·signedPow − 2·totalPow − 1 ≥ 0`. Read the leg list: that is the ONLY
comparison this descriptor carried. Two things follow, and both were live:

**(1) `signedPow ≤ totalPow` was forced by NOTHING.** `TOTAL_POW_LIMB` and `SIGNED_POW_LIMB` are two
independent witnessed limb vectors carrying only their own 16-bit lookups; no gate related them
except through the quorum difference, which is satisfied *more easily* the larger `signedPow` gets.
So a trace claiming a signed voting power ABOVE the total — the Tendermint analogue of the ETH
client's `PC = 1023` against a 512-key committee (`dfa434d46`) — satisfied every emitted constraint.
`SLE_LIMB` / `SLE_CARRY` are the second chain, at `α = 1, β = 1, γ = 0`: the difference is
`1·totalPow − 1·signedPow`, and its non-negativity IS `signedPow ≤ totalPow`.

**(2) There was NO EMPTINESS FLOOR**, and a theorem's NAME said otherwise.
`tmLcAir_refuses_the_empty_validator_set` took `hTotal = 0` **and** `hSigned = 0` and concluded a
refusal — but `T = 0, S = 1` gives `3·1 − 2·0 − 1 = 2 ≥ 0`, an accepting fill. The strict threshold
refuses `(0, 0)` and NOTHING ELSE at `total = 0`. `TPOS_LIMB` / `TPOS_CARRY` are the third chain, at
`α = 1, β = 0, γ = 1`: the difference is `totalPow − 1`, and its non-negativity IS `totalPow ≥ 1`,
at EVERY signed power — the same shape Solana (`sol_two_teeth_are_independent`) and Midnight have
carried all along and Tendermint did not.

⚑ **INDEPENDENT means its OWN SLACK.** The floor could have been read off the `signed ≤ total`
chain's difference (with `signed ≤ total` in hand, the strict quorum already forces `total ≥ 1`) —
and that would be two shapes agreeing, not two teeth. It has its own five difference limbs and its
own four carries, so `tm_three_teeth_are_independent` can disarm them ONE AT A TIME and each
survivor still refuses on its own. -/

/-- **Limb `i` of the ORDERING difference `totalPow − signedPow`**, LSB-first. Five limbs (columns
32..36). Its non-negativity is `signedPow ≤ totalPow` — the relation nothing forced. -/
def SLE_LIMB (i : Nat) : Nat := 32 + i
/-- **Offset carry `i` of the ordering chain** (columns 37..40), same `−128` offset. -/
def SLE_CARRY (i : Nat) : Nat := 37 + i
/-- **Limb `i` of the EMPTY-SET FLOOR difference `totalPow − 1`**, LSB-first. Five limbs (columns
41..45). Its non-negativity is `totalPow ≥ 1` — the floor this descriptor did not have. -/
def TPOS_LIMB (i : Nat) : Nat := 41 + i
/-- **Offset carry `i` of the emptiness-floor chain** (columns 46..49), same `−128` offset. -/
def TPOS_CARRY (i : Nat) : Nat := 46 + i

/-- **PUBLIC ANCHOR** — the TRUSTED `next_validators_hash` (the WS-checkpoint trust anchor). PI-bound. -/
def TRUSTED_NEXT_VALS_ROOT : Nat := 50

/-- The number of ~31-bit limbs the FULL 256-bit committed app-hash is exposed as: `⌈256 / 31⌉ = 9`.
Eight 31-bit limbs cover 248 bits; the ninth (most-significant) limb carries the remaining 8 bits.
This is the felt-width close — a SINGLE anchor felt bound only a 31-bit PROJECTION of the 256-bit
app-hash (two roots agreeing in 31 bits both verified); nine limbs bind the WHOLE root. -/
def COMMITTED_APP_HASH_LIMBS : Nat := 9

/-- **PUBLIC ANCHOR (limb `i`)** — the claimed committed app_hash / state root A as its radix-`2^31`,
MOST-SIGNIFICANT-limb-first decomposition. Limb `i` is trace column `51 + i` (cols 51..59); limb `0`
is the MSB (its top carries only 8 bits). PI-bound to slot `1 + i`, so the peer-wrap's radix-`2^31`
MSB-first pack over `PI[1..9]` recomposes the 256-bit app-hash exactly before its 128-bit split. -/
def COMMITTED_APP_HASH (i : Nat) : Nat := 51 + i

/-- **PUBLIC ANCHOR** — the chain-id + epoch/height domain. PI-bound. -/
def CHAIN_ID_DOMAIN : Nat := 51 + COMMITTED_APP_HASH_LIMBS

/-- Total main-trace width: 15 scalar/carrier logic columns + 4 total-power limbs + 4 signed-power
limbs + 5 quorum-difference limbs + 4 quorum carries + 5 ORDERING-difference limbs + 4 ordering
carries + 5 FLOOR-difference limbs + 4 floor carries + 1 next-vals anchor + 9 app-hash limbs + 1
domain anchor = 61.

⚑ It was 29, then 43, and it is now 61. The first +14 was the tally becoming REPRESENTABLE; this +18
is the tally becoming RELATED — `signedPow ≤ totalPow` and `totalPow ≥ 1`, neither of which any gate
forced. Nine columns is what a limbed comparison costs (five difference limbs, four borrow carries),
and there is no cheaper shape: eth closed the same class with ONE column because its count was one
felt, and these are `u64` limb vectors. -/
def TM_LC_WIDTH : Nat := 61

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

/-- ⚑ **The four rungs of the ORDERING chain** — `α = 1` on TOTAL power, `β = 1` on SIGNED power,
`γ = 0`, i.e. the emitted difference is `totalPow − signedPow`.

⚠ The operands are SWAPPED relative to `tdiffRungs`: `aCol` is the total-power limb here and the
signed-power limb there, because `LimbTally.cmp_sound` concludes `γ ≤ α·A − β·B` and the relation
wanted is `0 ≤ total − signed`. The two chains therefore read the SAME eight operand columns in the
opposite order, which is exactly what makes them two teeth on one pair of tallies rather than two
spellings of one. -/
def sleRungs : List LimbTally.Rung :=
  [ ⟨TOTAL_POW_LIMB 0, SIGNED_POW_LIMB 0, SLE_LIMB 0, SLE_CARRY 0⟩
  , ⟨TOTAL_POW_LIMB 1, SIGNED_POW_LIMB 1, SLE_LIMB 1, SLE_CARRY 1⟩
  , ⟨TOTAL_POW_LIMB 2, SIGNED_POW_LIMB 2, SLE_LIMB 2, SLE_CARRY 2⟩
  , ⟨TOTAL_POW_LIMB 3, SIGNED_POW_LIMB 3, SLE_LIMB 3, SLE_CARRY 3⟩ ]

/-- The ordering difference vector's TOP limb — that chain's closure column. -/
def SLE_TOP : Nat := SLE_LIMB 4

/-- ⚑ **The four rungs of the EMPTY-SET FLOOR chain** — `α = 1, β = 0, γ = 1`, i.e. the emitted
difference is `1·totalPow − 0·(…) − 1 = totalPow − 1`.

⚠ **`bCol` POINTS AT THE SAME COLUMN AS `aCol`, AND THAT IS DELIBERATE, NOT A TYPO** — the same
convention `LightClientMidnightAir.tPosRungs` and `LightClientSolanaAir.tposRungs` follow.
`LimbTally.Rung` carries a `bCol` at every rung because the general shape is `α·A − β·B − γ`; this
comparison has no right operand. At `β = 0` the generated term is `.mul (.const 0) (.var bCol)`,
contributing nothing to any gate and nothing to `LimbTally.cmp_sound`'s conclusion, which reads
`γ ≤ α·A − 0·B = α·A` with `B` free. Pointing it at the total-power limb keeps the trace four
columns narrower than a dedicated zero column would. -/
def tposRungs : List LimbTally.Rung :=
  [ ⟨TOTAL_POW_LIMB 0, TOTAL_POW_LIMB 0, TPOS_LIMB 0, TPOS_CARRY 0⟩
  , ⟨TOTAL_POW_LIMB 1, TOTAL_POW_LIMB 1, TPOS_LIMB 1, TPOS_CARRY 1⟩
  , ⟨TOTAL_POW_LIMB 2, TOTAL_POW_LIMB 2, TPOS_LIMB 2, TPOS_CARRY 2⟩
  , ⟨TOTAL_POW_LIMB 3, TOTAL_POW_LIMB 3, TPOS_LIMB 3, TPOS_CARRY 3⟩ ]

/-- The floor difference vector's TOP limb — that chain's closure column. -/
def TPOS_TOP : Nat := TPOS_LIMB 4

/-- The emitted ORDERING gate bodies (`signedPow ≤ totalPow`): five from four rungs. -/
def sleChainBodies : List EmittedExpr :=
  LimbTally.chainBodies TM_LIMB_BITS 1 1 0 LimbTally.TALLY_CARRY_OFF SLE_TOP sleRungs

/-- The emitted EMPTY-SET FLOOR gate bodies (`totalPow ≥ 1`): five from four rungs. -/
def tposChainBodies : List EmittedExpr :=
  LimbTally.chainBodies TM_LIMB_BITS 1 0 1 LimbTally.TALLY_CARRY_OFF TPOS_TOP tposRungs

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

/-- ⚑ The ORDERING difference as a limbed quantity — FIVE limbs, and the load-bearing one for
`signedPow ≤ totalPow`. Its containment is what forces `totalPow − signedPow ≥ 0`. -/
def sleLeg : EffectAirIR.LimbsLeg :=
  { cols := [SLE_LIMB 0, SLE_LIMB 1, SLE_LIMB 2, SLE_LIMB 3, SLE_LIMB 4]
  , bits := TM_LIMB_BITS, table := TID_TALLY_LIMB }

/-- The ordering chain's offset carries. Same job as `tdiffCarryLeg`: the mod-`p` bridge only. -/
def sleCarryLeg : EffectAirIR.LimbsLeg :=
  { cols := [SLE_CARRY 0, SLE_CARRY 1, SLE_CARRY 2, SLE_CARRY 3]
  , bits := TM_CARRY_BITS, table := TID_TALLY_CARRY }

/-- ⚑ The EMPTY-SET FLOOR difference as a limbed quantity — FIVE limbs. Its containment is what
forces `totalPow − 1 ≥ 0`, i.e. a validator set with voting power at all. -/
def tposLeg : EffectAirIR.LimbsLeg :=
  { cols := [TPOS_LIMB 0, TPOS_LIMB 1, TPOS_LIMB 2, TPOS_LIMB 3, TPOS_LIMB 4]
  , bits := TM_LIMB_BITS, table := TID_TALLY_LIMB }

/-- The floor chain's offset carries. -/
def tposCarryLeg : EffectAirIR.LimbsLeg :=
  { cols := [TPOS_CARRY 0, TPOS_CARRY 1, TPOS_CARRY 2, TPOS_CARRY 3]
  , bits := TM_CARRY_BITS, table := TID_TALLY_CARRY }

/-- **THE TALLY TEETH — one range lookup per limb, EMITTED BY THE COMPILER.**

Twenty-three 16-bit lookups (four total-power, four signed-power, five quorum-difference, five
ORDERING-difference, five FLOOR-difference) and twelve 8-bit carry lookups, all of them
`EffectLower.lowerLimbsLeg` output — 35 in all, where the single-felt threshold carried ONE.

⚠ Two of the three chains query NO operand lookups of their own: `sleRungs` reads the same eight
operand columns `tdiffRungs` does (swapped), and `tposRungs` reads the total-power limbs. Those are
already checked once, and checking them twice would be a lookup that cannot go red. -/
def tallyRangeLookups : List VmConstraint2 :=
  EffectLower.lowerLimbsLeg totalPowLeg ++ EffectLower.lowerLimbsLeg signedPowLeg
    ++ EffectLower.lowerLimbsLeg tdiffLeg ++ EffectLower.lowerLimbsLeg tdiffCarryLeg
    ++ EffectLower.lowerLimbsLeg sleLeg ++ EffectLower.lowerLimbsLeg sleCarryLeg
    ++ EffectLower.lowerLimbsLeg tposLeg ++ EffectLower.lowerLimbsLeg tposCarryLeg

/-- The generated threshold gates, wrapped into the target's constraint constructor. GENERATED —
there is no hand-written `VmConstraint2` in this block. -/
def tdiffChainGates : List VmConstraint2 :=
  tdiffChainBodies.map (fun b => .base (.gate b))

/-- The generated ORDERING gates (`signedPow ≤ totalPow`). Also `LimbTally.chainBodies` output. -/
def sleChainGates : List VmConstraint2 :=
  sleChainBodies.map (fun b => .base (.gate b))

/-- The generated EMPTY-SET FLOOR gates (`totalPow ≥ 1`). Also `LimbTally.chainBodies` output. -/
def tposChainGates : List VmConstraint2 :=
  tposChainBodies.map (fun b => .base (.gate b))

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
                   ++ tallyRangeLookups ++ tdiffChainGates ++ sleChainGates ++ tposChainGates
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
  -- ⚑ THE ORDERING TOOTH: `totalPow − signedPow ≥ 0`. Added 2026-08-03; no gate forced it before.
  ∧ LimbTally.BodiesVanish a sleChainBodies
  ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols sleRungs SLE_TOP)
  -- ⚑ THE EMPTINESS FLOOR: `totalPow − 1 ≥ 0`, independent of both chains above (its own slack).
  ∧ LimbTally.BodiesVanish a tposChainBodies
  ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP)
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
  obtain ⟨hchainB, hheightB, htdiffBodies, htdiffLimbs, _hsleBodies, _hsleLimbs,
    _htposBodies, _htposLimbs, htwmB, ⟨htwm0, _⟩, htwdB, ⟨htwd0, _⟩,
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
    (hSleChain : LimbTally.BodiesVanish a sleChainBodies)
    (hSleLimbs : LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols sleRungs SLE_TOP))
    (hTposChain : LimbTally.BodiesVanish a tposChainBodies)
    (hTposLimbs : LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP))
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
  refine ⟨?_, ?_, hTdiffChain, hTdiffLimbs, hSleChain, hSleLimbs, hTposChain, hTposLimbs,
    ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
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

/-! ## §5b — ⚑⚑ THE TWO RELATIONS NO GATE FORCED, NOW FORCED **FROM THE TRACE ALONE**.

Everything in §5 is a refinement: it says what the AIR entails GIVEN a witness relation naming which
columns carry which projections. The two theorems here take NO such hypothesis. They read the
emitted chains and the emitted containments and conclude facts about the tally the trace denotes —
which is the form a bound has to take before it can be called a bound. -/

/-- ⚑ **THE ORDERING CHAIN READS THE QUORUM CHAIN'S OPERANDS, SWAPPED — by `rfl`.**

Without this the two chains could bound two DIFFERENT pairs of quantities while both looking right:
a prover could satisfy `signed ≤ total` on one pair of vectors and `3·signed > 2·total` on another.
`LimbTally.aCols sleRungs` and `LimbTally.bCols tdiffRungs` are literally the same column list (and
likewise the other side), so `totalPow` and `signedPow` each mean ONE thing in this AIR. -/
theorem tm_ordering_reads_the_quorum_operands :
    LimbTally.aCols sleRungs = LimbTally.bCols tdiffRungs
      ∧ LimbTally.bCols sleRungs = LimbTally.aCols tdiffRungs := by decide

/-- …and the FLOOR chain reads the quorum chain's denominator, likewise by `rfl`. -/
theorem tm_floor_reads_the_quorum_denominator :
    LimbTally.aCols tposRungs = LimbTally.bCols tdiffRungs := by decide

/-- ⚑⚑ **`signedPow ≤ totalPow`, FROM THE TRACE, WITH NO HYPOTHESIS ABOUT THE UPDATE.**

This is the relation the descriptor did not have. Before the ordering chain, a row claiming a signed
voting power ABOVE the total satisfied every emitted constraint — the quorum tooth only gets EASIER
as `signedPow` grows, and the two limb vectors were otherwise unrelated. -/
theorem tmLcAir_forces_signed_le_total (a : Assignment) (hacc : airAccepts a) :
    LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs)
      ≤ LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs) := by
  have h := LimbTally.emitted_chain_sound hacc.2.2.2.2.1 hacc.2.2.2.2.2.1
  have hA : LimbTally.aCols sleRungs = LimbTally.bCols tdiffRungs := by decide
  have hB : LimbTally.bCols sleRungs = LimbTally.aCols tdiffRungs := by decide
  rw [hA, hB] at h
  linarith

/-- ⚑⚑ **AND THE VALIDATOR SET IS NON-EMPTY, FROM THE TRACE.** `totalPow ≥ 1` — the floor Solana and
Midnight carried as a separate `TPOS` slack and Tendermint did not.

⚠ It is the FLOOR chain that gives this, not the quorum one: the strict threshold refuses `(0, 0)`
and nothing else at `total = 0` (`tm_strict_threshold_does_not_subsume_an_emptiness_floor` below is
the arithmetic). -/
theorem tmLcAir_forces_nonempty_validator_set (a : Assignment) (hacc : airAccepts a) :
    1 ≤ LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs) := by
  have h := LimbTally.emitted_chain_sound hacc.2.2.2.2.2.2.1 hacc.2.2.2.2.2.2.2.1
  have hA : LimbTally.aCols tposRungs = LimbTally.bCols tdiffRungs := by decide
  rw [hA] at h
  linarith

/-- **The two together, plus the quorum, as one sandwich** — the shape of what the emitted AIR now
forces about a Tendermint tally, with no hypothesis about the update at all:

    1 ≤ totalPow    and    2·totalPow < 3·signedPow    and    signedPow ≤ totalPow

so `signedPow` is pinned into `(2/3·totalPow, totalPow]` on a non-empty set. Before this change the
middle inequality was the ONLY one, and it bounded `signedPow` from BELOW only. -/
theorem tmLcAir_forces_the_tally_sandwich (a : Assignment) (hacc : airAccepts a) :
    1 ≤ LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs)
    ∧ 2 * LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs)
        < 3 * LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs)
    ∧ LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs)
        ≤ LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs) := by
  refine ⟨tmLcAir_forces_nonempty_validator_set a hacc, ?_,
    tmLcAir_forces_signed_le_total a hacc⟩
  have h := LimbTally.emitted_chain_sound hacc.2.2.1 hacc.2.2.2.1
  linarith

/-! ## §5b2 — ⚑ AND THE NEW TEETH CANNOT REFUSE AN HONEST PROVER — proved over the MODEL.

A wrong bound is worse than no bound. The eth lane's rule (`participants_length_le_bits`): do not
show the new leg refusing a chosen forgery and stop — show it ADMITS every real update, over the
model rather than over a row. Tendermint's version is one induction. -/

/-- ⚑ **THE MODEL FACT: VERIFIED STAKE IS A SUB-SUM OF TOTAL STAKE.** `signedPower` walks the
validator list and the positional signature list together, adding `v.power` only where
`L.sigVerify` succeeds and zero otherwise; `totalPower` adds every `v.power`. So the verified stake
is never above the total, on ANY validator list and ANY signature list — including a signature list
of the wrong length, where `signedPower` stops early.

This is what makes the ordering chain a REPAIR rather than a narrowing: it refuses exactly the rows
the model cannot produce. -/
theorem signedPower_le_totalPower (L : CryptoLeaf) (msg : L.Msg) :
    ∀ (vs : List (TmValidator L.PubKey)) (ss : List (Option L.Sig)),
      signedPower L msg vs ss ≤ totalPower vs := by
  intro vs
  induction vs with
  | nil => intro ss; simp [signedPower, totalPower]
  | cons v vs ih =>
      intro ss
      cases ss with
      | nil => simp [signedPower, totalPower]
      | cons s ss =>
          cases s with
          | none => have := ih ss; simp only [signedPower, totalPower]; omega
          | some sig =>
              by_cases hv : L.sigVerify v.pubkey msg sig
              · have := ih ss; simp only [signedPower, totalPower, if_pos hv]; omega
              · have := ih ss; simp only [signedPower, totalPower, if_neg hv]; omega

/-- ⚑ **THE ORDERING SLACK IS FILLABLE ON EVERY REAL UPDATE.** The honest difference
`totalPower u.validators − signedPower …` is non-negative for every `(validators, commit)` pair the
model can present, so the honest prover always has a limb vector to write. The new chain cannot
refuse a genuine Cosmos update. -/
theorem tm_ordering_slack_is_fillable (L : CryptoLeaf) (sb : TmHeader L.Digest → L.Msg)
    (u : TmUpdate L) :
    signedPower L (sb u.header) u.validators u.commit ≤ totalPower u.validators :=
  signedPower_le_totalPower L (sb u.header) u.validators u.commit

/-- ⚑ **AND SO IS THE EMPTINESS FLOOR** — on any update the DECISION accepts. `tmVerifyDecision`
requires `2·total < 3·signed`, and `signedPower ≤ totalPower`; at `total = 0` that forces
`signed = 0` and `0 < 0`, absurd. So `totalPower ≥ 1` holds on every decision-accepted update and
the floor refuses nothing an honest prover would present.

⚠ Note what this does NOT say: it is `signedPower ≤ totalPower` — a MODEL fact, not a decision
conjunct — that makes the floor free. The DECISION alone still accepts `total = 0, signed = 1`
(`tm_decision_accepts_a_zero_power_validator_set`). The emitted AIR is now strictly STRONGER than the
object it refines on this conjunct, which is the sound direction to be stronger in. -/
theorem tm_emptiness_floor_is_fillable (L : CryptoLeaf) (sb : TmHeader L.Digest → L.Msg)
    (u : TmUpdate L)
    (hq : 2 * totalPower u.validators
      < 3 * signedPower L (sb u.header) u.validators u.commit) :
    1 ≤ totalPower u.validators := by
  have hle := tm_ordering_slack_is_fillable L sb u
  omega

/-! ## §5c — ⚑ THREE TEETH, DISARMED ONE AT A TIME.

Midnight's harness disarms its two floors one at a time to show the depth is real; this is the same
bar at three. Each row of the conjunction is a `(total, signed)` pair at which exactly the named
teeth fire, so no tooth is a re-spelling of another. -/

/-- ⚑ **NO TOOTH SUBSUMES ANOTHER — the arithmetic, so "independent" is not a mood.**

  * `(total, signed) = (0, 1)`: the QUORUM passes (`3·1 − 2·0 − 1 = 2 ≥ 0`) and `signed ≤ total`
    FAILS (`0 − 1 = −1`) and the FLOOR fails (`0 − 1 = −1`). ⚑ **This is the row that PROVED before
    this change** — an empty validator set with a claimed unit of signed power.
  * `(total, signed) = (3, 100)`: the QUORUM passes hugely and the ORDERING chain fails alone
    (`3 − 100 < 0`) while the floor passes (`3 − 1 ≥ 0`). ⚑ **This is the `PC = 1023`-of-512 row**,
    Tendermint-shaped: signed weight above the total.
  * `(total, signed) = (3, 1)`: ORDERING passes (`3 − 1 ≥ 0`) and FLOOR passes (`3 − 1 ≥ 0`) and the
    QUORUM alone fails (`3·1 − 2·3 − 1 = −4 < 0`) — an ordinary sub-quorum.

So the three cover strictly more than any two of them, which is the whole content of "depth". -/
theorem tm_three_teeth_are_independent :
    -- (0, 1): quorum SATISFIED, ordering FAILS, floor FAILS.
    ((0 : ℤ) ≤ 3 * 1 - 2 * 0 - 1 ∧ ¬ ((0 : ℤ) ≤ 0 - 1) ∧ ¬ ((0 : ℤ) ≤ 0 - 1))
    -- (3, 100): quorum SATISFIED, ordering FAILS, floor SATISFIED.
    ∧ ((0 : ℤ) ≤ 3 * 100 - 2 * 3 - 1 ∧ ¬ ((0 : ℤ) ≤ 3 - 100) ∧ (0 : ℤ) ≤ 3 - 1)
    -- (3, 1): quorum FAILS, ordering SATISFIED, floor SATISFIED.
    ∧ (¬ ((0 : ℤ) ≤ 3 * 1 - 2 * 3 - 1) ∧ (0 : ℤ) ≤ 3 - 1 ∧ (0 : ℤ) ≤ 3 - 1) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩⟩

/-- ⚑ **THE ORDERING REFUSAL, ON THE EMITTED OBJECT, AT EVERY LIMB WIDTH.** If the true signed power
EXCEEDS the true total, no assignment of ordering-difference limbs and carries satisfies the emitted
chain together with the containments. No premise about `p`, exactly as the quorum refusal carries
none. -/
theorem tm_ordering_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 1 * LimbTally.limbValue bits a (LimbTally.aCols sleRungs)
      - 1 * LimbTally.limbValue bits a (LimbTally.bCols sleRungs) < 0) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 1 1 0 LimbTally.TALLY_CARRY_OFF SLE_TOP sleRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols sleRungs SLE_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-- ⚑ **THE EMPTINESS REFUSAL, likewise.** At `totalPow = 0` the floor difference is `−1`, and no limb
vector of non-negative limbs denotes `−1`. Quantified over EVERY limb width. -/
theorem tm_emptiness_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 1 * LimbTally.limbValue bits a (LimbTally.aCols tposRungs)
      - 0 * LimbTally.limbValue bits a (LimbTally.bCols tposRungs) < 1) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 1 0 1 LimbTally.TALLY_CARRY_OFF TPOS_TOP tposRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols tposRungs TPOS_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-! ### ⚑ §5d — the mod-`p` ↔ `ℤ` bridge at the TWO NEW COEFFICIENT SETS.

`LimbTally.rung_no_alias_at_deployed_constants` is stated at `α = 3, β = 2, γ = 1` — the quorum
chain's constants. The ordering chain runs at `α = 1, β = 1, γ = 0` and the floor at `α = 1, β = 0,
γ = 1`; both are STRICTLY SMALLER images than the quorum's, but "smaller, therefore fine" is an
argument and not a theorem, so each gets one. -/

/-- **NO ALIAS FOR THE ORDERING RUNGS.** At `α = 1, β = 1, γ = 0`, limbs in `[0, 2^16)` and carries
in `[0, 2^8)`, every rung gate's `ℤ` value lies strictly inside `(−p, p)`. -/
theorem tm_sle_rung_no_alias_at_deployed_constants (x y d cin cout : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ TM_LIMB_BITS) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ TM_LIMB_BITS)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ TM_LIMB_BITS)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ TM_CARRY_BITS)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ TM_CARRY_BITS) :
    -Dregg2.Circuit.Emit.EffectLower.P
        < 1 * x - 1 * y - 0 + (cin - LimbTally.TALLY_CARRY_OFF) - d
            - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ TM_LIMB_BITS
      ∧ 1 * x - 1 * y - 0 + (cin - LimbTally.TALLY_CARRY_OFF) - d
            - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ TM_LIMB_BITS
          < Dregg2.Circuit.Emit.EffectLower.P := by
  have h := LimbTally.rung_value_bounds TM_LIMB_BITS TM_CARRY_BITS 1 1 0
    LimbTally.TALLY_CARRY_OFF x y d cin cout (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LimbTally.TALLY_CARRY_OFF]) hx hy hd hcin hcout
  obtain ⟨hlo, hhi⟩ := h
  simp only [TM_LIMB_BITS, TM_CARRY_BITS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_CARRY_BITS,
    LimbTally.TALLY_CARRY_OFF] at hlo hhi ⊢
  norm_num [Dregg2.Circuit.Emit.EffectLower.P] at hlo hhi ⊢
  constructor <;> linarith

/-- **NO ALIAS FOR THE FLOOR RUNGS.** Same, at `α = 1, β = 0, γ = 1`. -/
theorem tm_tpos_rung_no_alias_at_deployed_constants (x y d cin cout : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ TM_LIMB_BITS) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ TM_LIMB_BITS)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ TM_LIMB_BITS)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ TM_CARRY_BITS)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ TM_CARRY_BITS) :
    -Dregg2.Circuit.Emit.EffectLower.P
        < 1 * x - 0 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
            - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ TM_LIMB_BITS
      ∧ 1 * x - 0 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
            - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ TM_LIMB_BITS
          < Dregg2.Circuit.Emit.EffectLower.P := by
  have h := LimbTally.rung_value_bounds TM_LIMB_BITS TM_CARRY_BITS 1 0 1
    LimbTally.TALLY_CARRY_OFF x y d cin cout (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LimbTally.TALLY_CARRY_OFF]) hx hy hd hcin hcout
  obtain ⟨hlo, hhi⟩ := h
  simp only [TM_LIMB_BITS, TM_CARRY_BITS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_CARRY_BITS,
    LimbTally.TALLY_CARRY_OFF] at hlo hhi ⊢
  norm_num [Dregg2.Circuit.Emit.EffectLower.P] at hlo hhi ⊢
  constructor <;> linarith

/-! ## §6 — the emitted wire JSON (byte-pinned golden) + shape pins. -/

-- ⚑ THE BYTE-GOLDEN `#guard` IS RETIRED, not deleted — the same move the ETH lane made
-- (`dfa434d46`). A transcribed 12 KB wire string cannot see a DROPPED leg (it only sees the string
-- it was captured from), it is invisible to `#assert_axioms`, and it is exactly the `#guard`
-- discipline `metatheory/docs/GUARD-DISCIPLINE.md` forbids. What replaces it is stronger: `rfl`
-- pins on the compiler's own emission (`tm_tally_lookups_are_the_compilers_output` below), the
-- structural shape pins, and the checked-in artifact
-- `circuit/descriptors/by-name/dregg-tm-lightclient-verify-v1.json`, which `EmitByName.lean`
-- RE-DERIVES from this very `def` and `scripts/emit_descriptors.py` reconciles both directions.

-- Shape pins (robust; a layout drift moves these).
theorem tm_shape_pins :
    tmLcVerifyDesc.traceWidth = TM_LC_WIDTH
      ∧ tmLcVerifyDesc.piCount = PI_COUNT
      ∧ tmLcVerifyDesc.constraints.length = 72
      ∧ tmLcVerifyDesc.tables.length = 3 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  decide

/-- ⚑ **THE TALLY IS THIRTY-FIVE LOOKUPS, NOT ONE — AND NOT SEVENTEEN.** Twenty-three 16-bit limb
checks plus twelve 8-bit carry checks, where the single-felt threshold carried exactly ONE and the
single-chain limbed threshold carried seventeen. A re-emission that dropped a limb moves this
number; the old shape had no number to move. -/
theorem tm_tally_lookup_count : tallyRangeLookups.length = 35 := by decide

/-- ⚑ **THE LOOKUPS ARE THE COMPILER'S OUTPUT, by `rfl` on the emission** — not a transcription that
happens to agree. `EffectLower.lowerLimbsLeg` is the ONLY path from a `LimbsLeg` to the range teeth
in this descriptor, so a leg that lost a column loses its lookups here rather than silently keeping
a hand-written one. -/
theorem tm_tally_lookups_are_the_compilers_output :
    tallyRangeLookups
      = EffectLower.lowerLimbsLeg totalPowLeg ++ EffectLower.lowerLimbsLeg signedPowLeg
        ++ EffectLower.lowerLimbsLeg tdiffLeg ++ EffectLower.lowerLimbsLeg tdiffCarryLeg
        ++ EffectLower.lowerLimbsLeg sleLeg ++ EffectLower.lowerLimbsLeg sleCarryLeg
        ++ EffectLower.lowerLimbsLeg tposLeg ++ EffectLower.lowerLimbsLeg tposCarryLeg := rfl

/-- …and the THREE chains' gate bodies are `LimbTally.chainBodies` output, likewise by `rfl`. There
is no hand-written `VmConstraint2` carrying a comparison in this module. -/
theorem tm_chain_gates_are_generated :
    tdiffChainBodies
        = LimbTally.chainBodies TM_LIMB_BITS 3 2 1 LimbTally.TALLY_CARRY_OFF TDIFF_TOP tdiffRungs
    ∧ sleChainBodies
        = LimbTally.chainBodies TM_LIMB_BITS 1 1 0 LimbTally.TALLY_CARRY_OFF SLE_TOP sleRungs
    ∧ tposChainBodies
        = LimbTally.chainBodies TM_LIMB_BITS 1 0 1 LimbTally.TALLY_CARRY_OFF TPOS_TOP tposRungs :=
  ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE IR'S WIDTH VERDICT IS LOAD-BEARING ON THIS DEPLOYED DESCRIPTOR.** All EIGHT limbed
quantities pass `EffectAirIR.LimbsLeg.mainRailOk`, which REFUSES an empty limb vector and any limb
width above the wrap-free ceiling 29 — the exact class this descriptor shipped in at 64 bits. The
teeth in `tallyRangeLookups` are `EffectLower.lowerLimbsLeg`'s output, so the verdict gates the
emitted object rather than commenting on it. -/
theorem tm_tally_legs_are_expressible :
    totalPowLeg.mainRailOk = true ∧ signedPowLeg.mainRailOk = true
      ∧ tdiffLeg.mainRailOk = true ∧ tdiffCarryLeg.mainRailOk = true
      ∧ sleLeg.mainRailOk = true ∧ sleCarryLeg.mainRailOk = true
      ∧ tposLeg.mainRailOk = true ∧ tposCarryLeg.mainRailOk = true := by decide

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

/-- …and each chain is FIVE generated gates for four rungs — one per rung plus the closure gate that
forces the final carry into the top difference limb. Without the closure gate the prover could dump
a residue into a carry nothing reads, and the recomposition would be off by `2^64`.

⚑ THREE chains now: quorum, ordering (`signed ≤ total`), emptiness floor (`total ≥ 1`). Fifteen
generated gates where the single-felt threshold carried one hand-written body. -/
theorem tm_chain_gate_count :
    tdiffChainGates.length = 5 ∧ sleChainGates.length = 5 ∧ tposChainGates.length = 5 := by decide

/-- The three crypto carriers are real trace columns and none is PI-bound (the results ride hidden). -/
theorem tm_carriers_are_hidden_columns :
    ED_OK < TM_LC_WIDTH ∧ VSET_OK < TM_LC_WIDTH ∧ EPOCH_OK < TM_LC_WIDTH := by decide

/-- The tally block occupies columns 15..49 contiguously, below the published anchors: four
total-power limbs, four signed-power limbs, and then THREE chains of five difference limbs + four
carries each — quorum (23..31), ordering (32..40), emptiness floor (41..49).

⚑ **THE THREE DIFFERENCE BLOCKS ARE DISJOINT, and that is what `independent` means here.** A floor
that read the ordering chain's slack would be two spellings of one tooth; these overlap in NOTHING
but the operands they are comparisons OF. -/
theorem tm_tally_block_layout :
    TOTAL_POW_LIMB 0 = 15 ∧ TOTAL_POW_LIMB 3 = 18
      ∧ SIGNED_POW_LIMB 0 = 19 ∧ SIGNED_POW_LIMB 3 = 22
      ∧ TDIFF_LIMB 0 = 23 ∧ TDIFF_TOP = 27
      ∧ TDIFF_CARRY 0 = 28 ∧ TDIFF_CARRY 3 = 31
      ∧ SLE_LIMB 0 = 32 ∧ SLE_TOP = 36
      ∧ SLE_CARRY 0 = 37 ∧ SLE_CARRY 3 = 40
      ∧ TPOS_LIMB 0 = 41 ∧ TPOS_TOP = 45
      ∧ TPOS_CARRY 0 = 46 ∧ TPOS_CARRY 3 = 49
      ∧ TPOS_CARRY 3 < TRUSTED_NEXT_VALS_ROOT := by decide

/-- ⚑ **THE THREE DIFFERENCE VECTORS SHARE NO COLUMN** — stated as a `decide`able fact about the
emitted column lists rather than read off the arithmetic above, because that is the property
`tm_three_teeth_are_independent` is arithmetic ABOUT. -/
theorem tm_the_three_slacks_are_disjoint :
    (LimbTally.diffCols tdiffRungs TDIFF_TOP).all
        (fun c => !(LimbTally.diffCols sleRungs SLE_TOP).contains c
                  && !(LimbTally.diffCols tposRungs TPOS_TOP).contains c) = true
    ∧ (LimbTally.diffCols sleRungs SLE_TOP).all
        (fun c => !(LimbTally.diffCols tposRungs TPOS_TOP).contains c) = true
    ∧ (LimbTally.carryCols tdiffRungs).all
        (fun c => !(LimbTally.carryCols sleRungs).contains c
                  && !(LimbTally.carryCols tposRungs).contains c) = true
    ∧ (LimbTally.carryCols sleRungs).all
        (fun c => !(LimbTally.carryCols tposRungs).contains c) = true := by decide

/-- The widened committed-app-hash anchor is unchanged by the tally work, only shifted: nine limbs,
contiguous cols 51..59 → PI 1..9, MSB-first, `⌈256/31⌉ = 9` covering the full 256 bits. -/
theorem tm_app_hash_anchor_layout :
    COMMITTED_APP_HASH_LIMBS = 9 ∧ appHashPins.length = COMMITTED_APP_HASH_LIMBS
      ∧ COMMITTED_APP_HASH 0 = 51 ∧ COMMITTED_APP_HASH 8 = 59
      ∧ CHAIN_ID_DOMAIN = 60 ∧ PI_CHAIN_ID_DOMAIN = 10
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
  , 21844, 21845, 21845, 1365, 0    -- SLE   limbs = T − S = 384307168202282324
  , 128, 128, 128, 128              -- SLE   carries, offset
  , 65534, 65535, 65535, 4095, 0    -- TPOS  limbs = T − 1 = 1152921504606846974
  , 128, 128, 128, 128              -- TPOS  carries, offset
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
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, by decide, ⟨by decide, by decide⟩,
    by decide, ⟨by decide, by decide⟩, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    by decide⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- ⚑ …and the row's ORDERING and FLOOR difference vectors denote the right numbers, so the two new
chains are not merely satisfied — they are satisfied BY THE HONEST FILL of a protocol-maximum
validator set. `T − S = 384307168202282324` and `T − 1 = 1152921504606846974`. -/
theorem tmMaxScaleRow_new_slacks_denote_the_honest_differences :
    LimbTally.limbValue TM_LIMB_BITS tmMaxScaleRow (LimbTally.diffCols sleRungs SLE_TOP)
      = 384307168202282324
    ∧ LimbTally.limbValue TM_LIMB_BITS tmMaxScaleRow (LimbTally.diffCols tposRungs TPOS_TOP)
      = 1152921504606846974 := by decide

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

/-- ⚑⚑ **THE EMPTY VALIDATOR SET IS REFUSED — BY THE FLOOR CHAIN, AND ONLY BY IT.**

⚠ **THIS THEOREM USED TO SAY SOMETHING WEAKER THAN ITS NAME.** Until 2026-08-03 it read
`totalPow = 0 → signedPow = 0 → ¬ (the QUORUM chain accepts)` and carried the docstring *"Tendermint's
strict threshold subsumes the empty-set floor its Solana and Midnight siblings carry as a separate
`TPOS` slack."* That is true at `signedPow = 0` and **FALSE everywhere else on the empty set**: at
`totalPow = 0, signedPow = 1` the quorum difference is `3·1 − 2·0 − 1 = 2 ≥ 0`, an honest, in-range,
ACCEPTING fill. The name claimed a refusal the statement obtained only under an extra hypothesis.

It now says what its name says. ONE hypothesis — `totalPow = 0` — and the refusal comes from the
FLOOR chain, whose difference `0 − 1 = −1` no vector of non-negative limbs can denote, at every
`signedPow` whatsoever. `tm_strict_threshold_does_not_subsume_an_emptiness_floor` keeps the
refutation of the old claim so it cannot be re-asserted. -/
theorem tmLcAir_refuses_the_empty_validator_set (a : Assignment)
    (hTotal : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs) = 0) :
    ¬ (LimbTally.BodiesVanish a tposChainBodies
        ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  have hA : LimbTally.aCols tposRungs = LimbTally.bCols tdiffRungs := by decide
  rw [hA, hTotal]; norm_num

/-- …and the OLD statement is kept as a corollary, under the name that describes it: at
`totalPow = signedPow = 0` the QUORUM chain refuses too, because its difference is `−1`. It is a
narrower fact than the one above and it is no longer the only one. -/
theorem tmLcAir_quorum_also_refuses_the_all_zero_row (a : Assignment)
    (hTotal : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs) = 0)
    (hSigned : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs) = 0) :
    ¬ (LimbTally.BodiesVanish a tdiffChainBodies
        ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tdiffRungs TDIFF_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal, hSigned]; norm_num

/-- ⚑⚑ **AND THE ROW THAT PROVED BEFORE THIS CHANGE IS REFUSED NOW.** `totalPow = 0, signedPow = 1`
— a validator set with NO voting power and a claimed unit of signed power — satisfied every gate this
descriptor had. It is refused twice over: by the FLOOR (`0 − 1 = −1`) and by the ORDERING chain
(`0 − 1 = −1`), each on its own difference limbs. -/
theorem tmLcAir_refuses_zero_total_with_signed_power (a : Assignment)
    (hTotal : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs) = 0)
    (hSigned : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs) = 1) :
    ¬ (LimbTally.BodiesVanish a tposChainBodies
        ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP))
    ∧ ¬ (LimbTally.BodiesVanish a sleChainBodies
        ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols sleRungs SLE_TOP)) := by
  have hA : LimbTally.aCols tposRungs = LimbTally.bCols tdiffRungs := by decide
  have hSa : LimbTally.aCols sleRungs = LimbTally.bCols tdiffRungs := by decide
  have hSb : LimbTally.bCols sleRungs = LimbTally.aCols tdiffRungs := by decide
  refine ⟨LimbTally.emitted_chain_refuses ?_, LimbTally.emitted_chain_refuses ?_⟩
  · rw [hA, hTotal]; norm_num
  · rw [hSa, hSb, hTotal, hSigned]; norm_num

/-- ⚑ **AND A SIGNED WEIGHT ABOVE THE TOTAL IS REFUSED** — the Tendermint shape of the ETH client's
`PC = 1023` against a 512-key committee. At `totalPow = 3, signedPow = 100` the quorum tooth passes
comfortably (`3·100 − 2·3 − 1 = 293 ≥ 0`) and the ordering chain refuses alone. -/
theorem tmLcAir_refuses_signed_above_total (a : Assignment)
    (hTotal : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.bCols tdiffRungs) = 3)
    (hSigned : LimbTally.limbValue TM_LIMB_BITS a (LimbTally.aCols tdiffRungs) = 100) :
    ¬ (LimbTally.BodiesVanish a sleChainBodies
        ∧ LimbTally.LimbsInRange TM_LIMB_BITS a (LimbTally.diffCols sleRungs SLE_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  have hSa : LimbTally.aCols sleRungs = LimbTally.bCols tdiffRungs := by decide
  have hSb : LimbTally.bCols sleRungs = LimbTally.aCols tdiffRungs := by decide
  rw [hSa, hSb, hTotal, hSigned]; norm_num

/-- ⚑⚑ **THE CLAIM THAT USED TO SIT ON THAT THEOREM WAS FALSE — REFUTED, then FIXED.**

The docstring on `tmLcAir_refuses_the_empty_validator_set` read *"Tendermint's strict threshold
subsumes the empty-set floor its Solana and Midnight siblings carry as a separate `TPOS` slack."*
That is true at `signedPow = 0` and **FALSE everywhere else on the empty set**: at
`totalPow = 0, signedPow = 1` the strict difference is `3·1 − 2·0 − 1 = 2 ≥ 0`, an honest, in-range,
**ACCEPTING** fill. `cmp_sound`'s conclusion is `γ ≤ α·A − β·B`, which bounds the DIFFERENCE and says
nothing about the denominator being real.

⚑ **THIS THEOREM IS KEPT AFTER THE FIX**, and is now the reason the floor exists rather than a
finding awaiting one. Its content is exactly "a strict quorum refuses `(0,0)` and NOTHING ELSE at
`total = 0`", which is why Solana keeps its `TPOS` floor even with a strict quorum
(`LightClientSolanaAir.sol_two_teeth_are_independent`) and why Tendermint now has one
(`tposChainBodies`, `tmLcAir_forces_nonempty_validator_set`). Delete this and the next reader has no
record of why a second chain is not redundant with the first. -/
theorem tm_strict_threshold_does_not_subsume_an_emptiness_floor :
    -- the exhibited empty-set-with-signed-power point SATISFIES the strict threshold…
    (1 : ℤ) ≤ 3 * 1 - 2 * 0
    -- …while the SAME point fails the positivity floor Solana and Midnight carry separately.
    ∧ ¬ ((1 : ℤ) ≤ 1 * 0 - 0 * 0)
    -- And the only case the strict threshold does catch on the empty set is `signed = 0`.
    ∧ ¬ ((1 : ℤ) ≤ 3 * 0 - 2 * 0) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- ⚑ …and the gap is INHERITED FROM THE DECISION, which is why it survived: `tmVerifyDecision`
accepts an update whose total voting power is ZERO, given the scalar/carrier conjuncts. The threshold
conjunct is the only one that reads the tally, and `2·0 < 3·1` holds.

⚠ **THIS IS STILL TRUE AFTER THE REPAIR, DELIBERATELY.** The emitted AIR is now strictly STRONGER
than the scalar decision it refines on two conjuncts (`signedPow ≤ totalPow`, `totalPow ≥ 1`), which
is the sound direction to be stronger in — exactly as the ETH lane's AIR is stronger than
`syncDecision` on `pc ≤ bitsLen`. `tmLcAir_sound` is UNAFFECTED (it concludes the decision from the
AIR, and the AIR now says more). Closing it at the gate layer as well is named, not done: the same
omission is in `solVerifyDecision` and `midVerifyDecision`. -/
theorem tm_decision_accepts_a_zero_power_validator_set :
    Dregg2.Bridge.LightClientTendermintGate.tmVerifyDecision
      7 7 11 10 5 6 6 1 100 true true 0 1 = true := by decide

/-- …and it accepts a SIGNED POWER ABOVE THE TOTAL, likewise: `2·3 < 3·100`. The decision-layer twin
of the relation the AIR now forces. -/
theorem tm_decision_accepts_signed_above_total :
    Dregg2.Bridge.LightClientTendermintGate.tmVerifyDecision
      7 7 11 10 5 6 6 1 100 true true 3 100 = true := by decide

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
#assert_axioms tmLcAir_quorum_also_refuses_the_all_zero_row
-- ⚑⚑ THE REFUTATION of the "strict subsumes the floor" claim, KEPT after the fix as the reason the
-- floor is not redundant: `total = 0, signed = 1` was an ACCEPTING fill for the only tally gate this
-- descriptor used to have.
#assert_axioms tm_strict_threshold_does_not_subsume_an_emptiness_floor
#assert_axioms tm_decision_accepts_a_zero_power_validator_set
#assert_axioms tm_decision_accepts_signed_above_total
-- ⚑⚑ THE TWO CLOSURES, 2026-08-03: `signedPow ≤ totalPow` and `totalPow ≥ 1`, both FROM THE TRACE
-- with no hypothesis about the update, plus the model facts that make them free for an honest
-- prover and the arithmetic that says no tooth subsumes another.
#assert_axioms tm_ordering_reads_the_quorum_operands
#assert_axioms tm_floor_reads_the_quorum_denominator
#assert_axioms tmLcAir_forces_signed_le_total
#assert_axioms tmLcAir_forces_nonempty_validator_set
#assert_axioms tmLcAir_forces_the_tally_sandwich
#assert_axioms signedPower_le_totalPower
#assert_axioms tm_ordering_slack_is_fillable
#assert_axioms tm_emptiness_floor_is_fillable
#assert_axioms tm_three_teeth_are_independent
#assert_axioms tm_the_three_slacks_are_disjoint
#assert_axioms tm_ordering_refusal_is_field_independent
#assert_axioms tm_emptiness_refusal_is_field_independent
#assert_axioms tm_sle_rung_no_alias_at_deployed_constants
#assert_axioms tm_tpos_rung_no_alias_at_deployed_constants
#assert_axioms tmLcAir_refuses_zero_total_with_signed_power
#assert_axioms tmLcAir_refuses_signed_above_total
#assert_axioms tmMaxScaleRow_new_slacks_denote_the_honest_differences
#assert_axioms tm_tally_lookups_are_the_compilers_output
#assert_axioms tm_chain_gates_are_generated

#print axioms tmLcAir_complete
#print axioms tmLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientTendermintAir
