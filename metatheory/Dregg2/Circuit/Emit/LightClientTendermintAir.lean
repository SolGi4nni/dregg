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

`PI[0] = TRUSTED_NEXT_VALS_ROOT` — the TRUSTED `next_validators_hash` (the WS-checkpoint anchor the
                                   EPOCH_OK carrier is a verify against). The trust root the proof is
                                   relative to.
`PI[1] = COMMITTED_APP_HASH`     — the claimed committed app_hash / state root A (what ICS-23
                                   membership later opens against).
`PI[2] = CHAIN_ID_DOMAIN`        — the chain-id + epoch/height domain the proof speaks for.

These ride as published witness columns pinned to the public inputs (`.piBinding`), so a verifier
sees WHICH trust root and WHICH app-hash the proof is about. NOT-YET-CLOSED (named residual): in this
carrier slice the anchors are published but not yet arithmetically bound to the carrier bits (that
binding IS the in-AIR-crypto iteration — `EPOCH_OK` derived from `TRUSTED_NEXT_VALS_ROOT`, the app
hash opened against `COMMITTED_APP_HASH`). So `airAccepts` (the LOGIC refinement) is stated over the
eleven projections; the anchor pins are the addressing layer around it.

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
| threshold slack definition                  | (bridges `2·totalPow < 3·signedPow`)       | `.gate (TDIFF − 3·SIGNED_POW + 2·TOTAL_POW+1)`|
| strict >2/3 (slack non-negative)            | `decide (2·totalPow < 3·signedPow)`        | `.lookup ⟨range, [TDIFF]⟩` (`[0,2^TM_BITS)`)  |
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
| claimed committed app-hash is public       | (addressing)                               | `.piBinding first COMMITTED_APP_HASH 1`       |
| chain-id / epoch domain is public          | (addressing)                               | `.piBinding first CHAIN_ID_DOMAIN 2`          |

The four range lookups are the LOAD-BEARING teeth: each slack `∈ [0, 2^TM_BITS)` iff its inequality
holds with no field-wrap escape. The threshold slack is the exact strict-`>2/3` boundary — a
sub-quorum (`signedPow = 2, totalPow = 3`) gives `TDIFF = −1`, far outside the interval — UNSAT.

## The mod-p ↔ ℤ reading (the shared field-soundness residual)

`airAccepts` reads the emitted gate bodies as ℤ equalities and the range lookups as ℤ intervals (the
strong reading, exactly as `LightClientEthAir.airAccepts` does). The deployed denotation is mod-`p`
(`VmConstraint.holdsVm`) and a `2^TM_BITS`-wide range is realized by limb decomposition, not a
literal table; bridging the two needs full-wire range decomposition, the same field-soundness
residual every Emit descriptor carries. Not re-litigated here. `TM_BITS = 64` fits real Tendermint
u64 timestamps and (`MaxTotalVotingPower ≈ 2^60`) the aggregate-power slacks, so completeness is
real, not toy.

## Axiom hygiene

Definitional descriptor + non-vacuous per-gate `iff` lemmas (`omega`) + the load-bearing
`tmLcAir_sound` / `tmLcAir_no_forgery` refinement to `tmVerifyDecision` / `TmForeignValid`.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
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
them crypto carriers), plus the four range slacks. Columns 18..20 are the published PUBLIC anchors. -/

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
/-- Total voting power of the validator set (`totalPower`). Witness. -/
def TOTAL_POW : Nat := 9
/-- Ed25519-VERIFIED signed power (`signedPower`) — the summed stake of validators whose commit
signature verified. Its Ed25519 provenance is the `ED_OK` carrier. Witness. -/
def SIGNED_POW : Nat := 10
/-- The strict `>2/3` threshold SLACK `3·SIGNED_POW − 2·TOTAL_POW − 1`; the range tooth forces it
into `[0, 2^TM_BITS)`, i.e. `2·totalPow < 3·signedPow`. -/
def TDIFF : Nat := 11
/-- Monotonic-advance slack `TIME − HEADER_TIME − 1`; range-forced `≥ 0`, i.e. `headerTime < time`. -/
def TW_MONO : Nat := 12
/-- Not-from-the-future slack `NOW + CLOCK_DRIFT − TIME`; range-forced `≥ 0`, i.e.
`time ≤ now + clockDrift`. -/
def TW_DRIFT : Nat := 13
/-- Trusting-period slack `HEADER_TIME + TRUSTING_PERIOD − NOW − 1`; range-forced `≥ 0`, i.e.
`now < headerTime + trustingPeriod`. -/
def TW_TRUST : Nat := 14
/-- **CARRIER** — the Ed25519 batch-verify RESULT (attests `SIGNED_POW` is the genuine verified
stake); forced `= 1`. NAMED verified-FFI carrier, not re-derived in-AIR (this slice). Witness. -/
def ED_OK : Nat := 15
/-- **CARRIER** — the SHA-256 header self-binding compare RESULT (`hash(enc valset) =
header.validatorsHash`); forced `= 1`. NAMED carrier. Witness. -/
def VSET_OK : Nat := 16
/-- **CARRIER** — the SHA-256 next-validators epoch-binding compare RESULT (`hash(enc valset) =
ts.nextValidatorsHash`); forced `= 1`. NAMED carrier. Witness. -/
def EPOCH_OK : Nat := 17

/-- **PUBLIC ANCHOR** — the TRUSTED `next_validators_hash` (the WS-checkpoint trust anchor). PI-bound. -/
def TRUSTED_NEXT_VALS_ROOT : Nat := 18
/-- **PUBLIC ANCHOR** — the claimed committed app_hash / state root A. PI-bound. -/
def COMMITTED_APP_HASH : Nat := 19
/-- **PUBLIC ANCHOR** — the chain-id + epoch/height domain. PI-bound. -/
def CHAIN_ID_DOMAIN : Nat := 20

/-- Total main-trace width: 18 logic columns + 3 published anchors. -/
def TM_LC_WIDTH : Nat := 21

/-- PI slot 0: the trusted next-validators root. -/
def PI_TRUSTED_NEXT_VALS_ROOT : Nat := 0
/-- PI slot 1: the claimed committed app-hash. -/
def PI_COMMITTED_APP_HASH : Nat := 1
/-- PI slot 2: the chain-id / epoch domain. -/
def PI_CHAIN_ID_DOMAIN : Nat := 2
/-- Number of public inputs. -/
def PI_COUNT : Nat := 3

/-- The range-slack width. `TM_BITS = 64` fits real Tendermint u64 timestamps and (with
`MaxTotalVotingPower ≈ 2^60`) the aggregate-power slack `3·signedPow − 2·totalPow − 1 < 2^62`, so
completeness holds for real chain data; the interval's floor `≥ 0` is the load-bearing tooth. -/
def TM_BITS : Nat := 64

/-! ## §2 — the emitted gate bodies (the descriptor's OWN constraint polynomials). -/

/-- `CHAIN_ID − TS_CHAIN_ID` — zero iff the header's chain-id matches the trusted chain-id. -/
def chainMatchBody : EmittedExpr :=
  .add (.var CHAIN_ID) (.mul (.const (-1)) (.var TS_CHAIN_ID))
/-- `HEIGHT − TS_HEIGHT − 1` — zero iff the header is the adjacent next height. -/
def heightAdjBody : EmittedExpr :=
  .add (.add (.var HEIGHT) (.mul (.const (-1)) (.var TS_HEIGHT))) (.const (-1))
/-- `TDIFF − 3·SIGNED_POW + 2·TOTAL_POW + 1` — zero iff `TDIFF = 3·SIGNED_POW − 2·TOTAL_POW − 1`
(the strict `>2/3` threshold slack identity). -/
def tdiffBody : EmittedExpr :=
  .add (.add (.add (.var TDIFF) (.mul (.const (-3)) (.var SIGNED_POW)))
    (.mul (.const 2) (.var TOTAL_POW))) (.const 1)
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
def tdiffGate : VmConstraint2 := .base (.gate tdiffBody)
/-- The strict-`>2/3` range tooth: `TDIFF ∈ [0, 2^TM_BITS)` — the exactly-2/3 boundary rejects. -/
def tdiffRange : VmConstraint2 := .lookup ⟨TableId.range, [.var TDIFF]⟩
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
/-- Published-anchor pin: the claimed committed app-hash is `PI[1]`. -/
def appHashPin : VmConstraint2 :=
  .base (.piBinding VmRow.first COMMITTED_APP_HASH PI_COMMITTED_APP_HASH)
/-- Published-anchor pin: the chain-id / epoch domain is `PI[2]`. -/
def chainDomainPin : VmConstraint2 :=
  .base (.piBinding VmRow.first CHAIN_ID_DOMAIN PI_CHAIN_ID_DOMAIN)

/-- **`tmLcVerifyDesc`** — the Cosmos/Tendermint light-client verify-decision as an emitted IR-v2
AIR. PIs `[trusted_next_vals_root, committed_app_hash, chain_id_domain]`; the eleven verify-logic
projections + four range slacks as hidden witnesses, the three crypto results as carrier bits. The
range table (`TID_range`) carries the strict-threshold and time-window teeth. -/
def tmLcVerifyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-tm-lightclient-verify::v1"
  , traceWidth  := TM_LC_WIDTH
  , piCount     := PI_COUNT
  , tables      := [rangeTableDef TM_BITS]
  , constraints := [chainMatchGate, heightAdjGate, tdiffGate, tdiffRange, twMonoGate, twMonoRange,
                    twDriftGate, twDriftRange, twTrustGate, twTrustRange, edGate, vsetGate, epochGate,
                    nextValsRootPin, appHashPin, chainDomainPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — non-vacuous per-gate lemmas (the emitted bodies bite, both directions). -/

/-- `chainMatchBody = 0 ↔ CHAIN_ID = TS_CHAIN_ID`. -/
theorem chainMatch_body_zero_iff (a : Assignment) :
    chainMatchBody.eval a = 0 ↔ a CHAIN_ID = a TS_CHAIN_ID := by
  simp only [chainMatchBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `heightAdjBody = 0 ↔ HEIGHT = TS_HEIGHT + 1`. -/
theorem heightAdj_body_zero_iff (a : Assignment) :
    heightAdjBody.eval a = 0 ↔ a HEIGHT = a TS_HEIGHT + 1 := by
  simp only [heightAdjBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `tdiffBody = 0 ↔ TDIFF = 3·SIGNED_POW − 2·TOTAL_POW − 1`. -/
theorem tdiff_body_zero_iff (a : Assignment) :
    tdiffBody.eval a = 0 ↔ a TDIFF = 3 * a SIGNED_POW - 2 * a TOTAL_POW - 1 := by
  simp only [tdiffBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
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
  ∧ tdiffBody.eval a = 0
  ∧ (0 ≤ a TDIFF ∧ a TDIFF < (2 : ℤ) ^ TM_BITS)
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
    (hTotalPow : a TOTAL_POW = (totalPow : ℤ)) (hSignedPow : a SIGNED_POW = (signedPow : ℤ))
    (hEpoch : a EPOCH_OK = (if epochBindOk then (1 : ℤ) else 0))
    (hVset : a VSET_OK = (if selfBindOk then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    tmVerifyDecision chainId tsChainId height tsHeight headerTime time now clockDrift trustingPeriod
      epochBindOk selfBindOk totalPow signedPow = true := by
  obtain ⟨hchainB, hheightB, htdiffB, ⟨htdiff0, _⟩, htwmB, ⟨htwm0, _⟩, htwdB, ⟨htwd0, _⟩,
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
  -- strict >2/3 threshold: 2·totalPow < 3·signedPow.
  have hthresh : 2 * totalPow < 3 * signedPow := by
    have hid := (tdiff_body_zero_iff a).mp htdiffB
    have h0 : (0 : ℤ) ≤ a TDIFF := htdiff0
    rw [hid, hSignedPow, hTotalPow] at h0
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
    (hTotalPow : a TOTAL_POW = (totalPower u.validators : ℤ))
    (hSignedPow : a SIGNED_POW = (signedPower L (sb u.header) u.validators u.commit : ℤ))
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

/-- **Completeness (the honest prover CAN fill the slacks).** For any decision-accepting projections,
an honest row that fills the four slacks with the true differences and the carrier bits with the true
results is accepted by the emitted logic — PROVIDED the honest slacks fit the range interval (the
`< 2^TM_BITS` conditions; real Tendermint u64 times + `MaxTotalVotingPower ≈ 2^60` satisfy them).
This is the non-vacuity partner of soundness: the AIR is satisfiable EXACTLY on accepted updates, not
vacuously empty. -/
theorem tmLcAir_complete (a : Assignment)
    (chainId tsChainId height tsHeight headerTime time now clockDrift trustingPeriod : Nat)
    (epochBindOk selfBindOk : Bool) (totalPow signedPow : Nat)
    (hChainId : a CHAIN_ID = (chainId : ℤ)) (hTsChainId : a TS_CHAIN_ID = (tsChainId : ℤ))
    (hHeight : a HEIGHT = (height : ℤ)) (hTsHeight : a TS_HEIGHT = (tsHeight : ℤ))
    (hHeaderTime : a HEADER_TIME = (headerTime : ℤ)) (hTime : a TIME = (time : ℤ))
    (hNow : a NOW = (now : ℤ)) (hClockDrift : a CLOCK_DRIFT = (clockDrift : ℤ))
    (hTrustingPeriod : a TRUSTING_PERIOD = (trustingPeriod : ℤ))
    (hTotalPow : a TOTAL_POW = (totalPow : ℤ)) (hSignedPow : a SIGNED_POW = (signedPow : ℤ))
    (hEpoch : a EPOCH_OK = (if epochBindOk then (1 : ℤ) else 0))
    (hVset : a VSET_OK = (if selfBindOk then (1 : ℤ) else 0))
    (hEd : a ED_OK = 1)
    (hTdiff : a TDIFF = 3 * (signedPow : ℤ) - 2 * (totalPow : ℤ) - 1)
    (hTwMono : a TW_MONO = (time : ℤ) - (headerTime : ℤ) - 1)
    (hTwDrift : a TW_DRIFT = (now : ℤ) + (clockDrift : ℤ) - (time : ℤ))
    (hTwTrust : a TW_TRUST = (headerTime : ℤ) + (trustingPeriod : ℤ) - (now : ℤ) - 1)
    (hTdiffLt : 3 * (signedPow : ℤ) - 2 * (totalPow : ℤ) - 1 < (2 : ℤ) ^ TM_BITS)
    (hTwMonoLt : (time : ℤ) - (headerTime : ℤ) - 1 < (2 : ℤ) ^ TM_BITS)
    (hTwDriftLt : (now : ℤ) + (clockDrift : ℤ) - (time : ℤ) < (2 : ℤ) ^ TM_BITS)
    (hTwTrustLt : (headerTime : ℤ) + (trustingPeriod : ℤ) - (now : ℤ) - 1 < (2 : ℤ) ^ TM_BITS)
    (hdec : tmVerifyDecision chainId tsChainId height tsHeight headerTime time now clockDrift
      trustingPeriod epochBindOk selfBindOk totalPow signedPow = true) :
    airAccepts a := by
  simp only [tmVerifyDecision, Bool.and_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨⟨⟨⟨⟨⟨hchainP, hheightP⟩, htmono⟩, htdrift⟩, httrust⟩, hepochOk⟩, hvsetOk⟩, hthresh⟩ := hdec
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [chainMatch_body_zero_iff, hChainId, hTsChainId]; exact_mod_cast hchainP
  · rw [heightAdj_body_zero_iff, hHeight, hTsHeight]; exact_mod_cast hheightP
  · rw [tdiff_body_zero_iff, hTdiff, hSignedPow, hTotalPow]
  · rw [hTdiff]
    have : 2 * (totalPow : ℤ) < 3 * (signedPow : ℤ) := by exact_mod_cast hthresh
    linarith
  · rw [hTdiff]; exact hTdiffLt
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

/-! ## §6 — the emitted wire JSON (captured for the byte-pinned golden on first build) + shape pins. -/

-- The Rust decoder ingests THIS string (`parse_vm_descriptor2`); byte-pinned golden (a drift on
-- either side breaks this `#guard`). Captured from the hbox build's `emitVmJson2` emission.
#guard emitVmJson2 tmLcVerifyDesc ==
  "{\"name\":\"dregg-tm-lightclient-verify::v1\",\"ir\":2,\"trace_width\":21,\"public_input_count\":3,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":64}],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":11}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":12}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}}},\"r\":{\"t\":\"var\",\"v\":5}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":13}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":14}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":18,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":20,\"pi_index\":2}],\"hash_sites\":[],\"ranges\":[]}"

-- Shape pins (robust; a layout drift moves these).
#guard tmLcVerifyDesc.traceWidth == TM_LC_WIDTH
#guard tmLcVerifyDesc.piCount == PI_COUNT
#guard tmLcVerifyDesc.constraints.length == 16
#guard tmLcVerifyDesc.tables.length == 1
-- The three crypto carriers are real trace columns, and none is PI-bound (the results ride hidden).
#guard ED_OK < TM_LC_WIDTH
#guard VSET_OK < TM_LC_WIDTH
#guard EPOCH_OK < TM_LC_WIDTH

/-! ## §7 — NON-VACUITY: the emitted teeth DISCRIMINATE (the strict >2/3 boundary, in-AIR). -/

-- Chain-id: a matching pair accepts; a mismatch is refused (cross-chain replay fail-closure).
#guard decide (chainMatchBody.eval (fun i => if i = CHAIN_ID then 5 else if i = TS_CHAIN_ID then 5 else 0) = 0)
#guard decide (¬ (chainMatchBody.eval (fun i => if i = CHAIN_ID then 6 else if i = TS_CHAIN_ID then 5 else 0) = 0))
-- Adjacent height: h = th+1 accepts; a non-adjacent height is refused.
#guard decide (heightAdjBody.eval (fun i => if i = HEIGHT then 11 else if i = TS_HEIGHT then 10 else 0) = 0)
#guard decide (¬ (heightAdjBody.eval (fun i => if i = HEIGHT then 12 else if i = TS_HEIGHT then 10 else 0) = 0))
-- Threshold-slack identity: signedPow=3,totalPow=3 ⇒ TDIFF=2 vanishes; a mismatched TDIFF is refused.
#guard decide (tdiffBody.eval (fun i => if i = TDIFF then 2 else if i = SIGNED_POW then 3 else if i = TOTAL_POW then 3 else 0) = 0)
#guard decide (¬ (tdiffBody.eval (fun i => if i = TDIFF then 1 else if i = SIGNED_POW then 3 else if i = TOTAL_POW then 3 else 0) = 0))
-- THE STRICT >2/3 BOUNDARY, in-AIR: just-over (signedPow=3,totalPow=3) slack 3·3−2·3−1 = 2 is in
-- range; exactly-2/3 (signedPow=2,totalPow=3) slack 3·2−2·3−1 = −1 is NOT — the accept/reject tooth
-- (Tendermint's strict threshold: the exactly-2/3 sub-quorum is REJECTED).
example : ([2] : List ℤ) ∈ rangeRows TM_BITS := by rw [range_row_mem_iff]; norm_num [TM_BITS]
example : ¬ (([-1] : List ℤ) ∈ rangeRows TM_BITS) := by rw [range_row_mem_iff]; norm_num
-- The exactly-2/3 slack identity DOES fill to −1 (so the reject is the range tooth, not a gate gap).
#guard decide (tdiffBody.eval (fun i => if i = TDIFF then (-1) else if i = SIGNED_POW then 2 else if i = TOTAL_POW then 3 else 0) = 0)
-- Time window: monotonic advance (time 55 > headerTime 50 ⇒ slack 4 in range; time 45 ⇒ slack −6 out).
#guard decide (twMonoBody.eval (fun i => if i = TW_MONO then 4 else if i = TIME then 55 else if i = HEADER_TIME then 50 else 0) = 0)
example : ([4] : List ℤ) ∈ rangeRows TM_BITS := by rw [range_row_mem_iff]; norm_num [TM_BITS]
example : ¬ (([-6] : List ℤ) ∈ rangeRows TM_BITS) := by rw [range_row_mem_iff]; norm_num
-- Drift bound (time 55 ≤ now 60 + drift 5 ⇒ slack 10) and trusting period (now 60 < ht 50 + tp 100
-- ⇒ slack 89) both fill their honest non-negative slacks.
#guard decide (twDriftBody.eval (fun i => if i = TW_DRIFT then 10 else if i = NOW then 60 else if i = CLOCK_DRIFT then 5 else if i = TIME then 55 else 0) = 0)
#guard decide (twTrustBody.eval (fun i => if i = TW_TRUST then 89 else if i = HEADER_TIME then 50 else if i = TRUSTING_PERIOD then 100 else if i = NOW then 60 else 0) = 0)
-- Carriers: a set bit accepts; a cleared (forged) bit is refused.
#guard decide (edBody.eval (fun i => if i = ED_OK then 1 else 0) = 0)
#guard decide (¬ (edBody.eval (fun _ => 0) = 0))
#guard decide (vsetBody.eval (fun i => if i = VSET_OK then 1 else 0) = 0)
#guard decide (¬ (vsetBody.eval (fun _ => 0) = 0))
#guard decide (epochBody.eval (fun i => if i = EPOCH_OK then 1 else 0) = 0)
#guard decide (¬ (epochBody.eval (fun _ => 0) = 0))

/-! ## §8 — axiom hygiene. -/

#assert_axioms chainMatch_body_zero_iff
#assert_axioms tdiff_body_zero_iff
#assert_axioms twTrust_body_zero_iff
#assert_axioms tmLcAir_sound
#assert_axioms tmLcAir_no_forgery

#print axioms tmLcAir_complete
#print axioms tmLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientTendermintAir
