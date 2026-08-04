/-
# Dregg2.Circuit.Emit.LightClientEthAir — the ETH/Base light-client VERIFY-DECISION, EMITTED AS AN AIR.

## What this file IS (the "STARK-ify the light client" first slice)

`Dregg2.Bridge.LightClientEth` proves `eth_no_forgery` over `verifyFinalizedUpdate`, and
`Dregg2.Bridge.LightClientEthGate` collapses that decision to the eight scalar/boolean projections a
deployed node computes (`ethVerifyDecision`) and `@[export]`s it as `dregg_eth_lc_verify`. That gives
a node a Lean-PROVEN accept/reject — but the verdict is rendered by *running Lean code on the node's
own machine*. A peer (or an on-chain contract) that wants to trust "this dregg node saw Base finalize
beacon state B" must RE-TRUST that node's execution. There is no portable object.

This file emits `ethVerifyDecision` AS A DESCRIPTOR-IR-v2 AIR (`ethLcVerifyDesc`), so a dregg node can
PROVE the verify-decision as a STARK: the proof is a portable artifact any peer verifies without
re-running the node, and (via the gnark FRI-wrap → Groth16, §5 below) an on-chain contract verifies.
That is what makes dregg + Base TRUE PEERS: today Base verifies dregg's STARK while dregg's view of
Base is trusted-Rust; this AIR turns dregg's view of Base into the SAME kind of portable proof.

HOUSE LAW #1: the AIR is LEAN-AUTHORED. ⚑ **AND AS OF 2026-08-03 IT IS COMPILER-AUTHORED**:
`ethLcVerifyDesc` is `EffectLower.lowerAir` applied to `ethHeadAir` (§3), an `EffectAir` source in the
widened vocabulary (`Circuit/EffectAirIR.lean`). There is **no hand-written `VmConstraint2` list in
this file** — the source says `lhs = rhs`, `.lookup` and `.pin`, and the `VmConstraint2`s are the
compiler's business. Rust only ingests the emitted `emitVmJson2` descriptor and runs the generic
multi-table prover over it; it never hand-writes these constraints. The refinement `ethLcAir_sound` /
`ethLcAir_no_forgery` is a machine-checked theorem over the EMITTED object, tying acceptance to
`ethVerifyDecision` and hence to `eth_no_forgery` — so a STARK that satisfies this AIR CARRIES the
no-forgery guarantee, modulo the three named crypto carriers (below).

## ⚑ THE PARTICIPATION COUNT WAS AN UNBOUNDED WITNESS, AND IT PROVED (closed 2026-08-03)

The defect this revision closes was found by RUNNING the deployed prover, not by reading:

> `CL` and `BL` are both forced to 512, but **no gate related `PC` to either**, so a trace with
> `PC = 1023` against a 512-key committee **PROVED and VERIFIED** in release. The only bound was
> INCIDENTAL — the quorum slack's own width capped `PC` at 1023, because `PC = 1024` gives
> `QDIFF = 2048` which the `[0, 2^11)` table refuses.

No stated theorem broke, and that is precisely why it survived: `ethLcAir_sound` /
`ethLcAir_no_forgery` take `hpc : a PC = (pc : ℤ)` as a hypothesis, so `PC` sat inside the named
witness-relation boundary. It was undone work wearing a residual's clothes.

⚠ **AND THE GAP IS ALSO IN THE DECISION IT REFINES.** `LightClientEthGate.syncDecision`
(`LightClientEthGate.lean:90-95`) checks `committeeLen = 512`, `bitsLen = 512`, `0 < pc` and
`2·512 ≤ 3·pc` — it never checks `pc ≤ bitsLen` either. The model never produces such a `pc`
(`ethLcAir_no_forgery` instantiates it at `(participants ts.committee bits).length`, structurally
bounded by the committee), so `eth_no_forgery` is untouched; but a projection the DECISION does not
bound is exactly a projection an AIR author has no prompt to bound.

**The closure is `PC_SLACK` (§1, column 9) and one gate**: `PC_SLACK + PC = BL`, with `PC_SLACK`
range-checked into the SAME `[0, 2^11)` table the quorum tooth already declares. Non-negativity of
the slack IS `PC ≤ BL`, and combined with the quorum tooth the AIR now forces
`342 ≤ PC ≤ BL = 512` from the trace alone, with NO hypothesis about the update
(`ethLcAir_forces_participation_bounded`). No new column width, no new table, no new lookup width.

**On the deployed prover, in release**: `PC = 1023` against a 512-key committee is now refused with
`row 0: range wire 9 value 2013265410 >= 2^11` — the wrapped `512 − 1023 = −511`, i.e. `p − 511` —
and the honest 400-of-512 update still proves and verifies.

⚑ **AND THE BOUND IS PROVED RIGHT, NOT JUST PROVED PRESENT.** A wrong bound here would be worse than
none, so §5b2 proves `participants_length_le_bits` over the MODEL: `participants` is a simultaneous
recursion that consumes one bit per step (`LightClientEth.lean:370-373`), so the participating subset
is never longer than the bitfield and the honest fill `PC_SLACK = bl − pc` is non-negative on EVERY
real `(committee, bitfield)` pair (`eth_participation_slack_is_fillable`). The new leg cannot refuse
an honest prover.

## The crypto boundary: IN-AIR logic vs NAMED verified carriers (the pragmatic first cut)

Light-client verify is not pure logic — it invokes BLS12-381 aggregate-verify and SHA-256 SSZ Merkle
folds. This AIR draws the boundary EXACTLY where `LightClientEthGate` already draws it (the carrier
model): the pure `Nat`/`Bool` VERIFY-LOGIC goes IN-AIR as arithmetic gates; the heavy crypto results
ride as WITNESSED BOOLEAN CARRIERS the logic constrains.

  * IN-AIR (arithmetic gates over the trace):
      - the committee-size / bitfield-length structural checks (`= 512`),
      - the Nomad-floor + 2/3 multiply-form quorum threshold (`2·512 ≤ 3·participants`, i.e. the
        342-accept / 341-reject boundary) as a range-checked non-negative slack `QDIFF = 3·pc − 1024`,
      - ⚑ the participation-vs-bitfield bound `pc ≤ bl` as a range-checked non-negative slack
        `PC_SLACK = BL − PC`,
      - the finality-branch depth admissibility (`6 ∨ 7`) as `(FL−6)·(FL−7) = 0`,
      - the execution-branch depth (`= 4`).
  * NAMED verified CARRIERS (witnessed boolean columns, forced `= 1` for accept — the SAME opaque
    results `ethVerifyDecision` composes over):
      - `BLS_OK`  — `blst` aggregate-verify over the participating subset + signing root,
      - `FIN_OK`  — the SHA-256 finality-branch reconstruction compare (into the attested state root),
      - `EXEC_OK` — the SHA-256 execution-branch reconstruction compare (into the finalized body root).

The residual is HONEST and NAMED: in THIS slice the carriers are asserted, not re-derived in-circuit,
so the STARK proves the QUORUM/BRANCH/BINDING LOGIC is correct GIVEN the crypto results — precisely
the guarantee `ethVerifyDecision` gives, now portable. Putting BLS/SHA in-AIR (or as their own
verified sub-proofs the AIR `ProofBind`s against) is the next iteration; the public-input anchors
below are the hook it attaches to.

## Public inputs (the addressing layer — what the proof is ABOUT)

`PI[0]     = COMMITTEE_ROOT`       — the TRUSTED sync-committee root (the WS-checkpoint anchor the BLS
                             carrier is a verify against). The trust root the proof is relative to.
`PI[1..9]  = FIN_STATE_ROOT[0..8]` — the claimed FINALIZED execution state root B: the FULL 256-bit
                             EVM `state_root` (`eth-lightclient`'s `FinalizedExecution.
                             execution_state_root`, a `[u8;32]`) exposed as its NINE radix-`2^31`,
                             MOST-SIGNIFICANT-limb-first limbs (`⌈256/31⌉ = 9`; the top limb carries
                             the residual 8 bits). FELT-WIDTH CLOSE: the earlier single anchor felt
                             bound only a 31-bit PROJECTION of the root, so two 256-bit roots
                             agreeing in 31 bits both verified — a soundness gap at the peer-wrap
                             boundary. Nine PI-bound limbs bind the WHOLE root; the peer-wrap's
                             radix-`2^31` MSB-first pack over `PI[1..9]` recomposes it before its
                             128-bit split.
`PI[10]    = DOMAIN_GVR`           — the fork/domain (genesis-validators-root-derived signing domain).

These ride as published witness columns pinned to the public inputs (`.pin` legs), so a verifier
sees WHICH committee-root and WHICH (full 256-bit) state-root the proof speaks of. NOT-YET-CLOSED
(named residual, UNCHANGED by this revision): in this carrier slice the anchors are published but not
yet arithmetically bound to the carrier bits (that binding IS the in-AIR-crypto iteration — `BLS_OK`
derived from `COMMITTEE_ROOT` + signing root, `FIN_OK`/`EXEC_OK` derived from the branch folds into
`FIN_STATE_ROOT`). So `airAccepts` (the LOGIC refinement) is stated over the eight projections; the
anchor pins are the addressing layer around it.

## Witness (the update)

The hidden trace columns are the update's projections: `PC` (participant popcount), the two structural
lengths `CL`/`BL`, the two branch depths `FL`/`EL`, the two slacks `QDIFF`/`PC_SLACK`, and the three
carrier bits `BLS_OK`/`FIN_OK`/`EXEC_OK`. An honest prover fills `QDIFF = 3·pc − 1024` and
`PC_SLACK = bl − pc` and the carrier bits with the true `blst`/SHA-256 results; a forger who sets a
carrier bit it cannot justify is refused by the SAME no-forgery theorem the gate carries (the carriers
are `EthLeaf` fields under `hcr`/`hinj`).

## Constraint map (the SOURCE legs; the emitted bodies are the compiler's normal form)

| statement                                   | decision conjunct                          | source leg                               |
|---------------------------------------------|--------------------------------------------|------------------------------------------|
| committee is 512 keys                       | `decide (cl = 512)`                        | `.gate clC`                               |
| bitfield is 512 bits                        | `decide (bl = 512)`                        | `.gate blC`                               |
| quorum slack definition                     | (bridges `0<pc` ∧ `1024 ≤ 3pc`)            | `.gate qDiffC`                            |
| quorum slack non-negative (2/3 + Nomad)     | `decide (0<pc) ∧ decide (2·512 ≤ 3·pc)`    | `rangeLeg QDIFF` (`[0,2^11)`)             |
| ⚑ participation slack definition            | (nothing — the decision omits it too)      | `.gate pcSlackC`                          |
| ⚑ participation ≤ bitfield                  | (nothing — see the header)                 | `rangeLeg PC_SLACK` (`[0,2^11)`)          |
| BLS aggregate verified (carrier)            | `blsOk`                                    | `.gate blsC`                              |
| finality branch depth 6 ∨ 7                 | `decide (fl=6) ∨ decide (fl=7)`            | `.gate flC`                               |
| finality reconstruct ok (carrier)           | `finOk`                                    | `.gate finC`                              |
| execution branch depth 4                    | `decide (el=4)`                            | `.gate elC`                               |
| execution reconstruct ok (carrier)          | `execOk`                                   | `.gate execC`                             |
| trusted committee root is public            | (addressing)                               | `.pin COMMITTEE_ROOT → PI 0`              |
| finalized state root (full 256b) is public  | (addressing; nine limbs)                   | `.pin (FIN_STATE_ROOT i) → PI (1+i)`      |
| signing domain / gvr is public              | (addressing)                               | `.pin DOMAIN_GVR → PI 10`                 |

The two range lookups are the LOAD-BEARING teeth: `QDIFF = 3·pc − 1024 ∈ [0, 2^11)` iff `1024 ≤ 3·pc`
with no field-wrap escape (a sub-quorum `pc = 341` gives `QDIFF = −1`, far outside the interval —
UNSAT; this is the exact 342/341 Nomad boundary), and `PC_SLACK = bl − pc ∈ [0, 2^11)` iff `pc ≤ bl`
with the same no-wrap argument. The `0 < pc` floor is subsumed: `1024 ≤ 3·pc` already forces
`pc ≥ 342 > 0`.

## The mod-p ↔ ℤ reading (the shared field-soundness residual)

`airAccepts` reads the SOURCE constraints as ℤ equalities (`Constraint.holds`), the strong reading,
and `EffectLower.lowerConstraint_holdsAt_iff` carries them to the emitted gate bodies. The deployed
denotation is mod-`p` (`VmConstraint.holdsVm`); bridging the two needs full-wire range decomposition,
the same field-soundness residual every Emit descriptor carries. Not re-litigated here — but §5b
records that BOTH declared teeth sit strictly inside the field and that their wrapped negations are
outside the interval, which is what makes them `≤` relations rather than decorations.

## Axiom hygiene

Compiled descriptor + non-vacuous per-gate `iff` lemmas + the load-bearing `ethLcAir_sound` /
`ethLcAir_no_forgery` refinement + the hypothesis-free `ethLcAir_forces_participation_bounded`.
Every asserted fact is a NAMED THEOREM (`metatheory/docs/GUARD-DISCIPLINE.md`); this file contains
no `#guard`. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Circuit.Emit.EffectLowerCore
import Dregg2.Bridge.LightClientEthGate

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Dregg2.Circuit.Emit.LightClientEthAir

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId TableDef rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg PiPinLeg)
open Dregg2.Bridge.LightClientEth
open Dregg2.Bridge.LightClientEthGate

/-! ## §1 — the trace column layout (one logical row).

Columns 0..9 are the VERIFY-LOGIC projections `ethVerifyDecision` composes over (three of them
crypto carriers) plus the TWO slacks. Columns 10..20 are the published PUBLIC anchors:
`COMMITTEE_ROOT` (10), the NINE finalized-root limbs `FIN_STATE_ROOT 0..8` (cols 11..19 — the full
256-bit root, radix-`2^31`, MSB-first), and `DOMAIN_GVR` (20). -/

/-- Committee length (the sync-committee's key count); structural, forced `= 512`. Witness. -/
def CL : Nat := 0
/-- Bitfield length (the participation bitfield's bit count); structural, forced `= 512`. Witness. -/
def BL : Nat := 1
/-- Participant popcount (`SyncAggregate::count`). ⚑ Bounded BELOW by the quorum slack and ABOVE by
the participation slack — `342 ≤ PC ≤ BL`, both from the trace. Witness. -/
def PC : Nat := 2
/-- The quorum SLACK `3·PC − 1024`; the range tooth forces it into `[0, 2^11)`, i.e. `1024 ≤ 3·pc`. -/
def QDIFF : Nat := 3
/-- **CARRIER** — the `blst` aggregate-verify RESULT (participating subset signed the signing root);
forced `= 1` for accept. NAMED verified-FFI carrier, not re-derived in-AIR (this slice). Witness. -/
def BLS_OK : Nat := 4
/-- Finality-branch depth; forced `∈ {6, 7}` (Altair..Deneb | Electra+). Witness. -/
def FL : Nat := 5
/-- **CARRIER** — the SHA-256 finality-branch reconstruction compare RESULT (reconstruct into the
attested state root at subtree index 41); forced `= 1`. NAMED carrier. Witness. -/
def FIN_OK : Nat := 6
/-- Execution-branch depth; forced `= 4`. Witness. -/
def EL : Nat := 7
/-- **CARRIER** — the SHA-256 execution-branch reconstruction compare RESULT (reconstruct into the
finalized body root at subtree index 9); forced `= 1`. NAMED carrier. Witness. -/
def EXEC_OK : Nat := 8

/-- ⚑ **THE PARTICIPATION SLACK `BL − PC`** — the column that closes the unbounded-count residual.
Ranged into `[0, 2^11)`, so its non-negativity IS `PC ≤ BL`, with no field-wrap escape: a prover that
wants `PC > BL` must write `p − k` here, and `p − k ≥ p − 2^11` is two orders of magnitude above the
interval ceiling (`eth_wrapped_slack_is_outside_the_range`). Witness. -/
def PC_SLACK : Nat := 9

/-- **PUBLIC ANCHOR** — the TRUSTED sync-committee root (the WS-checkpoint trust anchor). PI-bound. -/
def COMMITTEE_ROOT : Nat := 10

/-- The number of ~31-bit limbs the FULL 256-bit finalized execution state root is exposed as:
`⌈256 / 31⌉ = 9`. Eight 31-bit limbs cover 248 bits; the ninth (most-significant) limb carries the
remaining 8 bits. This is the felt-width close — a SINGLE anchor felt bound only a 31-bit PROJECTION
of the 256-bit root (two roots agreeing in 31 bits both verified); nine limbs bind the WHOLE root. -/
def FIN_STATE_ROOT_LIMBS : Nat := 9

/-- **PUBLIC ANCHOR (limb `i`)** — the claimed FINALIZED execution state root B as its radix-`2^31`,
MOST-SIGNIFICANT-limb-first decomposition (the source `[u8;32]` from `eth-lightclient`'s
`FinalizedExecution.execution_state_root`). Limb `i` is trace column `11 + i` (cols 11..19); limb `0`
is the MSB (its top carries only 8 bits). PI-bound to slot `1 + i`, so the peer-wrap's radix-`2^31`
MSB-first pack over `PI[1..9]` recomposes the 256-bit root exactly before its 128-bit split. -/
def FIN_STATE_ROOT (i : Nat) : Nat := 11 + i

/-- **PUBLIC ANCHOR** — the fork/domain (genesis-validators-root-derived signing domain). PI-bound. -/
def DOMAIN_GVR : Nat := 11 + FIN_STATE_ROOT_LIMBS

/-- Total main-trace width: 9 logic columns + the participation slack + 1 committee anchor +
9 finalized-root limbs + 1 domain anchor. -/
def ETH_LC_WIDTH : Nat := 21

/-- PI slot 0: the trusted committee root. -/
def PI_COMMITTEE_ROOT : Nat := 0
/-- PI slot of finalized-root limb `i` (slots 1..9), MSB-first. -/
def PI_FIN_STATE_ROOT (i : Nat) : Nat := 1 + i
/-- PI slot of the signing domain / gvr (slot 10). -/
def PI_DOMAIN_GVR : Nat := 1 + FIN_STATE_ROOT_LIMBS
/-- Number of public inputs: committee root + 9 finalized-root limbs + domain. -/
def PI_COUNT : Nat := 11

/-- The shared slack range width, carrying BOTH teeth. `3·pc − 1024 ≤ 3·512 − 1024 = 512 < 2^11` and
`bl − pc ≤ 512 < 2^11` for any real committee, so completeness holds for `pc ≤ 512`; each interval's
floor `≥ 0` is the load-bearing relation. ⚑ 11 is WRAP-FREE at BabyBear (`≤ 29`) — the width census
that found three shipped tables vacuous at 64/128 left this one untouched. -/
def Q_BITS : Nat := 11

/-! ## §2 — the SOURCE constraints, in the framework's own gate algebra (`Circuit.Expr`).

These are `Constraint`s (`lhs = rhs`), NOT `VmConstraint2`s. The compiler normalizes each through
`AirBuilder.Head` and emits the residual `lhs − rhs`; nothing in this file writes a gate body. -/

/-- **G1 — the committee is 512 keys**: `CL = 512`. -/
def clC : Constraint := ⟨.var CL, .const 512⟩
/-- **G2 — the bitfield is 512 bits**: `BL = 512`. -/
def blC : Constraint := ⟨.var BL, .const 512⟩
/-- **G3 — the quorum slack identity**: `QDIFF + 1024 = 3·PC`. Ranged ⟹ `1024 ≤ 3·pc`. -/
def qDiffC : Constraint := ⟨.add (.var QDIFF) (.const 1024), .mul (.const 3) (.var PC)⟩
/-- ⚑ **G4 — THE PARTICIPATION SLACK IDENTITY**: `PC_SLACK + PC = BL`. Ranged ⟹ `PC ≤ BL`, the
conjunct neither this AIR nor `syncDecision` had. -/
def pcSlackC : Constraint := ⟨.add (.var PC_SLACK) (.var PC), .var BL⟩
/-- **G5 — the BLS carrier**: `BLS_OK = 1`. -/
def blsC : Constraint := ⟨.var BLS_OK, .const 1⟩
/-- **G6 — the finality depth is 6 or 7**: `(FL − 6)·(FL − 7) = 0`. -/
def flC : Constraint :=
  ⟨.mul (.add (.var FL) (.const (-6))) (.add (.var FL) (.const (-7))), .const 0⟩
/-- **G7 — the finality-reconstruct carrier**: `FIN_OK = 1`. -/
def finC : Constraint := ⟨.var FIN_OK, .const 1⟩
/-- **G8 — the execution depth is 4**: `EL = 4`. -/
def elC : Constraint := ⟨.var EL, .const 4⟩
/-- **G9 — the execution-reconstruct carrier**: `EXEC_OK = 1`. -/
def execC : Constraint := ⟨.var EXEC_OK, .const 1⟩

/-! ## §3 — ⚑ THE SOURCE AIR, and the descriptor as the COMPILER'S OUTPUT. -/

/-- The declared range table carrying both slack teeth. -/
def ethRangeTable : TableDef := rangeTableDef Q_BITS

/-- A range query on one wire, in the source vocabulary. -/
def rangeLeg (col : Nat) : AirLeg :=
  .lookup { table := TableId.range, tuple := [Expr.var col] }

/-- The nine finalized-root PI pins (cols 11..19 → PI 1..9), written out so the emission pins below
reduce with no fold. -/
def finStateRootPins : List AirLeg :=
  [ .pin ⟨VmRow.first, FIN_STATE_ROOT 0, PI_FIN_STATE_ROOT 0⟩
  , .pin ⟨VmRow.first, FIN_STATE_ROOT 1, PI_FIN_STATE_ROOT 1⟩
  , .pin ⟨VmRow.first, FIN_STATE_ROOT 2, PI_FIN_STATE_ROOT 2⟩
  , .pin ⟨VmRow.first, FIN_STATE_ROOT 3, PI_FIN_STATE_ROOT 3⟩
  , .pin ⟨VmRow.first, FIN_STATE_ROOT 4, PI_FIN_STATE_ROOT 4⟩
  , .pin ⟨VmRow.first, FIN_STATE_ROOT 5, PI_FIN_STATE_ROOT 5⟩
  , .pin ⟨VmRow.first, FIN_STATE_ROOT 6, PI_FIN_STATE_ROOT 6⟩
  , .pin ⟨VmRow.first, FIN_STATE_ROOT 7, PI_FIN_STATE_ROOT 7⟩
  , .pin ⟨VmRow.first, FIN_STATE_ROOT 8, PI_FIN_STATE_ROOT 8⟩ ]

/-- ⚑ **THE SOURCE.** The ETH finalized-update verify AIR in the `EffectAir` vocabulary. Nothing here
is in the deployed IR's language: `AirLeg`, `LookupLeg` and `PiPinLeg` are the source, and the
`VmConstraint2`s are what `EffectLower.lowerAir` produces. -/
def ethHeadAir : EffectAir :=
  { tables := [ethRangeTable]
  , legs   :=
      [ .gate clC
      , .gate blC
      , .gate qDiffC
      , rangeLeg QDIFF
      -- ⚑ the participation bound, the two legs that close the unbounded-count residual.
      , .gate pcSlackC
      , rangeLeg PC_SLACK
      , .gate blsC
      , .gate flC
      , .gate finC
      , .gate elC
      , .gate execC
      , .pin ⟨VmRow.first, COMMITTEE_ROOT, PI_COMMITTEE_ROOT⟩ ]
      ++ finStateRootPins
      ++ [ .pin ⟨VmRow.first, DOMAIN_GVR, PI_DOMAIN_GVR⟩ ] }

/-- ⚑ **THE VOCABULARY WAS ADEQUATE.** Every leg is main-rail expressible, decided on the emitted
predicate — so no leg lowered to `EffectLower.refuseConstraints` and nothing was hand-written around
the compiler. -/
theorem ethHeadAir_mainRailOk : ethHeadAir.mainRailOk = true := by rfl

/-- Every declared PI pin indexes a slot the descriptor declares. -/
theorem ethHeadAir_pinsFit : ethHeadAir.pinsFit PI_COUNT = true := by rfl

/-- The source carries 22 legs: 9 gates + 2 slack lookups + 11 PI pins. -/
theorem ethHeadAir_leg_count : ethHeadAir.legs.length = 22 := by rfl

/-- The per-kind shape: nine gates, two lookups, eleven pins, no windows and no limbed quantities.
A leg that changed kind (a gate quietly re-scoped to a window, a lookup dropped) moves one of
these. -/
theorem ethHeadAir_kind_shape :
    ethHeadAir.gateCount = 9 ∧ ethHeadAir.lookupCount = 2 ∧ ethHeadAir.pinCount = 11
      ∧ ethHeadAir.windowCount = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **`ethLcVerifyDesc` — COMPILER OUTPUT.** The ETH/Base light-client verify decision as an IR-v2
AIR. Not modelled beside a hand-written twin; there is no twin.

⚠ `lowerAir`, not `lowerEffect`: this descriptor is not a full-state effect and has no digest wires,
so the framework's `PIBindsDigests` surface would emit a descriptor nobody deployed. -/
def ethLcVerifyDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-eth-lightclient-verify::v1" ETH_LC_WIDTH PI_COUNT [] ethHeadAir

/-! ### §3a — the emission pins: what the compiler produced, against a hand-written expectation.

`rfl`, and therefore GATES rather than decoration — a change to the leg lowerings, the leg ORDER or
`assemble` moves one of these and it goes red here, one module above the compiler where the
descriptor is actually deployed from. The gate BODIES are deliberately not transcribed: their normal
form is the normalizer's business, and §4/§5 pin their MEANING. -/

theorem ethLcVerifyDesc_name : ethLcVerifyDesc.name = "dregg-eth-lightclient-verify::v1" := rfl
theorem ethLcVerifyDesc_width : ethLcVerifyDesc.traceWidth = ETH_LC_WIDTH := rfl
theorem ethLcVerifyDesc_piCount : ethLcVerifyDesc.piCount = PI_COUNT := rfl
theorem ethLcVerifyDesc_tables : ethLcVerifyDesc.tables = [ethRangeTable] := rfl
theorem ethLcVerifyDesc_hashSites : ethLcVerifyDesc.hashSites = [] := rfl
theorem ethLcVerifyDesc_ranges : ethLcVerifyDesc.ranges = [] := rfl

/-- The compiler emitted 22 constraints from 22 legs — one per leg, no `.limbs` fan-out. -/
theorem ethLcVerifyDesc_constraint_count : ethLcVerifyDesc.constraints.length = 22 := rfl

/-- ⚑ **THE TWO SLACK LOOKUPS, AT THEIR EMITTED POSITIONS.** `rfl` on a slice of the compiler's
output: constraint 3 is the quorum tooth, constraint 5 is the PARTICIPATION tooth. A leg that
lowered to `EffectLower.refuseConstraints` would emit a `.boundary` pair here instead and this goes
red; a dropped participation lookup — the state this file was in before 2026-08-03 — moves it too. -/
theorem ethLcVerifyDesc_slack_lookups :
    (ethLcVerifyDesc.constraints.drop 3).take 1 = [.lookup ⟨TableId.range, [.var QDIFF]⟩]
      ∧ (ethLcVerifyDesc.constraints.drop 5).take 1
        = [.lookup ⟨TableId.range, [.var PC_SLACK]⟩] :=
  ⟨rfl, rfl⟩

/-- ⚑ **THE ELEVEN PI PINS, AS THE COMPILER EMITTED THEM** — the addressing layer in one `rfl`. A
reordering, a dropped pin or a re-indexed slot moves this. -/
theorem ethLcVerifyDesc_pins :
    ethLcVerifyDesc.constraints.drop 11 =
      [ .base (.piBinding VmRow.first COMMITTEE_ROOT PI_COMMITTEE_ROOT)
      , .base (.piBinding VmRow.first (FIN_STATE_ROOT 0) (PI_FIN_STATE_ROOT 0))
      , .base (.piBinding VmRow.first (FIN_STATE_ROOT 1) (PI_FIN_STATE_ROOT 1))
      , .base (.piBinding VmRow.first (FIN_STATE_ROOT 2) (PI_FIN_STATE_ROOT 2))
      , .base (.piBinding VmRow.first (FIN_STATE_ROOT 3) (PI_FIN_STATE_ROOT 3))
      , .base (.piBinding VmRow.first (FIN_STATE_ROOT 4) (PI_FIN_STATE_ROOT 4))
      , .base (.piBinding VmRow.first (FIN_STATE_ROOT 5) (PI_FIN_STATE_ROOT 5))
      , .base (.piBinding VmRow.first (FIN_STATE_ROOT 6) (PI_FIN_STATE_ROOT 6))
      , .base (.piBinding VmRow.first (FIN_STATE_ROOT 7) (PI_FIN_STATE_ROOT 7))
      , .base (.piBinding VmRow.first (FIN_STATE_ROOT 8) (PI_FIN_STATE_ROOT 8))
      , .base (.piBinding VmRow.first DOMAIN_GVR PI_DOMAIN_GVR) ] := rfl

/-- Layout sanity, as theorems rather than guards: the nine root limbs are contiguous, sit between
the committee anchor and the domain anchor, all inside the declared width; the three carriers and
both slacks are hidden columns below the published block; and nine base-`2^31` limbs cover 256 bits. -/
theorem eth_layout_wellformed :
    FIN_STATE_ROOT 0 = 11 ∧ FIN_STATE_ROOT 8 = 19 ∧ DOMAIN_GVR = 20
      ∧ DOMAIN_GVR < ETH_LC_WIDTH ∧ COMMITTEE_ROOT < FIN_STATE_ROOT 0
      ∧ PI_FIN_STATE_ROOT 8 < PI_DOMAIN_GVR ∧ PI_DOMAIN_GVR < PI_COUNT
      ∧ 31 * FIN_STATE_ROOT_LIMBS ≥ 256 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The three carriers and both slacks are real hidden trace columns, all below the published
anchors: a carrier or a slack a verifier could set from outside the proof would be no check at all. -/
theorem eth_carriers_and_slacks_hidden :
    BLS_OK < COMMITTEE_ROOT ∧ FIN_OK < COMMITTEE_ROOT ∧ EXEC_OK < COMMITTEE_ROOT
      ∧ QDIFF < COMMITTEE_ROOT ∧ PC_SLACK < COMMITTEE_ROOT := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §4 — non-vacuous per-gate lemmas (the SOURCE constraints bite, both directions).

Each is an `iff` on the constraint's own `holds`, so a gate that stopped saying what its name says
goes red here. The compiler carries these to the emitted bodies through
`EffectLower.lowerConstraint_holdsAt_iff` + `AirBuilder.headToExpr_eval`. -/

theorem clC_holds_iff (a : Assignment) : clC.holds a ↔ a CL = 512 := Iff.rfl
theorem blC_holds_iff (a : Assignment) : blC.holds a ↔ a BL = 512 := Iff.rfl

theorem qDiffC_holds_iff (a : Assignment) :
    qDiffC.holds a ↔ a QDIFF = 3 * a PC - 1024 := by
  simp only [Constraint.holds, qDiffC, Expr.eval]; constructor <;> intro h <;> omega

/-- ⚑ The participation slack identity, both directions. -/
theorem pcSlackC_holds_iff (a : Assignment) :
    pcSlackC.holds a ↔ a PC_SLACK = a BL - a PC := by
  simp only [Constraint.holds, pcSlackC, Expr.eval]; constructor <;> intro h <;> omega

theorem blsC_holds_iff (a : Assignment) : blsC.holds a ↔ a BLS_OK = 1 := Iff.rfl

theorem flC_holds_iff (a : Assignment) : flC.holds a ↔ (a FL = 6 ∨ a FL = 7) := by
  simp only [Constraint.holds, flC, Expr.eval]
  rw [mul_eq_zero]; constructor <;> rintro (h | h) <;> omega

theorem finC_holds_iff (a : Assignment) : finC.holds a ↔ a FIN_OK = 1 := Iff.rfl
theorem elC_holds_iff (a : Assignment) : elC.holds a ↔ a EL = 4 := Iff.rfl
theorem execC_holds_iff (a : Assignment) : execC.holds a ↔ a EXEC_OK = 1 := Iff.rfl

/-! ## §5 — `airAccepts`: the descriptor's LOGIC-acceptance predicate on one row, and the
REFINEMENT to `ethVerifyDecision`. -/

/-- The range interval one slack column must fall in — the emitted lookup's own denotation. -/
def inRange (a : Assignment) (col : Nat) : Prop :=
  0 ≤ a col ∧ a col < (2 : ℤ) ^ Q_BITS

/-- **`airAccepts a`** — the emitted verify-logic constraints all hold on row `a`, and BOTH slacks
lie in the range interval `[0, 2^Q_BITS)`. This is "the descriptor accepts the logic of row `a`"
(the eleven published-anchor pins are the addressing layer, orthogonal to the logic). -/
def airAccepts (a : Assignment) : Prop :=
  clC.holds a
  ∧ blC.holds a
  ∧ qDiffC.holds a
  ∧ inRange a QDIFF
  ∧ pcSlackC.holds a
  ∧ inRange a PC_SLACK
  ∧ blsC.holds a
  ∧ flC.holds a
  ∧ finC.holds a
  ∧ elC.holds a
  ∧ execC.holds a

/-- **THE RANGE TOOTH IS THE EMITTED ONE.** A slack column in `inRange` is exactly a column whose
singleton row is in the declared range table — so `airAccepts`'s interval is the emitted lookup's
denotation, not a second private notion of "in range". -/
theorem inRange_iff_mem_rangeRows (a : Assignment) (col : Nat) :
    inRange a col ↔ [a col] ∈ rangeRows Q_BITS :=
  (range_row_mem_iff (a col) Q_BITS).symm

/-! ### §5a — ⚑ THE PARTICIPATION BOUND, FORCED FROM THE TRACE ALONE.

This is the theorem the residual was missing. It takes NO hypothesis about the update, no
witness relation, no `pc` argument — only that the emitted constraints hold on the row — and it
concludes the bound `ethLcAir_sound` previously could only assume. -/

/-- ⚑ **THE CLOSURE: an accepted row's participation count is bounded on BOTH sides, with nothing
assumed about what the row means.** `342 ≤ PC ≤ BL = 512`.

Before the `PC_SLACK` leg, the right-hand bound did not exist: `PC = 1023` satisfied every emitted
constraint (it is `QDIFF = 2045 < 2048`) and PROVED on the deployed prover. The upper bound here is
exactly what a run refuted. -/
theorem ethLcAir_forces_participation_bounded {a : Assignment} (h : airAccepts a) :
    a BL = 512 ∧ a CL = 512 ∧ 342 ≤ a PC ∧ a PC ≤ a BL := by
  obtain ⟨hcl, hbl, hq, ⟨hq0, _⟩, hslk, ⟨hs0, _⟩, _, _, _, _, _⟩ := h
  have hbl' : a BL = 512 := (blC_holds_iff a).mp hbl
  have hcl' : a CL = 512 := (clC_holds_iff a).mp hcl
  have hq' : a QDIFF = 3 * a PC - 1024 := (qDiffC_holds_iff a).mp hq
  have hs' : a PC_SLACK = a BL - a PC := (pcSlackC_holds_iff a).mp hslk
  refine ⟨hbl', hcl', ?_, ?_⟩
  · rw [hq'] at hq0; omega
  · rw [hs'] at hs0; omega

/-- The same bound in its most usable form: an accepted row's participation count lies in the real
interval a 512-key sync committee admits. -/
theorem ethLcAir_forces_pc_in_committee_interval {a : Assignment} (h : airAccepts a) :
    342 ≤ a PC ∧ a PC ≤ 512 := by
  obtain ⟨hbl, _, hlo, hhi⟩ := ethLcAir_forces_participation_bounded h
  exact ⟨hlo, by rw [hbl] at hhi; exact hhi⟩

/-! ### §5b — the two teeth are NOT vacuous: the interval sits inside the field, and the wrapped
negation sits outside it. Without both, a `≤` gate is decoration. -/

/-- The declared interval sits strictly inside the deployed field. At 31 or 32 bits this is FALSE
and the lookup refuses nothing, because every BabyBear element is already below `2^31`. -/
theorem eth_range_is_inside_the_field :
    (2 : ℤ) ^ Q_BITS < Dregg2.Circuit.Emit.EffectLower.P := by
  norm_num [Q_BITS, Dregg2.Circuit.Emit.EffectLower.P]

/-- ⚑ **AND THE WRAP IS REFUSED.** A slack the prover wanted to be `−k` for any `0 < k ≤ 2^11` is,
in the deployed mod-`p` reading, the element `p − k` — and `p − k ≥ p − 2048 = 2013263873`, six
orders of magnitude above the interval ceiling. So "the slack is non-negative" is enforced with NO
field-wrap escape, which is what makes G3 and G4 the `≤` relations they are named for.

This is the theorem the exhibited refusals cash: `PC = 341` writes `QDIFF = p − 1` and `PC = 1023`
writes `PC_SLACK = p − 511`, and both are outside `[0, 2^11)`. -/
theorem eth_wrapped_slack_is_outside_the_range (k : ℤ) (hk : 0 < k)
    (hk' : k ≤ (2 : ℤ) ^ Q_BITS) :
    ¬ (0 ≤ Dregg2.Circuit.Emit.EffectLower.P - k
        ∧ Dregg2.Circuit.Emit.EffectLower.P - k < (2 : ℤ) ^ Q_BITS) := by
  rintro ⟨_, hlt⟩
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  have hb : ((2 : ℤ) ^ Q_BITS) = 2048 := by norm_num [Q_BITS]
  rw [hp, hb] at hlt
  rw [hb] at hk'
  omega

/-! ### §5b2 — ⚑ THE NEW BOUND IS TRUE OF EVERY REAL UPDATE.

A wrong bound is worse than none, so this is the completeness half stated over the MODEL rather than
over a chosen row: whatever committee and whatever bitfield, the participating subset is never longer
than the bitfield, so an honest prover can ALWAYS fill `PC_SLACK` non-negatively. Without this the
new leg could be a gate that refuses honest updates, which is the failure mode a "bound" reaches for
first. -/

/-- **`participants` never returns more elements than the bitfield has bits.** It is a simultaneous
recursion over the committee and the bit list (`LightClientEth.lean:370-373`) that stops when EITHER
runs out, and the `b :: bs` step consumes one bit whether or not it keeps the key. -/
theorem participants_length_le_bits {α : Type} :
    ∀ (c : List α) (bs : List Bool), (participants c bs).length ≤ bs.length := by
  intro c
  induction c with
  | nil => intro bs; simp [participants]
  | cons pk cs ih =>
      intro bs
      cases bs with
      | nil => simp [participants]
      | cons b bs =>
          cases b with
          | true => simpa [participants] using ih bs
          | false => exact le_trans (by simpa [participants] using ih bs) (Nat.le_succ _)

/-- ⚑ **SO THE `PC_SLACK` LEG IS COMPLETE FOR EVERY UPDATE, NOT JUST THE ONES A TEST PICKS.** The
honest fill `PC_SLACK = bl − pc` is non-negative on every real `(committee, bitfield)` pair, so the
new gate cannot refuse an honest prover. This is the statement that makes the bound the RIGHT one
rather than merely a bound. -/
theorem eth_participation_slack_is_fillable (L : EthLeaf) (ts : EthState L)
    (u : LightClientUpdate L) :
    (participants ts.committee u.syncAggregate.bits).length ≤ u.syncAggregate.bits.length :=
  participants_length_le_bits _ _

/-! ### §5c — the refinement to the exported decision. -/

/-- **THE REFINEMENT (soundness): a satisfying AIR witness ENTAILS `ethVerifyDecision` accept.**
Fed a row `a` whose columns read the update's true projections (the honest-witness relation — the
lengths/depths as felts, the carrier bits as `if · then 1 else 0`), if the emitted verify-logic
constraints accept, then the exported scalar decision `ethVerifyDecision` accepts those projections.
This is the load-bearing tie: a STARK that satisfies `ethLcVerifyDesc` proves the object
`eth_no_forgery` is stated over. The quorum range floor discharges BOTH the Nomad floor `0 < pc` and
the 2/3 threshold.

⚠ **`hpc` IS NOT SHEDDABLE AND THE `PC_SLACK` GATE DOES NOT CHANGE THAT** — say it here rather than
leave it to be re-derived. `hpc` is not an ASSUMPTION about the value `pc`; it is the WITNESS
RELATION that names which trace column carries it, exactly like `hcl`/`hbl`/`hfl`/`hel`. Drop it and
`pc` is a free `Nat` the conclusion is simply false about (take `pc = 0`). What the new gate buys is
`ethLcAir_forces_participation_bounded`, which needs NO such hypothesis at all — a bound on the
TRACE rather than a bound assumed of the update. That is the strengthening, and it is a new theorem,
not a deleted hypothesis. -/
theorem ethLcAir_sound (a : Assignment)
    (cl bl pc fl el : Nat) (blsOk finOk execOk : Bool)
    (hcl : a CL = (cl : ℤ)) (hbl : a BL = (bl : ℤ)) (hpc : a PC = (pc : ℤ))
    (hfl : a FL = (fl : ℤ)) (hel : a EL = (el : ℤ))
    (hbls : a BLS_OK = (if blsOk then (1 : ℤ) else 0))
    (hfin : a FIN_OK = (if finOk then (1 : ℤ) else 0))
    (hexec : a EXEC_OK = (if execOk then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    ethVerifyDecision cl bl pc blsOk fl finOk el execOk = true := by
  obtain ⟨hclB, hblB, hqB, ⟨hq0, _hqlt⟩, _hslkB, _hslkR, hblsB, hflB, hfinB, helB, hexecB⟩ := hacc
  -- Structural length equalities (ℤ read, cast to Nat).
  have hcl512 : cl = syncCommitteeSize := by
    have h : (cl : ℤ) = 512 := by rw [← hcl]; exact (clC_holds_iff a).mp hclB
    have : cl = 512 := by exact_mod_cast h
    simpa [syncCommitteeSize] using this
  have hbl512 : bl = syncCommitteeSize := by
    have h : (bl : ℤ) = 512 := by rw [← hbl]; exact (blC_holds_iff a).mp hblB
    have : bl = 512 := by exact_mod_cast h
    simpa [syncCommitteeSize] using this
  -- Quorum: the range floor forces 1024 ≤ 3·pc, which subsumes the Nomad floor 0 < pc.
  have hqeq : a QDIFF = 3 * a PC - 1024 := (qDiffC_holds_iff a).mp hqB
  have hqge : (1024 : ℤ) ≤ 3 * (pc : ℤ) := by
    have h0 : (0 : ℤ) ≤ a QDIFF := hq0
    rw [hqeq, hpc] at h0; linarith
  have hnat : 1024 ≤ 3 * pc := by exact_mod_cast hqge
  have hpos : 0 < pc := by omega
  have hquorum : 2 * syncCommitteeSize ≤ 3 * pc := by unfold syncCommitteeSize; omega
  -- Carrier bits.
  have hbls' : blsOk = true := by
    have h : a BLS_OK = 1 := (blsC_holds_iff a).mp hblsB
    rw [hbls] at h; cases blsOk with | true => rfl | false => simp at h
  have hfin' : finOk = true := by
    have h : a FIN_OK = 1 := (finC_holds_iff a).mp hfinB
    rw [hfin] at h; cases finOk with | true => rfl | false => simp at h
  have hexec' : execOk = true := by
    have h : a EXEC_OK = 1 := (execC_holds_iff a).mp hexecB
    rw [hexec] at h; cases execOk with | true => rfl | false => simp at h
  -- Branch depths.
  have hfl67' : fl = finalizedRootDepth ∨ fl = finalizedRootDepthElectra := by
    rcases (flC_holds_iff a).mp hflB with h | h
    · left
      have : (fl : ℤ) = 6 := by rw [← hfl]; exact h
      have : fl = 6 := by exact_mod_cast this
      simpa [finalizedRootDepth] using this
    · right
      have : (fl : ℤ) = 7 := by rw [← hfl]; exact h
      have : fl = 7 := by exact_mod_cast this
      simpa [finalizedRootDepthElectra] using this
  have hel4 : el = executionPayloadDepth := by
    have h : a EL = 4 := (elC_holds_iff a).mp helB
    rw [hel] at h
    have : el = 4 := by exact_mod_cast h
    simpa [executionPayloadDepth] using this
  -- Assemble the three sub-decisions, then the composed decision.
  have hsync : syncDecision cl bl pc blsOk = true := by
    unfold syncDecision
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨hcl512, hbl512⟩, hpos⟩, hquorum⟩, hbls'⟩
  have hfinD : finalityDecision fl finOk = true := by
    unfold finalityDecision
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨hfl67', hfin'⟩
  have hexecD : execDecision el execOk = true := by
    unfold execDecision
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hel4, hexec'⟩
  simp only [ethVerifyDecision, hsync, hfinD, hexecD, Bool.and_true]

/-- ⚑ **THE STRENGTHENING THE NEW LEG BUYS AT THE REFINEMENT.** Under the SAME witness relations,
an accepted row now also entails that the participant count does not exceed the bitfield — a
conjunct `ethVerifyDecision` itself never checked (`syncDecision`, `LightClientEthGate.lean:90-95`).
So the emitted AIR is strictly STRONGER than the decision it refines on this conjunct, which is the
sound direction to be strictly stronger in. -/
theorem ethLcAir_sound_bounds_participation (a : Assignment) (bl pc : Nat)
    (hbl : a BL = (bl : ℤ)) (hpc : a PC = (pc : ℤ)) (hacc : airAccepts a) :
    pc ≤ bl ∧ pc ≤ syncCommitteeSize := by
  obtain ⟨hbl512, _, _, hle⟩ := ethLcAir_forces_participation_bounded hacc
  rw [hbl, hpc] at hle
  have h1 : pc ≤ bl := by exact_mod_cast hle
  have h2 : (bl : ℤ) = 512 := by rw [← hbl]; exact hbl512
  have h3 : bl = 512 := by exact_mod_cast h2
  exact ⟨h1, by simpa [syncCommitteeSize, h3] using h1⟩

/-- **THE PAYOFF: a satisfying AIR witness ENTAILS Ethereum-validity (no-forgery, routed through the
emitted AIR).** GIVEN the named SHA-256 CR + chunk-injectivity carriers (`hcr`/`hinj`), if a row `a`
reads update `u`'s true projections under trusted state `ts` and the emitted verify-logic
constraints accept, then `u` is Ethereum-VALID relative to `ts` — a ≥ 2/3 subset of the TRUSTED
committee genuinely signed the attested header, the attested state commits AND BINDS the finalized
header, and the finalized body commits the execution payload. So a STARK proving `ethLcVerifyDesc`
carries `eth_no_forgery`: the portable, trustless proof of Base/ETH finality. -/
theorem ethLcAir_no_forgery (L : EthLeaf) (hcr : L.hashPairCR) (hinj : L.uChunkInj)
    (ts : EthState L) (u : LightClientUpdate L) (a : Assignment)
    (hcl : a CL = (ts.committee.length : ℤ))
    (hbl : a BL = (u.syncAggregate.bits.length : ℤ))
    (hpc : a PC = ((participants ts.committee u.syncAggregate.bits).length : ℤ))
    (hfl : a FL = (u.finalityBranch.length : ℤ))
    (hel : a EL = (u.finalizedHeader.executionBranch.length : ℤ))
    (hbls : a BLS_OK = (if L.blsAggVerify (participants ts.committee u.syncAggregate.bits)
                          (signingRoot L ts u.attestedHeader) u.syncAggregate.sig
                        then (1 : ℤ) else 0))
    (hfin : a FIN_OK = (if L.beq (reconstruct L (htrHeader L u.finalizedHeader.beacon)
                          u.finalityBranch finalizedRootSubtreeIndex) u.attestedHeader.stateRoot
                        then (1 : ℤ) else 0))
    (hexec : a EXEC_OK = (if L.beq (reconstruct L (htrExec L u.finalizedHeader.execution)
                          u.finalizedHeader.executionBranch executionPayloadSubtreeIndex)
                          u.finalizedHeader.beacon.bodyRoot
                        then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    EthValidAt L ts u := by
  -- `ethLcAir_sound` at `u`'s projections yields exactly `ethProjectedDecision L ts u = true`.
  have hdec := ethLcAir_sound a ts.committee.length u.syncAggregate.bits.length
      (participants ts.committee u.syncAggregate.bits).length
      u.finalityBranch.length u.finalizedHeader.executionBranch.length
      (L.blsAggVerify (participants ts.committee u.syncAggregate.bits)
        (signingRoot L ts u.attestedHeader) u.syncAggregate.sig)
      (L.beq (reconstruct L (htrHeader L u.finalizedHeader.beacon) u.finalityBranch
        finalizedRootSubtreeIndex) u.attestedHeader.stateRoot)
      (L.beq (reconstruct L (htrExec L u.finalizedHeader.execution)
        u.finalizedHeader.executionBranch executionPayloadSubtreeIndex)
        u.finalizedHeader.beacon.bodyRoot)
      hcl hbl hpc hfl hel hbls hfin hexec hacc
  exact ethVerifyDecision_no_forgery L hcr hinj ts u hdec

/-- **Completeness of the two teeth (the honest prover CAN fill both slacks).** For any decision-
accepting projections with a real committee (`pc ≤ 512`), an honest row that fills
`QDIFF = 3·pc − 1024`, `PC_SLACK = bl − pc` and the carrier bits with the true results is accepted by
the emitted logic. This is the non-vacuity partner of soundness: the AIR is satisfiable EXACTLY on
accepted updates, not vacuously empty.

⚠ `hpc_le` is NOT sheddable either, and for a different reason than `hpc`: `ethVerifyDecision` does
not bound `pc` above at all, so the decision alone does not supply it. That is the same omission the
`PC_SLACK` leg closes on the AIR side — the AIR now says more than the decision, so completeness
needs the extra fact as input. -/
theorem ethLcAir_complete (a : Assignment)
    (cl bl pc fl el : Nat) (blsOk finOk execOk : Bool)
    (hcl : a CL = (cl : ℤ)) (hbl : a BL = (bl : ℤ)) (hpc : a PC = (pc : ℤ))
    (hfl : a FL = (fl : ℤ)) (hel : a EL = (el : ℤ))
    (hqdiff : a QDIFF = 3 * (pc : ℤ) - 1024)
    (hslack : a PC_SLACK = (bl : ℤ) - (pc : ℤ))
    (hbls : a BLS_OK = (if blsOk then (1 : ℤ) else 0))
    (hfin : a FIN_OK = (if finOk then (1 : ℤ) else 0))
    (hexec : a EXEC_OK = (if execOk then (1 : ℤ) else 0))
    (hpc_le : pc ≤ syncCommitteeSize)
    (hdec : ethVerifyDecision cl bl pc blsOk fl finOk el execOk = true) :
    airAccepts a := by
  unfold ethVerifyDecision syncDecision finalityDecision execDecision at hdec
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨⟨⟨⟨⟨hcl512, hbl512⟩, _hpos⟩, hquorum⟩, hbls1⟩, hfl67, hfin1⟩, hel4, hexec1⟩ := hdec
  have hquorum' : 1024 ≤ 3 * pc := by unfold syncCommitteeSize at hquorum; omega
  have hpc_le' : pc ≤ 512 := by simpa [syncCommitteeSize] using hpc_le
  have hbl512' : bl = 512 := by simpa [syncCommitteeSize] using hbl512
  have hblZ : (bl : ℤ) = 512 := by exact_mod_cast hbl512'
  have hpcZ : (pc : ℤ) ≤ 512 := by exact_mod_cast hpc_le'
  have hpc0 : (0 : ℤ) ≤ (pc : ℤ) := Int.natCast_nonneg pc
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [clC_holds_iff, hcl]; exact_mod_cast (by simpa [syncCommitteeSize] using hcl512)
  · rw [blC_holds_iff, hbl]; exact_mod_cast hbl512'
  · rw [qDiffC_holds_iff, hpc, hqdiff]
  · rw [hqdiff]
    have h1024 : (1024 : ℤ) ≤ 3 * (pc : ℤ) := by exact_mod_cast hquorum'
    linarith
  · rw [hqdiff]
    have hle : 3 * (pc : ℤ) - 1024 ≤ 512 := by linarith
    calc 3 * (pc : ℤ) - 1024 ≤ 512 := hle
      _ < (2 : ℤ) ^ Q_BITS := by norm_num [Q_BITS]
  · rw [pcSlackC_holds_iff, hbl, hpc, hslack]
  · rw [hslack, hblZ]; linarith
  · rw [hslack, hblZ]
    calc (512 : ℤ) - (pc : ℤ) ≤ 512 := by linarith
      _ < (2 : ℤ) ^ Q_BITS := by norm_num [Q_BITS]
  · rw [blsC_holds_iff, hbls]; simp [hbls1]
  · rw [flC_holds_iff, hfl]
    rcases hfl67 with h | h
    · left; exact_mod_cast (by simpa [finalizedRootDepth] using h)
    · right; exact_mod_cast (by simpa [finalizedRootDepthElectra] using h)
  · rw [finC_holds_iff, hfin]; simp [hfin1]
  · rw [elC_holds_iff, hel]; exact_mod_cast (by simpa [executionPayloadDepth] using hel4)
  · rw [execC_holds_iff, hexec]; simp [hexec1]

/-! ## §6 — NON-VACUITY: the emitted teeth DISCRIMINATE, in BOTH polarities, as NAMED theorems.

⚑ These were `#guard`s. A `#guard` checks one closed instance, leaves no term and is invisible to
axiom accounting (`metatheory/docs/GUARD-DISCIPLINE.md`); each is now a theorem over the SOURCE
constraint the compiler lowers, so the discrimination is a fact something can build on. -/

/-- The honest row of an accepted 400-of-512 update — the row the deployed prover proves in release
(`circuit/tests/eth_lightclient_proves.rs`). All eleven anchors are zero here: they are the
addressing layer and no logic constraint reads them. -/
def honestRow (pc : ℤ) : Assignment := fun i =>
  if i = CL then 512
  else if i = BL then 512
  else if i = PC then pc
  else if i = QDIFF then 3 * pc - 1024
  else if i = PC_SLACK then 512 - pc
  else if i = BLS_OK then 1
  else if i = FL then 6
  else if i = FIN_OK then 1
  else if i = EL then 4
  else if i = EXEC_OK then 1
  else 0

/-- The honest 400-of-512 update is ACCEPTED. -/
theorem eth_accepts_the_honest_update : airAccepts (honestRow 400) := by
  refine ⟨rfl, rfl, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, rfl, ?_, rfl, rfl, rfl⟩ <;>
    simp [honestRow, Constraint.holds, Expr.eval, CL, BL, PC, QDIFF, PC_SLACK, BLS_OK, FL,
      Q_BITS, flC, qDiffC, pcSlackC]

/-- ⚑ **THE NOMAD BOUNDARY, in-AIR**: the exact-quorum `pc = 342` row is accepted… -/
theorem eth_accepts_the_minimal_quorum : airAccepts (honestRow 342) := by
  refine ⟨rfl, rfl, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, rfl, ?_, rfl, rfl, rfl⟩ <;>
    simp [honestRow, Constraint.holds, Expr.eval, CL, BL, PC, QDIFF, PC_SLACK, BLS_OK, FL,
      Q_BITS, flC, qDiffC, pcSlackC]

/-- …and the sub-quorum `pc = 341` row is REFUSED. `3·341 − 1024 = −1`, outside `[0, 2^11)` — the
342-accept / 341-reject tooth, and the reason a Nomad-style forgery cannot be witnessed. -/
theorem eth_refuses_the_sub_quorum : ¬ airAccepts (honestRow 341) := by
  intro h
  have := (ethLcAir_forces_participation_bounded h).2.2.1
  simp [honestRow, PC, CL, BL] at this

/-- ⚑ **THE CLOSED RESIDUAL, AS A REFUSAL**: `PC = 1023` against a 512-key committee. Before the
`PC_SLACK` leg this row satisfied every emitted constraint and PROVED on the deployed prover; the
participation slack `512 − 1023 = −511` is now outside `[0, 2^11)` and the row is UNSAT. -/
theorem eth_refuses_a_participation_count_above_the_committee :
    ¬ airAccepts (honestRow 1023) := by
  intro h
  have := (ethLcAir_forces_participation_bounded h).2.2.2
  simp [honestRow, PC, BL, CL] at this

/-- And the refusal is not an artifact of the ONE value a run exhibited: EVERY count above the
bitfield length is refused, for the structural reason that the slack would have to be negative. -/
theorem eth_refuses_every_over_committee_count (pc : ℤ) (h : 512 < pc) :
    ¬ airAccepts (honestRow pc) := by
  intro hacc
  have hbl := (ethLcAir_forces_participation_bounded hacc).1
  have hle := (ethLcAir_forces_participation_bounded hacc).2.2.2
  rw [hbl] at hle
  have hpc : honestRow pc PC = pc := by simp [honestRow, PC, CL, BL]
  rw [hpc] at hle
  omega

/-- Structural teeth: a 511-key committee is refused (the `= 512` gate bites). -/
theorem eth_refuses_a_511_committee (a : Assignment) (h : a CL = 511) : ¬ airAccepts a := by
  intro hacc
  have := (ethLcAir_forces_participation_bounded hacc).2.1
  omega

/-- Carrier teeth: a CLEARED (forged) BLS carrier bit is refused. -/
theorem eth_refuses_a_cleared_bls_carrier (a : Assignment) (h : a BLS_OK = 0) :
    ¬ airAccepts a := by
  intro hacc
  have := (blsC_holds_iff a).mp hacc.2.2.2.2.2.2.1
  omega

/-- Depth teeth: a finality depth of 5 is refused (wrong-depth branch fail-closure). -/
theorem eth_refuses_a_depth_5_finality_branch (a : Assignment) (h : a FL = 5) :
    ¬ airAccepts a := by
  intro hacc
  rcases (flC_holds_iff a).mp hacc.2.2.2.2.2.2.2.1 with h6 | h7 <;> omega

/-- Depth teeth: an execution depth of 3 is refused. -/
theorem eth_refuses_a_depth_3_execution_branch (a : Assignment) (h : a EL = 3) :
    ¬ airAccepts a := by
  intro hacc
  have := (elC_holds_iff a).mp hacc.2.2.2.2.2.2.2.2.2.1
  omega

/-! ## §7 — axiom hygiene. -/

#assert_axioms participants_length_le_bits
#assert_axioms eth_participation_slack_is_fillable
#assert_axioms ethLcAir_forces_participation_bounded
#assert_axioms ethLcAir_sound
#assert_axioms ethLcAir_sound_bounds_participation
#assert_axioms ethLcAir_no_forgery
#assert_axioms eth_refuses_a_participation_count_above_the_committee

#print axioms ethLcAir_complete
#print axioms ethLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientEthAir
