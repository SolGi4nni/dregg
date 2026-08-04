/-
# Dregg2.Circuit.Emit.LightClientMidnightAir — the Midnight GRANDPA VERIFY-DECISION, EMITTED AS AN AIR.

## What this file IS (the "STARK-ify the Midnight light client" slice — the Solana mirror)

`Dregg2.Bridge.LightClientMidnight` AUTHORS the Midnight GRANDPA-finality verification and proves
`mid_no_forgery` over `midVerifyDecision` — the scalar accept/reject a deployed node computes (the counted
signed authority weight, the total authority weight, the Ed25519 + authority-set carriers, the round + era
gates). That gives a node a Lean-PROVEN verdict — but rendered by running Lean on the node's own machine;
a peer (or an on-chain contract) that wants to trust "this dregg node saw Midnight finalize block B at
round R, era E" must RE-TRUST that node's execution. There is no portable object.

This file emits `midVerifyDecision` AS A DESCRIPTOR-IR-v2 AIR (`midLcVerifyDesc`), so a dregg node can
PROVE the verify-decision as a STARK: a portable artifact any peer verifies without re-running the node,
and (via the gnark FRI-wrap → Groth16 `SettlementCircuit` → `DreggPeerRegistry`, the SAME on-chain hook
the ETH/Cosmos/Solana AIRs attach to) an on-chain contract verifies. That closes the FOURTH interchain
gap — Midnight from a TRUSTED MIRROR (the observer follows the RPC's `chain_getFinalizedHead`; no
justification is verified) to a formalized, STARK-ified, PORTABLE GRANDPA-finality proof.

HOUSE LAW #1: the AIR is LEAN-AUTHORED. Rust only ingests the emitted `emitVmJson2` descriptor and runs
the generic multi-table prover over it; it never hand-writes these constraints. The refinement
`midLcAir_sound` / `midLcAir_no_forgery` is a machine-checked theorem over the EMITTED object
(`airAccepts` reads the descriptor's own gate bodies), tying acceptance to `midVerifyDecision` and hence
to `mid_no_forgery` — so a STARK satisfying this AIR CARRIES the no-forgery guarantee, modulo the two
named crypto carriers (below).

## ⚑ WHAT MIDNIGHT'S TALLY ACTUALLY IS, MEASURED: a SEAT COUNT, not a stake magnitude

Measured live against `https://rpc.mainnet.midnight.network` on **2026-08-03** (`system_chain` =
"Midnight Mainnet", `system_version` = "1.0.1-5edf8ddd"):

  * `state_call("GrandpaApi_grandpa_authorities", "0x")` SCALE-decodes to **130 entries**, each an
    `(AuthorityId[32], u64 weight)` pair. **Every weight is exactly 1, so the TOTAL AUTHORITY WEIGHT
    IS 130.** Thirteen distinct `gran` keys hold ten seats each.
  * `systemParameters_getAriadneParameters(647)` returns `dParameter = {numPermissionedCandidates:
    130, numRegisteredCandidates: 0}`, thirteen permissioned candidates all valid, and
    `candidateRegistrations: {}` — zero registered Cardano SPO candidates.
  * The `1` is not a Midnight choice, it is polkadot-sdk's: `substrate/frame/grandpa/src/lib.rs:609`
    and `:623` build the set as `validators.map(|(_, k)| (k, 1)).collect::<Vec<_>>()`, and
    `substrate/primitives/consensus/grandpa/src/lib.rs:65` declares `pub type AuthorityWeight = u64;`.

So this AIR's tally column carries a **SEAT COUNT — 130 live, seven bits — and it fits a BabyBear felt
with 24 bits to spare.** Cardano SPO delegated stake (lovelace) weights the Ariadne seat lottery
upstream, but the weight that REACHES GRANDPA, which is the number this AIR tallies, is 1 per seat.

⚠ **Therefore: limbing Midnight's tally does NOT close a live representability shortfall, and this
file does not claim it does.** Midnight COULD represent its real authority set on one column.
Tendermint (`MaxTotalVotingPower = 2^60 − 1`) and Solana (2^58.6 lamports of live stake) could NOT;
that is their modules' claim, and it is not transferable to this one. ⚠ Also NOT SOURCED: there is no
documented protocol cap on Midnight's committee size. 130 is a governance-set D-parameter, not a
bound. The only hard bound citable is the `u64` on `AuthorityWeight`.

What the limbing DOES buy, in order of what it is worth:

 1. ⚑ **THE REFUSAL STOPS DEPENDING ON THE FIELD SIZE.** This is the real payoff. The single-felt
    tooth refused the exactly-2/3 sub-quorum because `p − 1 ∉ [0, 2^29)` — a fact about `p`, FALSE at
    width 30 and catastrophically false at the 128 that shipped (below). The limbed tooth refuses it
    because a limb vector whose limbs are each `≥ 0` denotes a value `≥ 0`, and the sub-quorum's
    difference is `−1` (`LimbTally.cmp_refuses_below_threshold`, `LimbTally.emitted_chain_refuses`).
    That premise mentions no field, no modulus and no declared width — see
    `mid_quorum_refusal_is_field_independent` / `mid_positivity_refusal_is_field_independent`, which
    are quantified over EVERY limb width including the ones at which the old tooth was vacuous.
 2. **The DECLARED TYPE is `u64`, and 130 is a parameter rather than a bound.** A governance change
    to a stake-weighted committee is a config change on Midnight's side; at four 16-bit limbs it is
    not a change to this AIR at all. `midLcAir_accepts_at_the_u64_type_ceiling` (§7) proves an
    acceptance at `2^64 − 1` total weight, so the capability is exercised and not merely asserted.
 3. **Uniformity with the two siblings that genuinely need it** — one `LimbTally` chain shape, one
    set of range tables, one soundness lemma across Tendermint / Solana / Midnight.

## ⚑ THE WOUND THAT *WAS* REAL HERE, and what closed it

This descriptor shipped `bits: 128` on its range table over BabyBear (`p = 2013265921 < 2^31`), so a
128-bit interval contained the WHOLE FIELD and both lookups refused nothing
(`RangeFieldContainment.range_vacuous_at_or_above_31`). BOTH of its floors then failed CONCRETELY,
on the same admitted element `p − 1 = 2013265920`:

  * `WDIFF = 3·SIGNED_WEIGHT − 2·TOTAL_WEIGHT − 1` fills to `−1` at EXACTLY 2/3 — **the sub-quorum
    GRANDPA's strict threshold exists to reject passed**;
  * `TPOS = TOTAL_WEIGHT − 1` fills to `−1` at `total = 0` — **the EMPTY AUTHORITY SET passed its own
    emptiness floor.**

Narrowing to 29 (the maximum wrap-free width) fixed both, and that repair is what this change
INHERITS rather than replaces: `mid_exactly_two_thirds_was_admitted_at_128` and
`mid_both_floors_filled_the_admitted_element` are kept as the historical record of the defect, and
the two refusals that answer them are now the limbed ones, which do not mention `p`.

⚑ **WHAT THIS RE-AUTHORING DELETED, said out loud.** The 29-bit `rangeTableDef` DECLARATION IS GONE
from the descriptor. After both comparisons became limbed chains, NOTHING queried it — Midnight has
no time-window slacks (its Tendermint sibling keeps the 29-bit table for exactly those), so a
retained declaration would have been a table nothing looks up, which is the shape this repo treats as
worse than absent. The theorems that were ABOUT that interval (`mid_range_is_inside_the_field`,
`mid_wrapped_slack_is_outside_the_range`, `mid_honest_supermajority_slack_is_admitted`,
`mid_inRange_iff_mem_rangeRows`, and the two single-felt `*_fills_to_minus_one_*` gate lemmas) are
retired, and their CONTENT is replaced by strictly stronger statements about the emitted chains:
`mid_quorum_refusal_is_field_independent`, `mid_positivity_refusal_is_field_independent`,
`midLcAir_refuses_the_empty_authority_set`, `midLcAir_refuses_exactly_two_thirds` — each of which
says what the retired pair said, without the field-size premise that made the old pair fragile.

**Flag day:** trace width `20 → 42`, PI count unchanged at 12, constraint count `20 → 52`, declared
tables `[range@29] → [range_w16@85, range_w8@77]`. The descriptor bytes, and therefore the VK, change.
`circuit/descriptors/by-name/dregg-midnight-lightclient-verify-v1.json` is re-emitted from this
module; `circuit/descriptors/PROVENANCE.json`'s `by_name_sha256` entry needs refreshing with it.

## The crypto boundary: IN-AIR logic vs NAMED verified carriers

  * IN-AIR (arithmetic gates over the trace — the weight TALLY logic, the Nomad-class bug locus):
      - the STRICT > 2/3 supermajority `3·signed > 2·total` as a LIMBED difference chain
        `WDIFF = 3·SIGNED_WEIGHT − 2·TOTAL_WEIGHT − 1 ≥ 0` (GRANDPA's `threshold`) — five generated
        gates over four rungs, thirteen 16-bit limb lookups and four 8-bit carry lookups. An
        EXACTLY-2/3 commit makes the difference `−1`, which no vector of non-negative limbs denotes;
      - the empty-set floor `total > 0` as a SECOND limbed chain `TPOS = TOTAL_WEIGHT − 1 ≥ 0`
        (`α = 1, β = 0, γ = 1`) over the SAME four total-weight limb columns;
      - the ROUND binding (`ROUND_OK = 1` — cross-round) and the ERA binding (`ERA_OK = 1` —
        stale-authority-set) as forced boolean gates.
  * NAMED verified CARRIERS (witnessed boolean columns, forced `= 1`):
      - `ED_OK`      — the aggregate Ed25519 verify over the counted authorities + the precommit message
        `(targetHash, targetNumber, round, setId)`,
      - `AUTHSET_OK` — the derived authority set binds to the pinned WS anchor root (the
        denominator-shrink pin).

The residual is HONEST and NAMED: in THIS slice the two crypto carriers are asserted, not re-derived
in-circuit, so the STARK proves the TALLY/THRESHOLD/ROUND/ERA LOGIC is correct GIVEN the Ed25519 and
authority-set results — precisely `midVerifyDecision`'s guarantee, now portable. Putting Ed25519 and the
authority-set fold in-AIR (or as their own verified sub-proofs the AIR `ProofBind`s against) is the next
iteration; the public-input anchors below are the hook it attaches to. Also named: the counted
`SIGNED_WEIGHT` distinct-authority tally is a trusted projection (the deployed node's tally), the same
posture as the ETH `PC` / Solana `ROOTED_STK` participant count.

## Public inputs (the addressing layer — what the proof is ABOUT)

`PI[0]    = ANCHOR_ROOT`       — the pinned WS authority-set root (the governance trust anchor the
                              AUTHSET_OK carrier is a compare against). The trust root the proof is
                              relative to.
`PI[1..9] = TARGET_ROOT[0..8]` — the claimed finalized block/state hash B (what a proof-of-holdings
                              later opens against): the FULL 256-bit target root exposed as its NINE
                              radix-`2^31`, MOST-SIGNIFICANT-limb-first limbs (`⌈256/31⌉ = 9`; the top
                              limb carries the residual 8 bits). FELT-WIDTH CLOSE: the earlier single
                              anchor felt bound only a 31-bit PROJECTION of the target root (two
                              256-bit roots agreeing in 31 bits both verified — a soundness gap at the
                              peer-wrap boundary); nine PI-bound limbs bind the WHOLE root, recomposed
                              by the peer-wrap's radix-`2^31` MSB-first pack before its 128-bit split.
`PI[10]   = ROUND`            — the GRANDPA round R the commit is for.
`PI[11]   = ERA`             — the authority-set id (era) E the finality is claimed under (the ERA_OK
                              gate binds the counted precommits + the anchored set id to this).

These ride as published witness columns pinned to the public inputs (`.piBinding`). NOT-YET-CLOSED
(named residual, identical to the other slices, UNCHANGED by the limbing): the anchors are published
but not yet arithmetically bound to the carrier bits (that binding IS the in-AIR-crypto iteration —
`ED_OK` derived from the precommit message built on `TARGET_ROOT`+`ROUND`+`ERA`, `AUTHSET_OK` derived
from the set fold into `ANCHOR_ROOT`).

## The mod-`p` ↔ `ℤ` reading

`airAccepts` reads the emitted gate bodies as `ℤ` equalities. For the two limbed chains that reading
is BRIDGED rather than merely named: `LimbTally.rung_no_alias_at_deployed_constants` (quorum,
`α = 3, β = 2`) and `mid_tpos_rung_no_alias_at_deployed_constants` (positivity, `α = 1, β = 0`) bound
every rung gate's `ℤ` image, on any assignment respecting the DECLARED 16-bit limb and 8-bit carry
ranges, strictly inside `(−p, p)` — so a body that is `0 mod p` there IS `0` over `ℤ` and
`LimbTally.chain_recomposes` transfers to the deployed denotation.

## Axiom hygiene
Definitional descriptor + non-vacuous per-gate `iff` lemmas (`omega`) + the load-bearing
`midLcAir_sound` / `midLcAir_no_forgery` refinement to `midVerifyDecision` / `mid_no_forgery`.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.RangeFieldContainment
import Dregg2.Circuit.LimbTally
import Dregg2.Bridge.LightClientMidnight

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Dregg2.Circuit.Emit.LightClientMidnightAir

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId TableDef rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Bridge.LightClientMidnight

/-! ## §1 — the trace column layout (one logical row).

Columns 0..3 are the four boolean verify-logic projections `midVerifyDecision` composes over (two of
them crypto carriers). Columns 4..29 are the LIMBED TALLY BLOCK: the two `u64`-wide weights, the two
difference vectors of the two comparisons, and their borrow chains. Columns 30..41 are the published
PUBLIC anchors: `ANCHOR_ROOT` (30), the NINE target-root limbs `TARGET_ROOT 0..8` (cols 31..39 — the
full 256-bit target root, radix-`2^31`, MSB-first), `ROUND_COL` (40) and `ERA_COL` (41). -/

/-- **CARRIER** — the aggregate Ed25519 verify RESULT (counted authorities signed the precommit message);
forced `= 1`. NAMED verified-FFI carrier. Witness. -/
def ED_OK : Nat := 0
/-- **CARRIER** — the authority-set-root compare RESULT (derived set binds the pinned WS anchor root);
forced `= 1`. NAMED carrier (the denominator-shrink pin). Witness. -/
def AUTHSET_OK : Nat := 1
/-- **CARRIER** — the ROUND-binding RESULT (every counted precommit names the claimed round R —
cross-round); forced `= 1`. Witness.
⚠ **CORRECTED 2026-08-04 — this was labelled GATE and it is the same `x − 1` shape as the two
admitted carriers.** Its gate names column 2 and nothing else; the PUBLISHED round is column 49 and
is read by no gate and no lookup, so nothing relates the bit to the round it is named after. A prover
publishes any round and writes 1 here. `LightClientAnchorConnectivity.mid_round_and_era_bits_are_-
not_joined_to_the_published_round_and_era` is that measured on the emitted object. -/
def ROUND_OK : Nat := 2
/-- **CARRIER** — the ERA-binding RESULT (the claimed set id equals the anchored era AND every counted
precommit carries it — stale-authority-set); forced `= 1`. Witness.
⚠ Same correction as `ROUND_OK`: the bit is column 3, the published era is column 50, and they share
no constraint. There is no stale-authority-set refusal in the emitted object. -/
def ERA_OK : Nat := 3

/-! ### ⚑ THE TALLY, AS A LIMB VECTOR.

`TOTAL_WEIGHT` and `SIGNED_WEIGHT` used to be ONE COLUMN EACH, and — unlike this AIR's Tendermint and
Solana siblings — that was ADEQUATE for the live chain: Midnight's GRANDPA authority weights are all
`1` and the measured total is `130` (module header, measured 2026-08-03). The reason they are limbed
anyway is stated at the top and is NOT a live shortfall: the refusal stops depending on the field
size, the declared wire type is `u64` rather than 130, and the three peer-chain clients share one
comparison shape.

Four 16-bit limbs are exactly a `u64` — exactly `AuthorityWeight`'s declared type
(`substrate/primitives/consensus/grandpa/src/lib.rs:65`). The arithmetic and its soundness live in
`Dregg2.Circuit.LimbTally`. -/

/-- The tally limb width. `MID_TALLY_LIMBS · MID_LIMB_BITS = 64`. -/
def MID_LIMB_BITS : Nat := LimbTally.TALLY_LIMB_BITS
/-- The number of tally limbs — four 16-bit limbs are a `u64`. -/
def MID_TALLY_LIMBS : Nat := LimbTally.TALLY_LIMBS
/-- The carry width for both difference chains (the prover's own byte bus). -/
def MID_CARRY_BITS : Nat := LimbTally.TALLY_CARRY_BITS

/-- **Limb `i` of the TOTAL authority weight** (`totalWeight`), LSB-first. Columns 4..7. This is the
`> 2/3` denominator AND the operand of the emptiness floor — one set of columns, two comparisons.
Witness. -/
def TOTAL_WEIGHT_LIMB (i : Nat) : Nat := 4 + i
/-- **Limb `i` of the COUNTED SIGNED authority weight** (`signedWeight`), LSB-first. Columns 8..11.
Its Ed25519 provenance is the `ED_OK` carrier. Witness. -/
def SIGNED_WEIGHT_LIMB (i : Nat) : Nat := 8 + i
/-- **Limb `i` of the strict `>2/3` quorum DIFFERENCE `3·signedWeight − 2·totalWeight − 1`**,
LSB-first. FIVE limbs (columns 12..16), one more than the operands: `3·A` needs two bits beyond `A`.
Every limb carries its own 16-bit range lookup, and THAT is the quorum tooth — a limb vector of
non-negative limbs denotes a non-negative value, so a sub-quorum (whose difference is negative) has
no representation at all. -/
def WDIFF_LIMB (i : Nat) : Nat := 12 + i
/-- **Offset carry `i` of the quorum difference chain** (columns 17..20); denotes `col − 128`, since a
difference chain BORROWS and a field wire has no sign. Range-checked at 8 bits for the mod-`p` bridge
ONLY — `LimbTally.chain_recomposes` needs no bound on it whatsoever. -/
def WDIFF_CARRY (i : Nat) : Nat := 17 + i
/-- **Limb `i` of the EMPTY-SET FLOOR difference `totalWeight − 1`**, LSB-first. Five limbs (columns
21..25). Its non-negativity is `total ≥ 1` — the floor the 128-bit table admitted `total = 0`
through. -/
def TPOS_LIMB (i : Nat) : Nat := 21 + i
/-- **Offset carry `i` of the emptiness-floor chain** (columns 26..29), same `−128` offset. -/
def TPOS_CARRY (i : Nat) : Nat := 26 + i

/-! ### ⚑⚑ THE THIRD CHAIN, ADDED 2026-08-03 — a relation NO GATE FORCED.

The two chains above force `3·signedWeight − 2·totalWeight − 1 ≥ 0` and `totalWeight − 1 ≥ 0`. Read
the leg list: those were the ONLY comparisons. **Nothing related the two tallies to each other.**
`TOTAL_WEIGHT_LIMB` and `SIGNED_WEIGHT_LIMB` are independent witnessed limb vectors carrying only
their own 16-bit lookups, and the quorum tooth gets *easier* as `signedWeight` grows — so a row
claiming a signed authority weight ABOVE the total satisfied every emitted constraint. `(total,
signed) = (3, 100)` passes the quorum (`293 ≥ 0`) and the floor (`2 ≥ 0`) and PROVED.

That is the Midnight instance of the class the ETH light client's `PC = 1023`-of-512 belonged to
(`dfa434d46`), and it is closed the same way — but not with eth's one column, because these counts
are `u64` limb VECTORS: a third `LimbTally` chain at `α = 1, β = 1, γ = 0`, whose difference is
`totalWeight − signedWeight` and whose non-negativity IS `signedWeight ≤ totalWeight`. -/

/-- **Limb `i` of the ORDERING difference `totalWeight − signedWeight`**, LSB-first. Five limbs
(columns 30..34). Its non-negativity is `signedWeight ≤ totalWeight` — the relation nothing forced. -/
def SLE_LIMB (i : Nat) : Nat := 30 + i
/-- **Offset carry `i` of the ordering chain** (columns 35..38), same `−128` offset. -/
def SLE_CARRY (i : Nat) : Nat := 35 + i

/-- **PUBLIC ANCHOR** — the pinned WS authority-set root (the governance trust anchor). PI-bound. -/
def ANCHOR_ROOT : Nat := 39

/-- The number of ~31-bit limbs the FULL 256-bit finalized target root is exposed as: `⌈256 / 31⌉ = 9`.
Eight 31-bit limbs cover 248 bits; the ninth (most-significant) limb carries the remaining 8 bits. This
is the felt-width close — a SINGLE anchor felt bound only a 31-bit PROJECTION of the 256-bit target root
(two roots agreeing in 31 bits both verified); nine limbs bind the WHOLE root. -/
def TARGET_ROOT_LIMBS : Nat := 9

/-- **PUBLIC ANCHOR (limb `i`)** — the claimed finalized block/state root B as its radix-`2^31`,
MOST-SIGNIFICANT-limb-first decomposition. Limb `i` is trace column `31 + i` (cols 31..39); limb `0` is
the MSB (its top carries only 8 bits). PI-bound to slot `1 + i`, so the peer-wrap's radix-`2^31`
MSB-first pack over `PI[1..9]` recomposes the 256-bit target root exactly before its 128-bit split. -/
def TARGET_ROOT (i : Nat) : Nat := 40 + i

/-- **PUBLIC ANCHOR** — the GRANDPA round R. PI-bound. -/
def ROUND_COL : Nat := 40 + TARGET_ROOT_LIMBS
/-- **PUBLIC ANCHOR** — the authority-set id (era) E. PI-bound. -/
def ERA_COL : Nat := 41 + TARGET_ROOT_LIMBS

/-- Total main-trace width: 4 boolean logic columns + 4 total-weight limbs + 4 signed-weight limbs +
5 quorum-difference limbs + 4 quorum carries + 5 floor-difference limbs + 4 floor carries + 5
ORDERING-difference limbs + 4 ordering carries + 1 anchor-root + 9 target-root limbs + round + era
= 51.

⚑ It was 20, then 42, and it is now 51. The +22 was the two comparisons becoming limbed chains; this
+9 is the THIRD comparison, `signedWeight ≤ totalWeight`, which no gate forced at all. On Midnight —
unlike its two siblings — the limbing was NOT the price of representing the live authority set (130
fit one column); it was the price of a refusal whose premises do not mention the field. This nine is
different: it is a check that was ABSENT, at any width. -/
def MID_LC_WIDTH : Nat := 51

/-- PI slot 0: the pinned WS anchor root. -/
def PI_ANCHOR_ROOT : Nat := 0
/-- PI slot of target-root limb `i` (slots 1..9), MSB-first. -/
def PI_TARGET_ROOT (i : Nat) : Nat := 1 + i
/-- PI slot of the GRANDPA round (slot 10). -/
def PI_ROUND : Nat := 1 + TARGET_ROOT_LIMBS
/-- PI slot of the authority-set id / era (slot 11). -/
def PI_ERA : Nat := 2 + TARGET_ROOT_LIMBS
/-- Number of public inputs: anchor root + 9 target-root limbs + round + era. -/
def PI_COUNT : Nat := 12

/-! ## §2 — the emitted gate bodies (the descriptor's OWN constraint polynomials).

### ⚑ The two comparisons, GENERATED rather than transcribed.

`LightClientMinaAir` set the bar — `EffectLower.lowerAir`-authored, no hand-written `VmConstraint2`.
Each comparison used to be ONE hand-written gate body plus ONE lookup, because a single-felt slack is
one gate. A limbed comparison is five gates and thirteen-plus lookups, and hand-writing those would be
exactly the drift House Law #1 exists to stop. `LimbTally.chainBodies` GENERATES them from the rung
list and `LimbTally.chainBodies_zero_iff` ties what it generates back to `ChainOk`, so §5's soundness
is about the bodies that SHIP. -/

/-- **The four rungs of the QUORUM difference chain**, LSB-first: at radix position `i` the
signed-weight limb, the total-weight limb, the difference limb and the offset carry out. `α = 3` on
signed weight, `β = 2` on total weight, `γ = 1` for GRANDPA's STRICT `>2/3`.

Written as an explicit literal (rather than `List.range`-mapped) so the byte-golden `#guard` reduces
to the exact wire string with no fold — the same discipline `targetRootPins` follows. -/
def wDiffRungs : List LimbTally.Rung :=
  [ ⟨SIGNED_WEIGHT_LIMB 0, TOTAL_WEIGHT_LIMB 0, WDIFF_LIMB 0, WDIFF_CARRY 0⟩
  , ⟨SIGNED_WEIGHT_LIMB 1, TOTAL_WEIGHT_LIMB 1, WDIFF_LIMB 1, WDIFF_CARRY 1⟩
  , ⟨SIGNED_WEIGHT_LIMB 2, TOTAL_WEIGHT_LIMB 2, WDIFF_LIMB 2, WDIFF_CARRY 2⟩
  , ⟨SIGNED_WEIGHT_LIMB 3, TOTAL_WEIGHT_LIMB 3, WDIFF_LIMB 3, WDIFF_CARRY 3⟩ ]

/-- The quorum difference vector's TOP limb — the chain's closure column. -/
def WDIFF_TOP : Nat := WDIFF_LIMB 4

/-- **The four rungs of the EMPTY-SET FLOOR chain**, LSB-first. `α = 1, β = 0, γ = 1`, i.e. the
emitted difference is `1·TOTAL_WEIGHT − 0·(…) − 1 = totalWeight − 1`.

⚠ **`bCol` POINTS AT THE SAME COLUMN AS `aCol`, AND THAT IS DELIBERATE, NOT A TYPO.** `LimbTally.Rung`
carries a `bCol` at every rung because the general shape is `α·A − β·B − γ`; this comparison has no
right operand. At `β = 0` the generated term is `.mul (.const 0) (.var bCol)`, which contributes
nothing to any gate and nothing to `LimbTally.cmp_sound`'s conclusion — that conclusion reads
`γ ≤ α·A − 0·B = α·A`, with `B` free. Pointing `bCol` at the total-weight limb (rather than at a
dedicated zero column) keeps the trace 4 columns narrower and adds no constraint; the alternative
would be four columns whose only job is to be multiplied by zero. -/
def tPosRungs : List LimbTally.Rung :=
  [ ⟨TOTAL_WEIGHT_LIMB 0, TOTAL_WEIGHT_LIMB 0, TPOS_LIMB 0, TPOS_CARRY 0⟩
  , ⟨TOTAL_WEIGHT_LIMB 1, TOTAL_WEIGHT_LIMB 1, TPOS_LIMB 1, TPOS_CARRY 1⟩
  , ⟨TOTAL_WEIGHT_LIMB 2, TOTAL_WEIGHT_LIMB 2, TPOS_LIMB 2, TPOS_CARRY 2⟩
  , ⟨TOTAL_WEIGHT_LIMB 3, TOTAL_WEIGHT_LIMB 3, TPOS_LIMB 3, TPOS_CARRY 3⟩ ]

/-- The floor difference vector's TOP limb — that chain's closure column. -/
def TPOS_TOP : Nat := TPOS_LIMB 4

/-- ⚑ **The four rungs of the ORDERING chain** — `α = 1` on TOTAL weight, `β = 1` on SIGNED weight,
`γ = 0`, i.e. the emitted difference is `totalWeight − signedWeight`.

⚠ The operands are SWAPPED relative to `wDiffRungs`: `aCol` is the total-weight limb here and the
signed-weight limb there, because `LimbTally.cmp_sound` concludes `γ ≤ α·A − β·B` and the relation
wanted is `0 ≤ total − signed`. The two chains therefore read the SAME eight operand columns in the
opposite order, which is what makes them two teeth on ONE pair of tallies rather than two spellings
of one (`mid_ordering_reads_the_quorum_operands`). -/
def sleRungs : List LimbTally.Rung :=
  [ ⟨TOTAL_WEIGHT_LIMB 0, SIGNED_WEIGHT_LIMB 0, SLE_LIMB 0, SLE_CARRY 0⟩
  , ⟨TOTAL_WEIGHT_LIMB 1, SIGNED_WEIGHT_LIMB 1, SLE_LIMB 1, SLE_CARRY 1⟩
  , ⟨TOTAL_WEIGHT_LIMB 2, SIGNED_WEIGHT_LIMB 2, SLE_LIMB 2, SLE_CARRY 2⟩
  , ⟨TOTAL_WEIGHT_LIMB 3, SIGNED_WEIGHT_LIMB 3, SLE_LIMB 3, SLE_CARRY 3⟩ ]

/-- The ordering difference vector's TOP limb — that chain's closure column. -/
def SLE_TOP : Nat := SLE_LIMB 4

/-- The emitted QUORUM gate bodies: five from four rungs (one per rung plus the closure gate). -/
def wDiffChainBodies : List EmittedExpr :=
  LimbTally.chainBodies MID_LIMB_BITS 3 2 1 LimbTally.TALLY_CARRY_OFF WDIFF_TOP wDiffRungs

/-- The emitted EMPTY-SET FLOOR gate bodies: five from four rungs. -/
def tPosChainBodies : List EmittedExpr :=
  LimbTally.chainBodies MID_LIMB_BITS 1 0 1 LimbTally.TALLY_CARRY_OFF TPOS_TOP tPosRungs

/-- The emitted ORDERING gate bodies (`signedWeight ≤ totalWeight`): five from four rungs. -/
def sleChainBodies : List EmittedExpr :=
  LimbTally.chainBodies MID_LIMB_BITS 1 1 0 LimbTally.TALLY_CARRY_OFF SLE_TOP sleRungs

/-- `ED_OK − 1` — zero iff the Ed25519 carrier bit is set. -/
def edBody : EmittedExpr := .add (.var ED_OK) (.const (-1))
/-- `AUTHSET_OK − 1` — zero iff the authority-set-root carrier bit is set. -/
def authsetBody : EmittedExpr := .add (.var AUTHSET_OK) (.const (-1))
/-- `ROUND_OK − 1` — zero iff the round-binding gate bit is set. -/
def roundBody : EmittedExpr := .add (.var ROUND_OK) (.const (-1))
/-- `ERA_OK − 1` — zero iff the era-binding gate bit is set. -/
def eraBody : EmittedExpr := .add (.var ERA_OK) (.const (-1))

/-! ## §3 — the constraint list + descriptor.

### The two declared range tables, and the one that is GONE.

Both comparisons now ride limbs at 16 bits with carries at 8, on WIDTH-TAGGED CUSTOM tables
(`rangeTidW b = .custom (RANGE_W_TID_BASE + b)`, `RANGE_W_TID_BASE = 64`) — the same mechanism the
deployed availability-weld uses for its 15-bit borrow limbs. The Rust side resolves each lookup's
width from the DECLARED table (`descriptor_ir2.rs` `range_bits_for`), realizes every width as the
same byte-limb decomposition, and shares ONE byte table across all of them.

⚑ The 29-bit `rangeTableDef` this descriptor used to declare is NOT declared any more. Its only two
consumers were the single-felt quorum and positivity slacks, both of which are chains now; Midnight
carries no time-window slacks (its Tendermint sibling keeps its 29-bit table for exactly those). A
declared-but-unqueried table is a claim about a check nothing performs. -/

/-- The tally-limb range table: wire id `5 + 64 + 16 = 85`. -/
def TID_TALLY_LIMB : TableId := .custom (64 + MID_LIMB_BITS)
/-- The chain-carry range table: wire id `5 + 64 + 8 = 77`. -/
def TID_TALLY_CARRY : TableId := .custom (64 + MID_CARRY_BITS)

/-! ### ⚑ THE FIVE LIMBED QUANTITIES, AS `EffectAirIR` LEGS — the teeth are the COMPILER's output.

⚑ **THIS BLOCK USED TO BE A HAND-WRITTEN `List VmConstraint2`** — twenty-six literal `.lookup`s that
agreed with the leg shapes by inspection and by nothing else. It is now `EffectLower.lowerLimbsLeg`
output, the same path the Tendermint and Mina siblings take, so there is ONE road from source to
constraints rather than a source language plus a transcription. The emitted bytes for the six
pre-existing quantities are UNCHANGED — `lowerLimbsLeg` emits exactly `cols.map (fun c => .lookup
⟨table, [.var c]⟩)` in declaration order — so this is a routing change, not a wire change.

⚑ And it makes the IR's width verdict LOAD-BEARING on the deployed descriptor:
`LimbsLeg.mainRailOk` refuses an empty limb vector (which would denote `0` and check nothing) and any
limb width above the wrap-free ceiling 29 — the class this descriptor SHIPPED IN at 128 bits.
`mid_tally_legs_are_expressible` is that verdict, `decide`d. -/

/-- The total authority weight as a limbed quantity: four 16-bit limbs, LSB-first. -/
def totalWeightLeg : EffectAirIR.LimbsLeg :=
  { cols := [TOTAL_WEIGHT_LIMB 0, TOTAL_WEIGHT_LIMB 1, TOTAL_WEIGHT_LIMB 2, TOTAL_WEIGHT_LIMB 3]
  , bits := MID_LIMB_BITS, table := TID_TALLY_LIMB }

/-- The counted signed authority weight as a limbed quantity. -/
def signedWeightLeg : EffectAirIR.LimbsLeg :=
  { cols := [SIGNED_WEIGHT_LIMB 0, SIGNED_WEIGHT_LIMB 1, SIGNED_WEIGHT_LIMB 2, SIGNED_WEIGHT_LIMB 3]
  , bits := MID_LIMB_BITS, table := TID_TALLY_LIMB }

/-- ⚑ The QUORUM difference — FIVE limbs, load-bearing: its containment forces `3·S − 2·T − 1 ≥ 0`. -/
def wDiffLeg : EffectAirIR.LimbsLeg :=
  { cols := [WDIFF_LIMB 0, WDIFF_LIMB 1, WDIFF_LIMB 2, WDIFF_LIMB 3, WDIFF_LIMB 4]
  , bits := MID_LIMB_BITS, table := TID_TALLY_LIMB }

/-- The quorum chain's offset carries. ⚠ NOT part of the threshold argument — they exist solely for
the mod-`p` ↔ `ℤ` bridge (`LimbTally.chain_recomposes` needs no carry bound at all). -/
def wDiffCarryLeg : EffectAirIR.LimbsLeg :=
  { cols := [WDIFF_CARRY 0, WDIFF_CARRY 1, WDIFF_CARRY 2, WDIFF_CARRY 3]
  , bits := MID_CARRY_BITS, table := TID_TALLY_CARRY }

/-- ⚑ The EMPTY-SET FLOOR difference — FIVE limbs; its containment forces `T − 1 ≥ 0`. -/
def tPosLeg : EffectAirIR.LimbsLeg :=
  { cols := [TPOS_LIMB 0, TPOS_LIMB 1, TPOS_LIMB 2, TPOS_LIMB 3, TPOS_LIMB 4]
  , bits := MID_LIMB_BITS, table := TID_TALLY_LIMB }

/-- The floor chain's offset carries. -/
def tPosCarryLeg : EffectAirIR.LimbsLeg :=
  { cols := [TPOS_CARRY 0, TPOS_CARRY 1, TPOS_CARRY 2, TPOS_CARRY 3]
  , bits := MID_CARRY_BITS, table := TID_TALLY_CARRY }

/-- ⚑ The ORDERING difference — FIVE limbs; its containment forces `T − S ≥ 0`, the relation this
descriptor did not have. -/
def sleLeg : EffectAirIR.LimbsLeg :=
  { cols := [SLE_LIMB 0, SLE_LIMB 1, SLE_LIMB 2, SLE_LIMB 3, SLE_LIMB 4]
  , bits := MID_LIMB_BITS, table := TID_TALLY_LIMB }

/-- The ordering chain's offset carries. -/
def sleCarryLeg : EffectAirIR.LimbsLeg :=
  { cols := [SLE_CARRY 0, SLE_CARRY 1, SLE_CARRY 2, SLE_CARRY 3]
  , bits := MID_CARRY_BITS, table := TID_TALLY_CARRY }

/-- ⚑ **THE TEETH: one range lookup PER LIMB, for ALL THREE comparisons.**

Twenty-three 16-bit lookups (four total-weight limbs, four signed-weight limbs, five
quorum-difference, five floor-difference, five ORDERING-difference) and twelve 8-bit carry lookups.
The load-bearing ones are the FIFTEEN on the three differences: they are what force
`3·signed − 2·total − 1 ≥ 0`, `total − 1 ≥ 0` and `total − signed ≥ 0`, because a limb vector of
non-negative limbs denotes a non-negative value (`LimbTally.limbValue_nonneg`).

⚠ The eight OPERAND lookups are not part of that argument (`LimbTally.cmp_sound` does not use them);
they are there for the mod-`p` ↔ `ℤ` bridge (`LimbTally.rung_no_alias_at_deployed_constants`,
`mid_tpos_rung_no_alias_at_deployed_constants`, `mid_sle_rung_no_alias_at_deployed_constants`), which
needs every limb in `[0, 2^16)`. Two different jobs, said apart rather than blurred. The floor and
ordering chains query NO operand lookups of their own — their operands ARE the two weight vectors,
already checked once. -/
def tallyRangeLookups : List VmConstraint2 :=
  EffectLower.lowerLimbsLeg totalWeightLeg ++ EffectLower.lowerLimbsLeg signedWeightLeg
    ++ EffectLower.lowerLimbsLeg wDiffLeg ++ EffectLower.lowerLimbsLeg wDiffCarryLeg
    ++ EffectLower.lowerLimbsLeg tPosLeg ++ EffectLower.lowerLimbsLeg tPosCarryLeg
    ++ EffectLower.lowerLimbsLeg sleLeg ++ EffectLower.lowerLimbsLeg sleCarryLeg

/-- The generated QUORUM gates, wrapped into the target's constraint constructor. GENERATED — there
is no hand-written `VmConstraint2` in this block. -/
def wDiffChainGates : List VmConstraint2 :=
  wDiffChainBodies.map (fun b => .base (.gate b))

/-- The generated EMPTY-SET FLOOR gates. Also generated, from the same `LimbTally.chainBodies`. -/
def tPosChainGates : List VmConstraint2 :=
  tPosChainBodies.map (fun b => .base (.gate b))

/-- The generated ORDERING gates (`signedWeight ≤ totalWeight`). Also `LimbTally.chainBodies` output. -/
def sleChainGates : List VmConstraint2 :=
  sleChainBodies.map (fun b => .base (.gate b))

def edGate : VmConstraint2 := .base (.gate edBody)
def authsetGate : VmConstraint2 := .base (.gate authsetBody)
def roundGate : VmConstraint2 := .base (.gate roundBody)
def eraGate : VmConstraint2 := .base (.gate eraBody)
/-- Published-anchor pin: the pinned WS anchor root is `PI[0]`. -/
def anchorRootPin : VmConstraint2 :=
  .base (.piBinding VmRow.first ANCHOR_ROOT PI_ANCHOR_ROOT)
/-- Published-anchor pins: the NINE finalized-target-root limbs are `PI[1..9]` (MSB-first). Each limb
rides its own PI slot, so the peer-wrap's radix-`2^31` pack over `PI[1..9]` recovers the FULL 256-bit
target root — not a 31-bit projection. Written as an explicit literal (limb `i` → col `31+i` → PI `1+i`)
so the byte-golden `#guard` reduces to the exact wire string with no fold. -/
def targetRootPins : List VmConstraint2 :=
  [ .base (.piBinding VmRow.first (TARGET_ROOT 0) (PI_TARGET_ROOT 0))
  , .base (.piBinding VmRow.first (TARGET_ROOT 1) (PI_TARGET_ROOT 1))
  , .base (.piBinding VmRow.first (TARGET_ROOT 2) (PI_TARGET_ROOT 2))
  , .base (.piBinding VmRow.first (TARGET_ROOT 3) (PI_TARGET_ROOT 3))
  , .base (.piBinding VmRow.first (TARGET_ROOT 4) (PI_TARGET_ROOT 4))
  , .base (.piBinding VmRow.first (TARGET_ROOT 5) (PI_TARGET_ROOT 5))
  , .base (.piBinding VmRow.first (TARGET_ROOT 6) (PI_TARGET_ROOT 6))
  , .base (.piBinding VmRow.first (TARGET_ROOT 7) (PI_TARGET_ROOT 7))
  , .base (.piBinding VmRow.first (TARGET_ROOT 8) (PI_TARGET_ROOT 8)) ]
/-- Published-anchor pin: the GRANDPA round is `PI[10]`. -/
def roundPin : VmConstraint2 :=
  .base (.piBinding VmRow.first ROUND_COL PI_ROUND)
/-- Published-anchor pin: the era (set id) is `PI[11]`. -/
def eraPin : VmConstraint2 :=
  .base (.piBinding VmRow.first ERA_COL PI_ERA)

/-- **`midLcVerifyDesc`** — the Midnight GRANDPA verify-decision as an emitted IR-v2 AIR. PIs
`[anchor_root, target_root[0..8], round, era]` (12 total — the finalized target root is the FULL
256-bit value as nine radix-`2^31` MSB-first limbs, not a 31-bit projection); the two `u64`-wide
tallies as limb vectors, the two comparisons as generated difference chains, the two crypto results
as carrier bits. Two declared range tables (16-bit limbs, 8-bit carries) and NO felt-wide range
table — nothing queries one any more. -/
def midLcVerifyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-midnight-lightclient-verify::v1"
  , traceWidth  := MID_LC_WIDTH
  , piCount     := PI_COUNT
  , tables      := [⟨TID_TALLY_LIMB,  "range_w16", 1, .rangeLimb MID_LIMB_BITS⟩
                   , ⟨TID_TALLY_CARRY, "range_w8",  1, .rangeLimb MID_CARRY_BITS⟩]
  , constraints := tallyRangeLookups ++ wDiffChainGates ++ tPosChainGates ++ sleChainGates
                   ++ [edGate, authsetGate, roundGate, eraGate, anchorRootPin]
                   ++ targetRootPins ++ [roundPin, eraPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3b — ⚑ THE HISTORICAL DEFECT, and the refusal that replaced its repair.

`RANGE_BITS = 128` over BabyBear contained the whole field, so BOTH floors were satisfied by every
assignment. The two theorems below EXHIBIT the admitted element; the two after them are what now
refuses it — and they are quantified over every limb width, because they do not mention `p` at all. -/

/-- ⚑ **THE ADMITTED VALUE, EXHIBITED — the quorum floor.** `2013265920` is `p − 1`, the deployed
encoding of the strict-quorum slack `WDIFF = −1` that an EXACTLY-2/3 commit fills (e.g. `signed = 2`
of `total = 3`, or `86` of `129`, §7). The shipped 128-bit table CONTAINED it, so GRANDPA's strict
threshold accepted a sub-quorum. -/
theorem mid_exactly_two_thirds_was_admitted_at_128 :
    ([2013265920] : List ℤ) ∈ rangeRows 128 := by
  rw [range_row_mem_iff]; norm_num

/-- ⚑ **…AND IT WAS THE SAME ELEMENT FOR BOTH FLOORS.** The quorum slack `3·signed − 2·total − 1` at
EXACTLY 2/3 (86 of 129) and the emptiness slack `total − 1` at `total = 0` BOTH fill to `−1`, and
`−1`'s deployed encoding is exactly the `p − 1` the theorem above exhibits inside `[0, 2^128)`. Two
independent floors, one admitted value: the strict threshold accepted a sub-quorum and the emptiness
floor accepted the empty set, through the same hole. -/
theorem mid_both_floors_filled_the_admitted_element :
    (3 * 86 - 2 * 129 - 1 : ℤ) = -1
      ∧ ((0 : ℤ) - 1) = -1
      ∧ Dregg2.Circuit.Emit.EffectLower.P - 1 = (2013265920 : ℤ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num [Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- ⚑ **THE QUORUM REFUSAL, AND IT NO LONGER MENTIONS THE FIELD.** If the true weights fail the
strict `>2/3` threshold, NO assignment satisfies the emitted quorum chain together with the
difference-limb containment — for EVERY limb width, including the widths at which the single-felt
tooth was vacuous.

The retired tooth refused the sub-quorum because `p − 1 ∉ [0, 2^29)`: a fact about the FIELD SIZE,
false at 30 and catastrophically false at the 128 that shipped. This one refuses it because a limb
vector of non-negative limbs denotes a non-negative value and the difference is negative. -/
theorem mid_quorum_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 3 * LimbTally.limbValue bits a (LimbTally.aCols wDiffRungs)
      - 2 * LimbTally.limbValue bits a (LimbTally.bCols wDiffRungs) < 1) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 3 2 1 LimbTally.TALLY_CARRY_OFF WDIFF_TOP wDiffRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols wDiffRungs WDIFF_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-- ⚑ **AND THE EMPTINESS FLOOR'S REFUSAL, likewise field-free.** `α = 1, β = 0, γ = 1`, so the
hypothesis is `totalWeight − 0·(…) < 1`, i.e. `totalWeight ≤ 0`. At every limb width. -/
theorem mid_positivity_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 1 * LimbTally.limbValue bits a (LimbTally.aCols tPosRungs)
      - 0 * LimbTally.limbValue bits a (LimbTally.bCols tPosRungs) < 1) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 1 0 1 LimbTally.TALLY_CARRY_OFF TPOS_TOP tPosRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols tPosRungs TPOS_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-- ⚑ **THE FLOOR CHAIN'S OPERANDS ARE THE QUORUM DENOMINATOR'S COLUMNS**, by `rfl` on the emitted
rung lists — not by a comment. Both `aCol` and `bCol` of every `tPosRungs` entry are the
total-weight limb, which is what makes `β = 0` harmless AND what lets the floor reuse the operand
range lookups the quorum already declares. -/
theorem mid_tpos_operands_are_the_total_weight_limbs :
    LimbTally.aCols tPosRungs = LimbTally.bCols wDiffRungs
      ∧ LimbTally.bCols tPosRungs = LimbTally.bCols wDiffRungs :=
  ⟨rfl, rfl⟩

/-- …and the tables the descriptor DECLARES are the two the teeth query, by `rfl` on the emitted
object: the 16-bit tally-limb table and the 8-bit chain-carry table. **No 29-bit felt-wide range
table** — the shape a reader should check rather than take from the header. -/
theorem mid_declared_tables :
    midLcVerifyDesc.tables = [⟨TID_TALLY_LIMB, "range_w16", 1, .rangeLimb MID_LIMB_BITS⟩
      , ⟨TID_TALLY_CARRY, "range_w8", 1, .rangeLimb MID_CARRY_BITS⟩] := rfl

/-- ⚑ **AND THE RETIRED TABLE IS REALLY GONE**, stated as a refusal rather than left to the reader:
no `rangeTableDef` at any width (29 or the shipped 128) is among the declared tables. A re-emission
that quietly re-added one moves this. -/
theorem mid_no_felt_wide_range_table_is_declared :
    rangeTableDef 29 ∉ midLcVerifyDesc.tables ∧ rangeTableDef 128 ∉ midLcVerifyDesc.tables := by
  refine ⟨by decide, by decide⟩

/-- The width-tagged wire ids the Rust decoder reads, pinned: `.custom n` serializes as `5 + n`, so
the 16-bit table is id 85 and the 8-bit table is id 77, and `range_bits_for` recovers each width from
its own declaration. A drift in either id changes the descriptor bytes and therefore the VK. -/
theorem mid_tally_table_wire_ids :
    TID_TALLY_LIMB.wireId = 85 ∧ TID_TALLY_CARRY.wireId = 77 := by decide

/-! ### §3c — the mod-`p` ↔ `ℤ` bridge, for BOTH chains.

`LimbTally.rung_no_alias_at_deployed_constants` discharges it for `α = 3, β = 2, γ = 1` — the quorum
chain's coefficients, shared with Tendermint and Solana. The emptiness floor runs at `α = 1, β = 0`,
which that theorem does not cover, so it is discharged here at ITS constants rather than assumed to
follow. -/

/-- ⚑ **NO ALIAS ON THE EMPTINESS-FLOOR CHAIN.** At `bits = 16`, `carryBits = 8`, `coff = 128` and
`α = 1, β = 0, γ = 1`, every rung gate's `ℤ` value on a range-respecting assignment lies inside
`(−p, p)` — so for these gates too `body ≡ 0 (mod p)` IS `body = 0` over `ℤ`, and
`LimbTally.chain_recomposes` transfers to the deployed denotation. The interval is
`(−16842881, 8454400)`, comfortably inside `(−2013265921, 2013265921)`. -/
theorem mid_tpos_rung_no_alias_at_deployed_constants (x y d cin cout : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ MID_LIMB_BITS) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ MID_LIMB_BITS)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ MID_LIMB_BITS)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ MID_CARRY_BITS)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ MID_CARRY_BITS) :
    -Dregg2.Circuit.Emit.EffectLower.P
        < 1 * x - 0 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
            - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ MID_LIMB_BITS
      ∧ 1 * x - 0 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
            - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ MID_LIMB_BITS
          < Dregg2.Circuit.Emit.EffectLower.P := by
  have h := LimbTally.rung_value_bounds MID_LIMB_BITS MID_CARRY_BITS 1 0 1
    LimbTally.TALLY_CARRY_OFF x y d cin cout (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LimbTally.TALLY_CARRY_OFF]) hx hy hd hcin hcout
  obtain ⟨hlo, hhi⟩ := h
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  simp only [MID_LIMB_BITS, MID_CARRY_BITS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_CARRY_BITS,
    LimbTally.TALLY_CARRY_OFF] at hlo hhi ⊢
  rw [hp]
  norm_num at hlo hhi ⊢
  constructor <;> linarith

/-! ## §4 — non-vacuous per-gate lemmas (the emitted bodies bite, both directions). -/

/-- `edBody = 0 ↔ ED_OK = 1`. -/
theorem ed_body_zero_iff (a : Assignment) : edBody.eval a = 0 ↔ a ED_OK = 1 := by
  simp only [edBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `authsetBody = 0 ↔ AUTHSET_OK = 1`. -/
theorem authset_body_zero_iff (a : Assignment) : authsetBody.eval a = 0 ↔ a AUTHSET_OK = 1 := by
  simp only [authsetBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `roundBody = 0 ↔ ROUND_OK = 1`. -/
theorem round_body_zero_iff (a : Assignment) : roundBody.eval a = 0 ↔ a ROUND_OK = 1 := by
  simp only [roundBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `eraBody = 0 ↔ ERA_OK = 1`. -/
theorem era_body_zero_iff (a : Assignment) : eraBody.eval a = 0 ↔ a ERA_OK = 1 := by
  simp only [eraBody, EmittedExpr.eval]; constructor <;> intro h <;> omega

/-! ## §5 — `airAccepts`: the descriptor's LOGIC-acceptance predicate + the REFINEMENT to
`midVerifyDecision`. -/

/-- **`airAccepts a`** — the emitted verify-logic gates all vanish on row `a`, and both difference
vectors' limbs sit in `[0, 2^16)` (the denotation `range_row_mem_iff` connects the emitted lookups
to). The published-anchor pins are the addressing layer, orthogonal to the logic.

⚑ Each single-felt slack conjunct became a PAIR: the generated chain gates vanish, and every
difference limb is contained. Together they are the inequality at ANY tally magnitude a `u64` holds
— see `LimbTally.cmp_sound`. -/
def airAccepts (a : Assignment) : Prop :=
  LimbTally.BodiesVanish a wDiffChainBodies
  ∧ LimbTally.LimbsInRange MID_LIMB_BITS a (LimbTally.diffCols wDiffRungs WDIFF_TOP)
  ∧ LimbTally.BodiesVanish a tPosChainBodies
  ∧ LimbTally.LimbsInRange MID_LIMB_BITS a (LimbTally.diffCols tPosRungs TPOS_TOP)
  -- ⚑ THE ORDERING TOOTH: `totalWeight − signedWeight ≥ 0`. Added 2026-08-03; nothing forced it.
  ∧ LimbTally.BodiesVanish a sleChainBodies
  ∧ LimbTally.LimbsInRange MID_LIMB_BITS a (LimbTally.diffCols sleRungs SLE_TOP)
  ∧ edBody.eval a = 0
  ∧ authsetBody.eval a = 0
  ∧ roundBody.eval a = 0
  ∧ eraBody.eval a = 0

/-- **THE REFINEMENT (soundness): a satisfying AIR witness ENTAILS `midVerifyDecision` accept.** Fed a
row `a` whose columns read the update's true projections (the honest-witness relation — the two weights
as LIMB VECTORS, the carrier/gate bits as `if · then 1 else 0`), if the emitted verify-logic gates
accept, then the exported scalar decision `midVerifyDecision` accepts. The quorum chain discharges the
STRICT > 2/3 threshold; the floor chain discharges `total > 0`.

⚑ Note what is NOT a hypothesis: any bound on `signedW` or `totalW`. The two chains carry the
comparisons at every `u64` magnitude, so nothing here restricts the tally. -/
theorem midLcAir_sound (a : Assignment)
    (signedW totalW : Nat) (edB authsetB roundB eraB : Bool)
    (hSigned : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols wDiffRungs) = (signedW : ℤ))
    (hTotal : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs) = (totalW : ℤ))
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hauthset : a AUTHSET_OK = (if authsetB then (1 : ℤ) else 0))
    (hround : a ROUND_OK = (if roundB then (1 : ℤ) else 0))
    (hera : a ERA_OK = (if eraB then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    midVerifyDecision signedW totalW edB authsetB roundB eraB = true := by
  obtain ⟨hwBodies, hwLimbs, htBodies, htLimbs, _hsBodies, _hsLimbs,
    hedB, hauthsetB, hroundB, heraB⟩ := hacc
  -- ⚑ STRICT > 2/3, AT ANY TALLY MAGNITUDE. `LimbTally.emitted_chain_sound` reads the five generated
  -- quorum gates and the five difference-limb containments and returns `1 ≤ 3·A − 2·B` over the LIMB
  -- VALUES; the two hypotheses say those values are the true `signedW` / `totalW`.
  have hthr : 2 * totalW < 3 * signedW := by
    have hcmp := LimbTally.emitted_chain_sound hwBodies hwLimbs
    rw [hSigned, hTotal] at hcmp
    have : 2 * (totalW : ℤ) < 3 * (signedW : ℤ) := by linarith
    exact_mod_cast this
  -- The EMPTY-AUTHORITY-SET floor, from the second chain: `1 ≤ 1·total − 0·total`.
  have hpos : 0 < totalW := by
    have hcmp := LimbTally.emitted_chain_sound htBodies htLimbs
    have e1 : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols tPosRungs)
        = LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs) := rfl
    have e2 : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols tPosRungs)
        = LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs) := rfl
    rw [e1, e2, hTotal] at hcmp
    have hz : (1 : ℤ) ≤ (totalW : ℤ) := by linarith
    have : 1 ≤ totalW := by exact_mod_cast hz
    omega
  -- Carrier / gate bits.
  have hedTrue : edB = true := by
    have h : a ED_OK = 1 := (ed_body_zero_iff a).mp hedB
    rw [hed] at h; cases edB with | true => rfl | false => simp at h
  have hauthsetTrue : authsetB = true := by
    have h : a AUTHSET_OK = 1 := (authset_body_zero_iff a).mp hauthsetB
    rw [hauthset] at h; cases authsetB with | true => rfl | false => simp at h
  have hroundTrue : roundB = true := by
    have h : a ROUND_OK = 1 := (round_body_zero_iff a).mp hroundB
    rw [hround] at h; cases roundB with | true => rfl | false => simp at h
  have heraTrue : eraB = true := by
    have h : a ERA_OK = 1 := (era_body_zero_iff a).mp heraB
    rw [hera] at h; cases eraB with | true => rfl | false => simp at h
  -- Assemble.
  unfold midVerifyDecision
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hpos, hthr⟩, hedTrue⟩, hauthsetTrue⟩, hroundTrue⟩, heraTrue⟩

/-- **THE PAYOFF: a satisfying AIR witness ENTAILS Midnight GRANDPA-validity (no-forgery, routed through
the emitted AIR).** GIVEN the named authority-set CR carrier (`hcr`), if a row `a` reads update `u`'s true
projections under pinned anchor `ts` and the emitted verify-logic gates accept, then `u` is
Midnight-GRANDPA-VALID relative to `ts` — a STRICT > 2/3 subset of the authority weight, each authority
genuinely signed a precommit for the target at the claimed round under the anchored era, the denominator
pinned to the WS anchor. So a STARK proving `midLcVerifyDesc` carries `mid_no_forgery`: the portable,
trustless proof of Midnight GRANDPA finality. -/
theorem midLcAir_no_forgery (L : MidLeaf) (hcr : L.authSetCR)
    (ts : MidTrustedState L) (u : MidUpdate L) (a : Assignment)
    (hSigned : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols wDiffRungs)
      = (signedWeight L u : ℤ))
    (hTotal : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs)
      = (totalWeight L u : ℤ))
    (hed : a ED_OK = (if edOk L u then (1 : ℤ) else 0))
    (hauthset : a AUTHSET_OK = (if authSetOk L ts u then (1 : ℤ) else 0))
    (hround : a ROUND_OK = (if roundOk L u then (1 : ℤ) else 0))
    (hera : a ERA_OK = (if eraOk L ts u then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    MidValidAt L ts u := by
  have hdec := midLcAir_sound a (signedWeight L u) (totalWeight L u)
    (edOk L u) (authSetOk L ts u) (roundOk L u) (eraOk L ts u)
    hSigned hTotal hed hauthset hround hera hacc
  exact midVerifyDecision_no_forgery L hcr ts u hdec

/-- **Completeness of the two teeth (the honest prover CAN fill both chains).** For any
decision-accepting projections, an honest row that fills the quorum chain and the emptiness-floor
chain with their true limbs and carries (`LimbTally.fillDigit` / `LimbTally.fillCarry`) and the
carrier/gate bits with the true results is accepted by the emitted logic. The non-vacuity partner of
soundness.

⚑ **WHAT DISAPPEARED FROM THIS STATEMENT.** The previous version required
`3·signedW < 2^RANGE_BITS` — a bound on the TALLY at `2^29` — because the quorum slack was one felt,
plus the `TPOS = total − 1` and `WDIFF = …` fill equations as felt identities. **All three are gone.**
What replaces them is the honest chains themselves (`hWDiffChain`/`hWDiffLimbs`,
`hTPosChain`/`hTPosLimbs`), which an honest prover constructs at ANY tally magnitude a `u64` holds —
`midLcAir_accepts_at_the_u64_type_ceiling` (§7) exhibits exactly that at `2^64 − 1`.

⚠ Honest about what that costs in this statement's shape: the chain hypotheses are ASSUMED here
rather than DERIVED from `signedW`/`totalW`, exactly as the Tendermint sibling does. §7's three
explicit rows are what make the assumption a checkable fact rather than a promise. -/
theorem midLcAir_complete (a : Assignment)
    (signedW totalW : Nat) (edB authsetB roundB eraB : Bool)
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hauthset : a AUTHSET_OK = (if authsetB then (1 : ℤ) else 0))
    (hround : a ROUND_OK = (if roundB then (1 : ℤ) else 0))
    (hera : a ERA_OK = (if eraB then (1 : ℤ) else 0))
    (hWDiffChain : LimbTally.BodiesVanish a wDiffChainBodies)
    (hWDiffLimbs : LimbTally.LimbsInRange MID_LIMB_BITS a
      (LimbTally.diffCols wDiffRungs WDIFF_TOP))
    (hTPosChain : LimbTally.BodiesVanish a tPosChainBodies)
    (hTPosLimbs : LimbTally.LimbsInRange MID_LIMB_BITS a (LimbTally.diffCols tPosRungs TPOS_TOP))
    (hSleChain : LimbTally.BodiesVanish a sleChainBodies)
    (hSleLimbs : LimbTally.LimbsInRange MID_LIMB_BITS a (LimbTally.diffCols sleRungs SLE_TOP))
    (hdec : midVerifyDecision signedW totalW edB authsetB roundB eraB = true) :
    airAccepts a := by
  unfold midVerifyDecision at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨⟨⟨⟨_hpos, _hthr⟩, hedB⟩, hauthsetB⟩, hroundB⟩, heraB⟩ := hdec
  refine ⟨hWDiffChain, hWDiffLimbs, hTPosChain, hTPosLimbs, hSleChain, hSleLimbs,
    ?_, ?_, ?_, ?_⟩
  · rw [ed_body_zero_iff, hed]; simp [hedB]
  · rw [authset_body_zero_iff, hauthset]; simp [hauthsetB]
  · rw [round_body_zero_iff, hround]; simp [hroundB]
  · rw [era_body_zero_iff, hera]; simp [heraB]

/-! ## §5b — ⚑⚑ THE RELATION NO GATE FORCED, NOW FORCED **FROM THE TRACE ALONE**.

§5 is a refinement: it says what the AIR entails GIVEN a witness relation naming which columns carry
which projections. This takes no such hypothesis. -/

/-- ⚑ **THE ORDERING CHAIN READS THE QUORUM CHAIN'S OPERANDS, SWAPPED — by `rfl`.**

Without this the two chains could bound two DIFFERENT pairs while both looking right: a prover could
satisfy `signed ≤ total` on one pair of vectors and `3·signed > 2·total` on another. -/
theorem mid_ordering_reads_the_quorum_operands :
    LimbTally.aCols sleRungs = LimbTally.bCols wDiffRungs
      ∧ LimbTally.bCols sleRungs = LimbTally.aCols wDiffRungs := by decide

/-- ⚑⚑ **`signedWeight ≤ totalWeight`, FROM THE TRACE, WITH NO HYPOTHESIS ABOUT THE UPDATE.**

Before the ordering chain, a row claiming a signed authority weight ABOVE the total satisfied every
emitted constraint — the quorum tooth only gets EASIER as `signedWeight` grows, and the two limb
vectors were otherwise unrelated. -/
theorem midLcAir_forces_signed_le_total (a : Assignment) (hacc : airAccepts a) :
    LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols wDiffRungs)
      ≤ LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs) := by
  have h := LimbTally.emitted_chain_sound hacc.2.2.2.2.1 hacc.2.2.2.2.2.1
  have hA : LimbTally.aCols sleRungs = LimbTally.bCols wDiffRungs := by decide
  have hB : LimbTally.bCols sleRungs = LimbTally.aCols wDiffRungs := by decide
  rw [hA, hB] at h
  linarith

/-- **The three teeth together, as one sandwich** — what the emitted AIR now forces about a Midnight
GRANDPA tally, with no hypothesis about the update:

    1 ≤ totalWeight    and    2·totalWeight < 3·signedWeight    and    signedWeight ≤ totalWeight -/
theorem midLcAir_forces_the_tally_sandwich (a : Assignment) (hacc : airAccepts a) :
    1 ≤ LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs)
    ∧ 2 * LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs)
        < 3 * LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols wDiffRungs)
    ∧ LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols wDiffRungs)
        ≤ LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs) := by
  refine ⟨?_, ?_, midLcAir_forces_signed_le_total a hacc⟩
  · have h := LimbTally.emitted_chain_sound hacc.2.2.1 hacc.2.2.2.1
    have hA : LimbTally.aCols tPosRungs = LimbTally.bCols wDiffRungs := by decide
    rw [hA] at h; linarith
  · have h := LimbTally.emitted_chain_sound hacc.1 hacc.2.1
    linarith

/-- ⚑ **THE ORDERING REFUSAL, ON THE EMITTED OBJECT, AT EVERY LIMB WIDTH.** If the true signed weight
EXCEEDS the true total, no assignment of ordering-difference limbs and carries satisfies the emitted
chain together with the containments. No premise about `p`. -/
theorem mid_ordering_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 1 * LimbTally.limbValue bits a (LimbTally.aCols sleRungs)
      - 1 * LimbTally.limbValue bits a (LimbTally.bCols sleRungs) < 0) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 1 1 0 LimbTally.TALLY_CARRY_OFF SLE_TOP sleRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols sleRungs SLE_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-- ⚑ **NO TOOTH SUBSUMES ANOTHER — the arithmetic, at three.**

  * `(total, signed) = (0, 1)`: QUORUM passes (`3·1 − 2·0 − 1 = 2`), ORDERING fails, FLOOR fails.
  * `(total, signed) = (3, 100)`: QUORUM passes hugely, ORDERING fails ALONE, FLOOR passes.
    ⚑ **This row PROVED before this change.**
  * `(total, signed) = (3, 1)`: QUORUM fails ALONE, ORDERING passes, FLOOR passes. -/
theorem mid_three_teeth_are_independent :
    ((0 : ℤ) ≤ 3 * 1 - 2 * 0 - 1 ∧ ¬ ((0 : ℤ) ≤ 0 - 1) ∧ ¬ ((0 : ℤ) ≤ 0 - 1))
    ∧ ((0 : ℤ) ≤ 3 * 100 - 2 * 3 - 1 ∧ ¬ ((0 : ℤ) ≤ 3 - 100) ∧ (0 : ℤ) ≤ 3 - 1)
    ∧ (¬ ((0 : ℤ) ≤ 3 * 1 - 2 * 3 - 1) ∧ (0 : ℤ) ≤ 3 - 1 ∧ (0 : ℤ) ≤ 3 - 1) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩⟩

/-- ⚑ **THE THREE DIFFERENCE VECTORS SHARE NO COLUMN**, and neither do their carries — the property
`mid_three_teeth_are_independent` is arithmetic ABOUT, as a `decide`able fact on the emitted lists. -/
theorem mid_the_three_slacks_are_disjoint :
    (LimbTally.diffCols wDiffRungs WDIFF_TOP).all
        (fun c => !(LimbTally.diffCols tPosRungs TPOS_TOP).contains c
                  && !(LimbTally.diffCols sleRungs SLE_TOP).contains c) = true
    ∧ (LimbTally.diffCols tPosRungs TPOS_TOP).all
        (fun c => !(LimbTally.diffCols sleRungs SLE_TOP).contains c) = true
    ∧ (LimbTally.carryCols wDiffRungs).all
        (fun c => !(LimbTally.carryCols tPosRungs).contains c
                  && !(LimbTally.carryCols sleRungs).contains c) = true
    ∧ (LimbTally.carryCols tPosRungs).all
        (fun c => !(LimbTally.carryCols sleRungs).contains c) = true := by decide

/-- **NO ALIAS FOR THE ORDERING RUNGS.** `LimbTally.rung_no_alias_at_deployed_constants` is stated at
`α = 3, β = 2, γ = 1`; the ordering chain runs at `α = 1, β = 1, γ = 0`. Smaller image, but "smaller,
therefore fine" is an argument and not a theorem. -/
theorem mid_sle_rung_no_alias_at_deployed_constants (x y d cin cout : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ MID_LIMB_BITS) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ MID_LIMB_BITS)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ MID_LIMB_BITS)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ MID_CARRY_BITS)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ MID_CARRY_BITS) :
    -Dregg2.Circuit.Emit.EffectLower.P
        < 1 * x - 1 * y - 0 + (cin - LimbTally.TALLY_CARRY_OFF) - d
            - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ MID_LIMB_BITS
      ∧ 1 * x - 1 * y - 0 + (cin - LimbTally.TALLY_CARRY_OFF) - d
            - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ MID_LIMB_BITS
          < Dregg2.Circuit.Emit.EffectLower.P := by
  have h := LimbTally.rung_value_bounds MID_LIMB_BITS MID_CARRY_BITS 1 1 0
    LimbTally.TALLY_CARRY_OFF x y d cin cout (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LimbTally.TALLY_CARRY_OFF]) hx hy hd hcin hcout
  obtain ⟨hlo, hhi⟩ := h
  simp only [MID_LIMB_BITS, MID_CARRY_BITS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_CARRY_BITS,
    LimbTally.TALLY_CARRY_OFF] at hlo hhi ⊢
  norm_num [Dregg2.Circuit.Emit.EffectLower.P] at hlo hhi ⊢
  constructor <;> linarith

/-! ## §6 — the emitted wire JSON (byte-pinned golden) + shape pins. -/

-- ⚑ THE BYTE-GOLDEN `#guard` IS RETIRED, not deleted — the same move the ETH lane made
-- (`dfa434d46`) and the Tendermint sibling makes in this commit. A transcribed 10 KB wire string
-- cannot see a DROPPED leg (it only sees the string it was captured from), it is invisible to
-- `#assert_axioms`, and it is exactly the `#guard` discipline `metatheory/docs/GUARD-DISCIPLINE.md`
-- forbids. What replaces it is stronger: `rfl` pins on the compiler's own emission
-- (`mid_tally_lookups_are_the_compilers_output`), the structural shape pins, and the checked-in
-- artifact `circuit/descriptors/by-name/dregg-midnight-lightclient-verify-v1.json`, which
-- `EmitByName.lean` RE-DERIVES from this very `def`.

/-- Shape pins (robust; a layout drift moves these). ⚠ NAMED THEOREMS rather than `#guard`s, per
`metatheory/docs/GUARD-DISCIPLINE.md`: a `#guard` produces no term and is invisible to
`#assert_axioms`. -/
theorem mid_shape_pins :
    midLcVerifyDesc.traceWidth = MID_LC_WIDTH
      ∧ midLcVerifyDesc.piCount = PI_COUNT
      ∧ midLcVerifyDesc.constraints.length = 66
      ∧ midLcVerifyDesc.tables.length = 2 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  decide

/-- ⚑ **THE THREE COMPARISONS ARE THIRTY-FIVE LOOKUPS.** Twenty-three 16-bit limb checks plus twelve
8-bit carry checks, where the two single-felt slacks carried exactly ONE each and the two-chain
limbed shape carried twenty-six. A re-emission that dropped a limb moves this number. -/
theorem mid_tally_lookup_count : tallyRangeLookups.length = 35 := by decide

/-- ⚑ **AND THE LOOKUPS ARE THE COMPILER'S OUTPUT, by `rfl` on the emission** — this block used to be
twenty-six hand-written `.lookup` literals. `EffectLower.lowerLimbsLeg` is now the ONLY path from a
`LimbsLeg` to the range teeth in this descriptor. -/
theorem mid_tally_lookups_are_the_compilers_output :
    tallyRangeLookups
      = EffectLower.lowerLimbsLeg totalWeightLeg ++ EffectLower.lowerLimbsLeg signedWeightLeg
        ++ EffectLower.lowerLimbsLeg wDiffLeg ++ EffectLower.lowerLimbsLeg wDiffCarryLeg
        ++ EffectLower.lowerLimbsLeg tPosLeg ++ EffectLower.lowerLimbsLeg tPosCarryLeg
        ++ EffectLower.lowerLimbsLeg sleLeg ++ EffectLower.lowerLimbsLeg sleCarryLeg := rfl

/-- ⚑ **THE IR'S WIDTH VERDICT IS LOAD-BEARING ON THIS DEPLOYED DESCRIPTOR.** All eight limbed
quantities pass `EffectAirIR.LimbsLeg.mainRailOk`, which REFUSES an empty limb vector and any limb
width above the wrap-free ceiling 29 — and this descriptor SHIPPED at 128. -/
theorem mid_tally_legs_are_expressible :
    totalWeightLeg.mainRailOk = true ∧ signedWeightLeg.mainRailOk = true
      ∧ wDiffLeg.mainRailOk = true ∧ wDiffCarryLeg.mainRailOk = true
      ∧ tPosLeg.mainRailOk = true ∧ tPosCarryLeg.mainRailOk = true
      ∧ sleLeg.mainRailOk = true ∧ sleCarryLeg.mainRailOk = true := by decide

/-- …and the width this AIR SHIPPED is one the IR now refuses outright. A verdict that could not go
red would be decoration; this is the red, on the actual historical constant. -/
theorem mid_the_shipped_width_is_refused_by_the_ir :
    ({ totalWeightLeg with bits := 128 } : EffectAirIR.LimbsLeg).mainRailOk = false
      ∧ ({ totalWeightLeg with bits := 30 } : EffectAirIR.LimbsLeg).mainRailOk = false := by decide

/-- …and each chain is FIVE generated gates for four rungs — one per rung plus the closure gate that
forces the final carry into the top difference limb. Without the closure gate the prover could dump a
residue into a carry nothing reads, and the recomposition would be off by `2^64`.

⚑ THREE chains now: quorum, emptiness floor, ordering (`signed ≤ total`). -/
theorem mid_chain_gate_counts :
    wDiffChainGates.length = 5 ∧ tPosChainGates.length = 5 ∧ sleChainGates.length = 5 := by decide

/-- The two crypto carriers are real trace columns, and none is PI-bound (the results ride hidden). -/
theorem mid_carriers_are_hidden_columns :
    ED_OK < MID_LC_WIDTH ∧ AUTHSET_OK < MID_LC_WIDTH := by decide

/-- The tally block occupies columns 4..38 contiguously, below the published anchors: four
total-weight limbs, four signed-weight limbs, and THREE chains of five difference limbs + four
carries each — quorum (12..20), floor (21..29), ordering (30..38). -/
theorem mid_tally_block_layout :
    TOTAL_WEIGHT_LIMB 0 = 4 ∧ TOTAL_WEIGHT_LIMB 3 = 7
      ∧ SIGNED_WEIGHT_LIMB 0 = 8 ∧ SIGNED_WEIGHT_LIMB 3 = 11
      ∧ WDIFF_LIMB 0 = 12 ∧ WDIFF_TOP = 16
      ∧ WDIFF_CARRY 0 = 17 ∧ WDIFF_CARRY 3 = 20
      ∧ TPOS_LIMB 0 = 21 ∧ TPOS_TOP = 25
      ∧ TPOS_CARRY 0 = 26 ∧ TPOS_CARRY 3 = 29
      ∧ SLE_LIMB 0 = 30 ∧ SLE_TOP = 34
      ∧ SLE_CARRY 0 = 35 ∧ SLE_CARRY 3 = 38
      ∧ SLE_CARRY 3 < ANCHOR_ROOT := by decide

/-- The widened finalized-target-root anchor is unchanged by the tally work, only shifted: nine limbs,
contiguous cols 40..48 → PI 1..9, MSB-first, `⌈256/31⌉ = 9` covering the full 256 bits. -/
theorem mid_target_root_anchor_layout :
    TARGET_ROOT_LIMBS = 9 ∧ targetRootPins.length = TARGET_ROOT_LIMBS
      ∧ TARGET_ROOT 0 = 40 ∧ TARGET_ROOT 8 = 48
      ∧ ROUND_COL = 49 ∧ ERA_COL = 50
      ∧ PI_TARGET_ROOT 0 = 1 ∧ PI_TARGET_ROOT 8 = 9
      ∧ PI_ROUND = 10 ∧ PI_ERA = 11
      ∧ TARGET_ROOT 8 < ROUND_COL
      ∧ 31 * TARGET_ROOT_LIMBS ≥ 256 := by decide

/-! ## §7 — ⚑ THE MEASUREMENT: MIDNIGHT MAINNET'S LIVE AUTHORITY SET, AND THE `u64` CEILING.

Everything below is a NAMED THEOREM over an explicit row of the emitted descriptor — a LIST of cells,
so the Lean row and a Rust trace row are literally the same 42 numbers in the same order.

`totalWeight = 130` is Midnight mainnet's live GRANDPA total authority weight, measured 2026-08-03
(`GrandpaApi_grandpa_authorities` → 130 entries, every weight `1`; module header for the full
provenance). It is SEVEN BITS, and it fit a single BabyBear felt perfectly well — that is stated here
rather than hidden, because the second acceptance below is where the capability claim actually lives.

`87` is the SMALLEST strict supermajority of 130: `3·87 = 261 > 260 = 2·130`, and `3·86 = 258 < 260`.

The `u64` ceiling row proves the capability is real rather than merely adequate for today's 130:
`totalWeight = 18446744073709551615 = 2^64 − 1`, all four limbs `65535` — the maximum
`AuthorityWeight` the declared Substrate type can carry — with its own minimal strict supermajority
`12297829382473034411`. -/

/-- The honest row at Midnight's LIVE authority weight, as the cell vector a prover fills. -/
def midLiveCells : List ℤ :=
  [ 1, 1, 1, 1                       -- ED_OK, AUTHSET_OK, ROUND_OK, ERA_OK
  , 130, 0, 0, 0                     -- TOTAL_WEIGHT  limbs = 130 (live, 2026-08-03)
  , 87, 0, 0, 0                      -- SIGNED_WEIGHT limbs = 87 (minimal strict supermajority)
  , 0, 0, 0, 0, 0                    -- WDIFF limbs = 3·87 − 2·130 − 1 = 0
  , 128, 128, 128, 128               -- WDIFF carries, offset (honest carry 0 rides as 128)
  , 129, 0, 0, 0, 0                  -- TPOS  limbs = 130 − 1 = 129
  , 128, 128, 128, 128               -- TPOS carries, offset
  , 43, 0, 0, 0, 0                   -- SLE   limbs = 130 − 87 = 43
  , 128, 128, 128, 128               -- SLE   carries, offset
  , 77777                            -- ANCHOR_ROOT       (addressing layer; no logic gate reads it)
  , 1, 2, 3, 4, 5, 6, 7, 8, 9        -- TARGET_ROOT limbs 0..8 (addressing layer)
  , 4242                             -- ROUND_COL         (addressing layer)
  , 647 ]                            -- ERA_COL           (addressing layer)

/-- The row is exactly as wide as the descriptor. -/
theorem midLiveCells_width : midLiveCells.length = MID_LC_WIDTH := by decide

/-- The row as an `Assignment`. -/
def midLiveRow : Assignment := fun i => midLiveCells.getD i 0

/-- ⚑ **THE TALLY THE ROW DENOTES IS MIDNIGHT'S LIVE TOTAL AUTHORITY WEIGHT.** Four 16-bit limbs,
read by `limbValue`, recompose to `130` exactly — 130 seats, each of GRANDPA weight `1`. -/
theorem midLiveRow_total_is_the_live_authority_weight :
    LimbTally.limbValue MID_LIMB_BITS midLiveRow (LimbTally.bCols wDiffRungs) = 130 := by decide

/-- …and the signed weight is the SMALLEST strict supermajority of it. -/
theorem midLiveRow_signed_is_minimal_supermajority :
    LimbTally.limbValue MID_LIMB_BITS midLiveRow (LimbTally.aCols wDiffRungs) = 87 := by decide

/-- …which really is minimal, BOTH WAYS: `3·87 > 2·130` holds, and `3·86 > 2·130` FAILS. -/
theorem live_minimal_supermajority_is_minimal :
    2 * 130 < 3 * 87 ∧ ¬ (2 * 130 < 3 * 86) := by decide

/-- …and the floor chain's operand vector reads the SAME 130 (the two comparisons share the
denominator columns, `mid_tpos_operands_are_the_total_weight_limbs`). -/
theorem midLiveRow_floor_operand_is_the_live_authority_weight :
    LimbTally.limbValue MID_LIMB_BITS midLiveRow (LimbTally.aCols tPosRungs) = 130 := by decide

/-- ⚑⚑ **THE EMITTED AIR ACCEPTS MIDNIGHT MAINNET'S LIVE AUTHORITY SET** — 87 of 130, at the exact
strict-supermajority boundary (`WDIFF = 0`, the tightest accepting row there is). Every generated gate
of `midLcVerifyDesc` vanishes on this row and every range tooth admits it. -/
theorem midLcAir_accepts_the_live_authority_set : airAccepts midLiveRow := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### The exactly-2/3 sub-quorum, at a total divisible by 3.

130 is not divisible by 3, so exactly-2/3 is not representable there. `129` is: `3·86 = 258 = 2·129`,
difference `−1` — the precise defect the 128-bit table admitted. Both polarities at the same total. -/

/-- The honest row at `total = 129`, `signed = 87` — a genuine (non-boundary) supermajority. -/
def mid129Cells : List ℤ :=
  [ 1, 1, 1, 1                       -- ED_OK, AUTHSET_OK, ROUND_OK, ERA_OK
  , 129, 0, 0, 0                     -- TOTAL_WEIGHT  limbs = 129
  , 87, 0, 0, 0                      -- SIGNED_WEIGHT limbs = 87
  , 2, 0, 0, 0, 0                    -- WDIFF limbs = 3·87 − 2·129 − 1 = 2
  , 128, 128, 128, 128               -- WDIFF carries, offset
  , 128, 0, 0, 0, 0                  -- TPOS  limbs = 129 − 1 = 128
  , 128, 128, 128, 128               -- TPOS carries, offset
  , 42, 0, 0, 0, 0                   -- SLE   limbs = 129 − 87 = 42
  , 128, 128, 128, 128               -- SLE   carries, offset
  , 77777
  , 1, 2, 3, 4, 5, 6, 7, 8, 9
  , 4242
  , 647 ]

theorem mid129Cells_width : mid129Cells.length = MID_LC_WIDTH := by decide

/-- The `total = 129` row as an `Assignment`. -/
def mid129Row : Assignment := fun i => mid129Cells.getD i 0

/-- The row denotes `129` total and `87` signed. -/
theorem mid129Row_denotes :
    LimbTally.limbValue MID_LIMB_BITS mid129Row (LimbTally.bCols wDiffRungs) = 129
      ∧ LimbTally.limbValue MID_LIMB_BITS mid129Row (LimbTally.aCols wDiffRungs) = 87 := by
  refine ⟨by decide, by decide⟩

/-- **87 of 129 ACCEPTS.** -/
theorem midLcAir_accepts_87_of_129 : airAccepts mid129Row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **AND 86 of 129 — EXACTLY 2/3 — IS REFUSED.** `3·86 = 258 = 2·129`, so the quorum difference
is `−1`, and `LimbTally.emitted_chain_refuses` gives: NO assignment of difference limbs and carries
satisfies the chain together with the containments. Not "the wrapped value lands outside an interval"
— there is no limb vector of non-negative limbs denoting `−1`.

⚠ This is the exact defect the shipped 128-bit table ADMITTED
(`mid_exactly_two_thirds_was_admitted_at_128`), and the exact failure mode a wider representation
could have re-admitted. It does not, and the reason is structural rather than arithmetic-on-`p`. -/
theorem midLcAir_refuses_exactly_two_thirds (a : Assignment)
    (hTotal : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs) = 129)
    (hSigned : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols wDiffRungs) = 86) :
    ¬ (LimbTally.BodiesVanish a wDiffChainBodies
        ∧ LimbTally.LimbsInRange MID_LIMB_BITS a (LimbTally.diffCols wDiffRungs WDIFF_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal, hSigned]; norm_num

/-- ⚑ **THE EMPTY AUTHORITY SET IS REFUSED — through the NEW decomposition.** At `totalWeight = 0`
the floor chain's difference is `1·0 − 0·(…) − 1 = −1`, so no assignment of its difference limbs and
carries satisfies the chain together with the containments.

⚠ This is the second defect the 128-bit table admitted
(`mid_both_floors_filled_the_admitted_element`): the emptiness floor accepted the empty set, because
`−1` rode as `p − 1` and `[0, 2^128)` contained it. The refusal here has no `p` in its premises. -/
theorem midLcAir_refuses_the_empty_authority_set (a : Assignment)
    (hTotal : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols tPosRungs) = 0) :
    ¬ (LimbTally.BodiesVanish a tPosChainBodies
        ∧ LimbTally.LimbsInRange MID_LIMB_BITS a (LimbTally.diffCols tPosRungs TPOS_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal]; norm_num

/-- …and the QUORUM chain refuses the empty set INDEPENDENTLY (`3·0 − 2·0 − 1 = −1`). Two floors,
two refusals, as it was before the limbing — a forger must defeat both. -/
theorem midLcAir_quorum_also_refuses_the_empty_authority_set (a : Assignment)
    (hTotal : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs) = 0)
    (hSigned : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols wDiffRungs) = 0) :
    ¬ (LimbTally.BodiesVanish a wDiffChainBodies
        ∧ LimbTally.LimbsInRange MID_LIMB_BITS a (LimbTally.diffCols wDiffRungs WDIFF_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal, hSigned]; norm_num

/-- ⚑⚑ **AND A SIGNED WEIGHT ABOVE THE TOTAL IS REFUSED — the row that PROVED before this change.**
`(total, signed) = (3, 100)` clears the quorum tooth (`3·100 − 2·3 − 1 = 293 ≥ 0`) and the emptiness
floor (`3 − 1 = 2 ≥ 0`), and satisfied every other emitted constraint. The ordering chain refuses it
ALONE: its difference is `3 − 100 = −97`, and no vector of non-negative limbs denotes a negative
number.

This is the Midnight instance of the class the ETH client's `PC = 1023`-of-512 belonged to. -/
theorem midLcAir_refuses_signed_above_total (a : Assignment)
    (hTotal : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.bCols wDiffRungs) = 3)
    (hSigned : LimbTally.limbValue MID_LIMB_BITS a (LimbTally.aCols wDiffRungs) = 100) :
    ¬ (LimbTally.BodiesVanish a sleChainBodies
        ∧ LimbTally.LimbsInRange MID_LIMB_BITS a (LimbTally.diffCols sleRungs SLE_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  have hA : LimbTally.aCols sleRungs = LimbTally.bCols wDiffRungs := by decide
  have hB : LimbTally.bCols sleRungs = LimbTally.aCols wDiffRungs := by decide
  rw [hA, hB, hTotal, hSigned]; norm_num

/-- …and the QUORUM chain does NOT catch it — the pair is the point, and this is the half that shows
the ordering tooth is not redundant. `3·100 − 2·3 − 1 = 293`, comfortably accepting. -/
theorem mid_quorum_admits_signed_above_total :
    (1 : ℤ) ≤ 3 * 100 - 2 * 3 := by norm_num

/-! ### ⚑ THE `u64` TYPE CEILING — the capability, exercised.

130 fits a felt. `2^64 − 1` does not fit anything narrower than the four limbs this AIR now carries,
and it is what `pub type AuthorityWeight = u64` actually permits. If Midnight's governance ever moves
the D-parameter to a stake-weighted committee, this row is the evidence the AIR does not need to
change. -/

/-- The honest row at the `u64` ceiling: `total = 2^64 − 1` (all four limbs `65535`), `signed =
12297829382473034411` (the minimal strict supermajority of it — `3·S = 2^64·3 − 3 + 3 …` computed
exactly: `3·12297829382473034411 = 36893488147419103233 > 36893488147419103230 = 2·(2^64 − 1)`). -/
def midU64CeilingCells : List ℤ :=
  [ 1, 1, 1, 1                       -- ED_OK, AUTHSET_OK, ROUND_OK, ERA_OK
  , 65535, 65535, 65535, 65535       -- TOTAL_WEIGHT  limbs = 18446744073709551615 = 2^64 − 1
  , 43691, 43690, 43690, 43690       -- SIGNED_WEIGHT limbs = 12297829382473034411
  , 2, 0, 0, 0, 0                    -- WDIFF limbs = 3·S − 2·T − 1 = 2
  , 128, 128, 128, 128               -- WDIFF carries, offset (honest carry 0 at every rung)
  , 65534, 65535, 65535, 65535, 0    -- TPOS  limbs = T − 1 = 18446744073709551614
  , 128, 128, 128, 128               -- TPOS carries, offset
  , 21844, 21845, 21845, 21845, 0    -- SLE   limbs = T − S = 6148914691236517204
  , 128, 128, 128, 128               -- SLE   carries, offset
  , 77777
  , 1, 2, 3, 4, 5, 6, 7, 8, 9
  , 4242
  , 647 ]

theorem midU64CeilingCells_width : midU64CeilingCells.length = MID_LC_WIDTH := by decide

/-- The `u64`-ceiling row as an `Assignment`. -/
def midU64CeilingRow : Assignment := fun i => midU64CeilingCells.getD i 0

/-- ⚑ **THE ROW DENOTES `u64::MAX`.** Four 16-bit limbs of `65535` recompose to `2^64 − 1` — the
largest `AuthorityWeight` the declared Substrate type can hold. -/
theorem midU64CeilingRow_total_is_u64_max :
    LimbTally.limbValue MID_LIMB_BITS midU64CeilingRow (LimbTally.bCols wDiffRungs)
      = 18446744073709551615 := by decide

/-- …and the signed weight is the minimal strict supermajority of it. -/
theorem midU64CeilingRow_signed_is_minimal_supermajority :
    LimbTally.limbValue MID_LIMB_BITS midU64CeilingRow (LimbTally.aCols wDiffRungs)
      = 12297829382473034411 := by decide

/-- …minimal BOTH WAYS, at the ceiling: `3·S > 2·T` holds, and one unit below it FAILS. -/
theorem u64_ceiling_supermajority_is_minimal :
    2 * 18446744073709551615 < 3 * 12297829382473034411
      ∧ ¬ (2 * 18446744073709551615 < 3 * 12297829382473034410) := by decide

/-- ⚑⚑ **THE CAPABILITY, EXERCISED: THE EMITTED AIR ACCEPTS AN AUTHORITY SET AT THE `u64` CEILING.**
Every gate vanishes and every range tooth admits, at a total authority weight of `2^64 − 1` — 9.16
billion times the BabyBear modulus, which no single column and no declared range width ever made
representable. That is the difference between "adequate for the 130 measured today" and "adequate for
the type the protocol declares". -/
theorem midLcAir_accepts_at_the_u64_type_ceiling : airAccepts midU64CeilingRow := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- …and the SAME total does not fit a felt, at any declared width: `2^64 − 1` is more than 9.16
billion field moduli. The pair is what makes the ceiling row a capability claim and not decoration. -/
theorem u64_ceiling_does_not_fit_a_felt :
    (9160000000 : ℤ) * Dregg2.Circuit.Emit.EffectLower.P < 18446744073709551615 := by
  norm_num [Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- ⚠ **AND THE HONEST CONTRAST, said out loud rather than left for a reader to infer.** Midnight's
LIVE total authority weight fits a single BabyBear felt with room to spare — `130 < p`, by a factor
of 15 million. The limbing did not close a live representability shortfall on THIS chain; the two
things it closed are the field-size dependence of the refusal (`mid_quorum_refusal_is_field_independent`,
`mid_positivity_refusal_is_field_independent`) and the gap between the measured `130` and the
DECLARED `u64` (`midLcAir_accepts_at_the_u64_type_ceiling`). -/
theorem the_live_authority_weight_did_fit_a_felt :
    (130 : ℤ) * 15000000 < Dregg2.Circuit.Emit.EffectLower.P := by
  norm_num [Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- Carriers / gates, both polarities: a set bit accepts; a cleared (forged / cross-round /
stale-era) bit is refused. -/
theorem mid_carrier_bits_discriminate :
    (edBody.eval (fun i => if i = ED_OK then 1 else 0) = 0 ∧ edBody.eval (fun _ => 0) ≠ 0)
      ∧ (authsetBody.eval (fun i => if i = AUTHSET_OK then 1 else 0) = 0
          ∧ authsetBody.eval (fun _ => 0) ≠ 0)
      ∧ (roundBody.eval (fun i => if i = ROUND_OK then 1 else 0) = 0
          ∧ roundBody.eval (fun _ => 0) ≠ 0)
      ∧ (eraBody.eval (fun i => if i = ERA_OK then 1 else 0) = 0
          ∧ eraBody.eval (fun _ => 0) ≠ 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩⟩

/-! ## §8 — axiom hygiene. -/

#assert_axioms ed_body_zero_iff
#assert_axioms authset_body_zero_iff
#assert_axioms round_body_zero_iff
#assert_axioms era_body_zero_iff
#assert_axioms midLcAir_sound
#assert_axioms midLcAir_no_forgery
#assert_axioms midLcAir_complete
-- The historical defect, both floors, on the shipped 128-bit table.
#assert_axioms mid_exactly_two_thirds_was_admitted_at_128
#assert_axioms mid_both_floors_filled_the_admitted_element
-- ⚑ The limbed teeth: field-free refusals, the shared operand columns, the emitted shape.
#assert_axioms mid_quorum_refusal_is_field_independent
#assert_axioms mid_positivity_refusal_is_field_independent
#assert_axioms mid_tpos_operands_are_the_total_weight_limbs
#assert_axioms mid_tpos_rung_no_alias_at_deployed_constants
#assert_axioms mid_declared_tables
#assert_axioms mid_no_felt_wide_range_table_is_declared
#assert_axioms mid_tally_table_wire_ids
#assert_axioms mid_shape_pins
#assert_axioms mid_tally_lookup_count
#assert_axioms mid_chain_gate_counts
#assert_axioms mid_tally_block_layout
#assert_axioms mid_target_root_anchor_layout
#assert_axioms mid_carriers_are_hidden_columns
-- ⚑ THE MEASUREMENT.
#assert_axioms midLiveCells_width
#assert_axioms midLiveRow_total_is_the_live_authority_weight
#assert_axioms midLiveRow_signed_is_minimal_supermajority
#assert_axioms midLiveRow_floor_operand_is_the_live_authority_weight
#assert_axioms live_minimal_supermajority_is_minimal
#assert_axioms midLcAir_accepts_the_live_authority_set
#assert_axioms mid129Cells_width
#assert_axioms mid129Row_denotes
#assert_axioms midLcAir_accepts_87_of_129
#assert_axioms midLcAir_refuses_exactly_two_thirds
#assert_axioms midLcAir_refuses_the_empty_authority_set
#assert_axioms midLcAir_quorum_also_refuses_the_empty_authority_set
#assert_axioms midU64CeilingCells_width
#assert_axioms midU64CeilingRow_total_is_u64_max
#assert_axioms midU64CeilingRow_signed_is_minimal_supermajority
#assert_axioms u64_ceiling_supermajority_is_minimal
#assert_axioms midLcAir_accepts_at_the_u64_type_ceiling
#assert_axioms u64_ceiling_does_not_fit_a_felt
#assert_axioms the_live_authority_weight_did_fit_a_felt
#assert_axioms mid_carrier_bits_discriminate
-- ⚑⚑ THE CLOSURE, 2026-08-03: `signedWeight ≤ totalWeight`, forced FROM THE TRACE with no
-- hypothesis about the update, plus the arithmetic that says no tooth subsumes another and the
-- mod-`p` bridge at the new coefficients.
#assert_axioms mid_ordering_reads_the_quorum_operands
#assert_axioms midLcAir_forces_signed_le_total
#assert_axioms midLcAir_forces_the_tally_sandwich
#assert_axioms mid_ordering_refusal_is_field_independent
#assert_axioms mid_three_teeth_are_independent
#assert_axioms mid_the_three_slacks_are_disjoint
#assert_axioms mid_sle_rung_no_alias_at_deployed_constants
#assert_axioms midLcAir_refuses_signed_above_total
#assert_axioms mid_quorum_admits_signed_above_total
#assert_axioms mid_tally_lookups_are_the_compilers_output
#assert_axioms mid_tally_legs_are_expressible
#assert_axioms mid_the_shipped_width_is_refused_by_the_ir

#print axioms midLcAir_sound
#print axioms midLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientMidnightAir
