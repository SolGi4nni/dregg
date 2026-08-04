/-
# Dregg2.Circuit.Emit.LightClientSolanaAir — the Solana rooted-finality VERIFY-DECISION, EMITTED AS AN AIR.

## What this file IS (the "STARK-ify the Solana light client" slice — the ETH mirror, one level deeper)

`Dregg2.Bridge.LightClientSolana` AUTHORS the Solana Tower-BFT rooted-finality verification and proves
`sol_no_forgery` over `solVerifyDecision` — the scalar accept/reject a deployed node computes (the
counted rooted authorized voting stake, the active-stake total, the ed25519 + stake-table carriers, the
rooted + authorized-voter gates). That gives a node a Lean-PROVEN verdict — but rendered by running Lean
on the node's own machine; a peer (or an on-chain contract) that wants to trust "this dregg node saw
Solana root slot S with bank hash B" must RE-TRUST that node's execution. There is no portable object.

This file emits `solVerifyDecision` AS A DESCRIPTOR-IR-v2 AIR (`solLcVerifyDesc`), so a dregg node can
PROVE the verify-decision as a STARK: a portable artifact any peer verifies without re-running the node,
and (via the gnark FRI-wrap → Groth16 `SettlementCircuit` → `DreggPeerRegistry`, the SAME on-chain hook
the ETH `LightClientEthAir` attaches to) an on-chain contract verifies. That closes the biggest
interchain gap — Solana from a TRUSTED `True`-instance (the old `ProofOfHoldings` finality oracle) to a
formalized, STARK-ified, PORTABLE rooted-finality proof.

HOUSE LAW #1: the AIR is LEAN-AUTHORED. Rust only ingests the emitted `emitVmJson2` descriptor and runs
the generic multi-table prover over it; it never hand-writes these constraints. The refinement
`solLcAir_sound` / `solLcAir_no_forgery` is a machine-checked theorem over the EMITTED object
(`airAccepts` reads the descriptor's own gate bodies), tying acceptance to `solVerifyDecision` and hence
to `sol_no_forgery` — so a STARK satisfying this AIR CARRIES the no-forgery guarantee, modulo the two
named crypto carriers (below).

## ⚑ THE TALLY REPAIR (2026-08-03): SOLANA'S STAKE NEVER FIT A COLUMN, AT ANY DECLARED WIDTH

This descriptor shipped `bits: 128` on its range table. Over BabyBear (`p = 2013265921 < 2^31 < 2^128`)
**every field element was already in the declared interval**, so both lookups refused NOTHING
(`RangeFieldContainment.range_vacuous_at_or_above_31`). Narrowing to 29 — the maximum wrap-free width
— bought the teeth back, and in doing so it EXPOSED the limit the vacuous width had been hiding:
`ROOTED_STK` and `TOTAL_STK` were ONE COLUMN EACH, and one BabyBear felt holds 30.9 bits.

⚑ **MEASURED LIVE, 2026-08-03**, `getVoteAccounts` on `api.mainnet-beta.solana.com` (epoch 1011, slot
436,909,708; 689 current + 14 delinquent vote accounts): mainnet-beta ACTIVE stake is

    432,650,183,925,625,587 lamports  =  432.650M SOL  =  2^58.586

and `getSupply` puts total supply at 631,503,420,149,974,995 lamports (2^59.13) — re-sampled from the
same endpoint while authoring this file and agreeing to eight significant figures (631,503,394,549,607,495,
a drift of ~26 SOL over the intervening minutes), which is the corroboration the headline number gets.
The wire type is `u64`. **None of that ever fit a column** — not at 128 bits, not at 29, not at any
width, because a width declares an INTERVAL and the wire is one field element. The 128-bit declaration
did not make the tally fit; it made the shortfall invisible, and the 29-bit repair made it VISIBLE and
no smaller.

Both tallies are now **four 16-bit limbs each, LEAST-significant first — exactly a `u64`**. The
arithmetic, its soundness and its refusal live in `Dregg2.Circuit.LimbTally`; this file instantiates
that theory twice and GENERATES the gates from it.

## ⚑ THE STRICTNESS REPAIR (2026-08-03): THE THRESHOLD WAS THE WRONG POLARITY

This descriptor shipped `γ = 0` — the NON-STRICT `3·rooted ≥ 2·total`. **That is not Solana's rule.**
Read at source 2026-08-03 (agave `c7670b260b8cd34674e05c03c0babdaf54e15987`):

    runtime/src/commitment.rs:9        pub const VOTE_THRESHOLD_SIZE: f64 = 2f64 / 3f64;
    core/src/commitment_service.rs:59  if (stake_sum as f64 / total_stake as f64) > VOTE_THRESHOLD_SIZE

`get_highest_super_majority_root` (`core/src/commitment_service.rs:54-64`) IS the rooted-finality rule
this AIR models — it walks per-validator rooted stake against the epoch total and returns the highest
root clearing the threshold — and its comparison is **STRICT `>`**.

⚠ **The previous version of this note cited `core/src/consensus.rs`'s `Tower::is_slot_confirmed` at
"line 1041". That function is `#[cfg(test)]`** (`core/src/consensus.rs:584-596` at the sha above) —
a test helper, not the reference comparison. The production rule is the one quoted above.

The old defence of non-strict was: `2f64 / 3f64` is the double `0.666666666666666629659…`, strictly
BELOW 2/3, so agave's `>` against it already admits ratios a strict `> 2/3` would reject. That is TRUE
about the CONSTANT and WRONG about the COMPARISON — **the dividend is rounded to the same double.**
When `rooted/total` is exactly 2/3 and both operands are exactly representable, the correctly-rounded
quotient IS `2f64/3f64`, and `d > d` is false. agave refuses the exact-2/3 point; the shipped γ = 0
accepted it.

MEASURED (`agave_strictness_equiv.rs`, agave's comparison transcribed verbatim, 2026-08-03):

  * FULL exhaustive `r ∈ [0, t]` for every `t ≤ 3000` (4 504 500 pairs), a windowed sweep to
    `t = 20 000`, and 2 000 000 random pairs at `t < 2^52`: agave's float rule and the STRICT integer
    rule `3·rooted > 2·total` disagree on **ZERO of 6 684 470 pairs**. agave and the NON-STRICT rule
    disagree on 1000 of the full-exhaustive pairs — every one the exact-2/3 point, every one this AIR
    ACCEPTING where agave REFUSES.
  * ⚑ At `total = 0`: `0f64 / 0f64` is `NaN` and `NaN > x` is FALSE, so **agave refuses the empty
    stake table at the threshold comparison itself.** The shipped γ = 0 accepted it (`3·0 ≥ 2·0`).
    That is the empty-stake hole, and it was an INFIDELITY, not a design choice.
  * Above `2^53` neither integer form matches: `total as f64` is itself rounded and the boundary
    acquires ±1 lamport of jitter (`432650183925625587` as `f64` is `432650183925625600`, 13 lamports
    off, ULP 64 at 2^58). At live magnitude agave disagrees with strict on 32.8% of boundary-adjacent
    pairs and with non-strict on 43.8%. Strict is the closer AND the conservative one — it refuses
    inside the jitter band rather than accepting inside it.

So this AIR now carries `α = 3, β = 2, **γ = 1**` — `3·rooted ≥ 2·total + 1`, the same constants
Midnight and Tendermint already carried. ⚠ Still NOT a bit-for-bit model of agave's float arithmetic
above 2^53; nothing in a prime field is. What IS established: strict reproduces agave EXACTLY wherever
agave's own arithmetic is exact, and errs toward refusal where it is not.

## ⚠ AND THE RULE IS BEING REPLACED — say it before someone reads `γ = 1` as permanent

Alpenglow (`votor/`) is in agave master TODAY and does not use this rule at all.
`votor/src/aggregate_accumulator.rs:94-95` builds a certificate iff
`Fraction::new(stake, total) >= cert_type.threshold()` — **NON-STRICT**, by EXACT `u128`
cross-multiplication (`votor-messages/src/fraction.rs:47-60` — no floats, and structurally the same
`α·A ≥ β·B` shape a circuit wants), against **60%** (Notarize / Finalize / Skip / NotarizeFallback)
and **80%** (FinalizeFast) (`votor-messages/src/certificate.rs:101-109`), with an 82% migration
threshold (`votor-messages/src/migration.rs:87`). So the successor rule is non-strict — at 3/5 and
4/5, not 2/3, and over a CERTIFICATE rather than a rooted-stake walk. It is not a retroactive defence
of γ = 0.

mainnet-beta was still on the Tower rule when this was written: measured 2026-08-03, `getVersion` →
`solana-core 4.1.0` and `getBlockCommitment` still serves the Tower `BlockCommitmentCache`, reporting
`totalStake = 432650183925625587` — the exact denominator §7 pins. **When Alpenglow activates, this
descriptor is wrong again**, in the constant AND in the shape, and that is a re-authoring, not a
parameter tweak.

## The crypto boundary: IN-AIR logic vs NAMED verified carriers

  * IN-AIR (arithmetic gates over the trace — the stake TALLY logic, the Nomad-class bug locus):
      - the STRICT >2/3 supermajority `3·rooted ≥ 2·total + 1` as a LIMBED comparison: four rungs of
        an offset carry chain over the two `u64` limb vectors, five range-checked difference limbs,
        `α = 3, β = 2, γ = 1`;
      - the `EmptyStakeTable` floor `total ≥ 1` as a SECOND limbed chain over the SAME total-stake
        limb vector, `α = 1, β = 0, γ = 1`;
      - the ROOTED flag (`ROOTED_OK = 1` — HOLE-1) and the AUTHORIZED-voter binding (`AUTH_OK = 1` —
        BR-2-A) as forced boolean gates.
  * NAMED verified CARRIERS (witnessed boolean columns, forced `= 1`):
      - `ED_OK`         — the aggregate ed25519 verify over the counted authorized voters + the vote
        message `(slot, bankHash)` (`ed25519_dalek` / a verified realization),
      - `STAKE_TABLE_OK`— the derived stake table binds to the pinned WS anchor root (the SHA-256
        `EpochStakeTable::root` compare — the HOLE-2 denominator pin).

The residual is HONEST and NAMED: in THIS slice the two crypto carriers are asserted, not re-derived
in-circuit, so the STARK proves the TALLY/THRESHOLD/ROOTED/AUTHORIZED LOGIC is correct GIVEN the ed25519
and stake-table results — precisely `solVerifyDecision`'s guarantee, now portable. Putting ed25519 and
the stake-table SHA fold in-AIR (or as their own verified sub-proofs the AIR `ProofBind`s against) is the
next iteration; the public-input anchors below are the hook it attaches to. Also named: the counted
`ROOTED_STK` popcount-of-stake is a trusted projection (the deployed node's distinct-voter tally), the
same posture as the ETH `PC` participant count.

## ⚑ WHAT THE EMPTY-STAKE-TABLE FLOOR COST, AND WHY ITS NEW REFUSAL IS BETTER

`TPOS = TOTAL_STK − 1 ≥ 0` is the `EmptyStakeTable` floor, and it is the check that FAILED. At
`TOTAL_STK = 0` the slack filled to `−1`, which in the deployed mod-`p` reading rides as
`p − 1 = 2013265920`, and the 128-bit table CONTAINED it. **The empty stake table passed its own
emptiness floor** — and with `ROOTED_STK = TOTAL_STK = 0` the quorum slack `3·0 − 2·0 = 0` passed too,
so a block signed by nobody satisfied both teeth.

The 29-bit narrowing refused it because `p − 1 ∉ [0, 2^29)`: a fact about the FIELD SIZE, false at 30
and catastrophically false at the 128 that shipped. The limbed floor refuses it because a limb vector
of non-negative limbs denotes a non-negative value and `1 ≤ 0` is false — a fact about limb vectors,
true at EVERY width in EVERY field (`solLcAir_refuses_the_empty_stake_table`,
`sol_empty_stake_refusal_is_field_independent`). Widening the representable tally by 2^33× does not
re-admit it; it removes the field size from the refusal's premises.

⚑ **AND THE FLOOR IS NO LONGER ALONE.** That the quorum ADMITTED the empty set was not an artefact of
the limbing — it was `γ = 0`, and `γ = 0` was a fidelity defect (agave gets this refusal for free from
`NaN > x = false`; see the strictness note above). With `γ = 1` the quorum difference at
`rooted = total = 0` is `3·0 − 2·0 − 1 = −1` and the QUORUM chain refuses the empty stake table from
its own five difference limbs (cols 12..16) and its own four carries (cols 17..20)
(`solLcAir_quorum_also_refuses_the_empty_stake_table`). Two gates on disjoint columns, neither
subsuming the other (`sol_two_teeth_are_independent`) — the shape Midnight already had.

⚠ **Bound the independence claim honestly.** The two refusals read disjoint columns and are carried by
distinct gate sets, so disarming either leaves the other standing — that is demonstrated on the
DEPLOYED prover, one at a time, in `circuit/tests/solana_lightclient_proves.rs`. They are NOT
independent all the way down: both bottom out in `LimbTally.limbValue_nonneg`. Two gates, one lemma —
exactly as Midnight's pair is, and a break in that lemma takes both.

## The two declared range tables, and the one that is GONE

The tally rides at 16 bits and its carries at 8, on WIDTH-TAGGED CUSTOM tables (`.custom (64 + b)`,
wire ids 85 and 77) — the same mechanism the deployed availability-weld uses for its 15-bit borrow
limbs. Rust resolves each lookup's width from the DECLARED table (`descriptor_ir2.rs`
`range_bits_for`), realizes every width as the same byte-limb decomposition, and shares ONE byte table
across all of them.

⚑ **The 29-bit `range` table (wire id 2) is NO LONGER DECLARED.** It carried exactly two lookups —
`QDIFF` and `TPOS` — and BOTH are now limbed chains, so nothing queries it. Declaring a table no
constraint reads is a table whose width nothing checks; it is dropped rather than left standing.
`RANGE_BITS` survives only as the subject of the HISTORICAL record theorems in §3b (the value the
128-bit table admitted and the 29-bit table refused), and `sol_range_table_is_not_declared` is the
tripwire that reds if a felt-width slack is ever re-introduced.

## Public inputs (the addressing layer — what the proof is ABOUT)

`PI[0..8]  = ANCHOR_ROOT[0..8]` — the pinned WS stake-table root (the governance trust anchor the
                            STAKE_TABLE_OK carrier is a compare against). The trust root the proof is
                            relative to, as its NINE radix-`2^31` MSB-first limbs.
                            ⚑ 2026-08-04 — THIS WAS ONE COLUMN. `WeakSubjectivityAnchor.stake_table_root`
                            is `[u8; 32]` and `PI[0]` carried it as a single BabyBear element, so the
                            comparison a light client makes against its own pinned anchor was over 31
                            BITS OF A 256-BIT HASH — colliding pair findable in `2^31`. That is the
                            SAME defect the bank root below documents as closed, on the OTHER root in
                            the SAME descriptor, and it stood for as long as the fix next to it.
`PI[9..17] = BANK_ROOT[0..8]` — the claimed ROOTED bank/state hash B at slot S (what a proof-of-holdings
                            later opens against): the FULL 256-bit bank hash exposed as its NINE
                            radix-`2^31`, MOST-SIGNIFICANT-limb-first limbs (`⌈256/31⌉ = 9`; the top
                            limb carries the residual 8 bits). FELT-WIDTH CLOSE: the earlier single
                            anchor felt bound only a 31-bit PROJECTION of the bank hash (two 256-bit
                            roots agreeing in 31 bits both verified — a soundness gap at the peer-wrap
                            boundary); nine PI-bound limbs bind the WHOLE root, recomposed by the
                            peer-wrap's radix-`2^31` MSB-first pack before its 128-bit split.
`PI[18]    = SLOT`           — the rooted slot S (the epoch/slot the finality is claimed at).
`PI[19..22] = TOTAL_STK[0..3]` — ⚑⚑ **THE ACTIVE-STAKE DENOMINATOR, PUBLISHED.** The four 16-bit limbs
                            the quorum chain divides by, PI-bound to the light client's
                            weak-subjectivity anchor. **The prover does not choose the number its own
                            quorum is a fraction of.** Before 2026-08-04 it did: a cartel holding 1% of
                            mainnet-beta could exhibit a `(total, rooted)` pair over a stake universe
                            100× too small, satisfy every gate in this descriptor, and the emitted
                            object had nothing to say about it
                            (`circuit/tests/solana_lightclient_proves.rs::a_swapped_stake_table_*`).

These ride as published witness columns pinned to the public inputs (`.piBinding`). PARTLY CLOSED
2026-08-04: the DENOMINATOR is now published, so the tally block and the anchor block share columns
(§6b — and the two disconnection tripwires FIRED saying so). STILL OPEN, and kept as tripwires in the
same shape: the bank root and slot are read by no gate (`ED_OK` derived from the vote message built on
`BANK_ROOT`+`SLOT` is the Ed25519/EC arc), and the anchor root is read by no gate (`STAKE_TABLE_OK`
derived from the table fold into `ANCHOR_ROOT` — §6c prices why that one is not this commit).

## The mod-p ↔ ℤ reading

`airAccepts` reads the emitted gate bodies as ℤ equalities and the limb lookups as ℤ intervals. For the
CHAIN gates that bridge is DISCHARGED rather than named — but ⚠ **at THIS AIR's constants, not by
citing a sibling's**. `LimbTally.rung_no_alias_at_deployed_constants` is stated at `α = 3, β = 2,
γ = 1`; ⚑ since the strictness repair the QUORUM chain has exactly those constants (the FLOOR, at
`α = 1, β = 0`, still does not). Both instances are nevertheless proved here from the parametric
`LimbTally.rung_value_bounds` rather than by citing the sibling — a local claim proved locally cannot
silently follow a sibling's constants if either drifts:
`sol_qdiff_rung_no_alias` (`α = 3, β = 2, γ = 1`) and `sol_tpos_rung_no_alias` (`α = 1, β = 0,
γ = 1`). Each bounds every rung gate's ℤ value, on any assignment respecting the DECLARED ranges,
strictly inside `(−p, p)` — so `body ≡ 0 (mod p)` IS `body = 0` over ℤ there, and §3's recomposition
transfers to the deployed denotation. `LimbTally.rung_alias_reachable_at_24_bits` exhibits a reachable
failure eight bits above the deployed limb width, so the constant has a measured margin AND a measured
failure point.

## What this file BREAKS (say the flag day out loud)

Trace width `19 → 41`, constraints `19 → 51`, declared tables `[range@29] → [range_w16, range_w8]`,
and the emitted descriptor bytes therefore change — so `dregg-solana-lightclient-verify::v1`'s VK
ROTATES and `circuit/descriptors/by-name/dregg-solana-lightclient-verify-v1.json` is RE-EMITTED. Any
Rust witness filler for this descriptor must now fill limb vectors and two carry chains instead of two
felt slacks; the old 19-column row REFUSES to satisfy the new descriptor (its columns are not even the
same quantities). Nothing else in the tree consumes this AIR yet.

⚑ **AND A SECOND FLAG DAY, SAME DAY: THE STRICTNESS REPAIR (`γ = 0 → 1`).** The emitted object moves
by ONE constant — the quorum chain's LSB rung goes `8388608 → 8388607` — so the shape (41 / 11 / 51 /
two tables) is UNCHANGED and only the bytes move. What that costs, said out loud:

  * `dregg-solana-lightclient-verify::v1`'s VK **ROTATES AGAIN**, and
    `circuit/descriptors/by-name/dregg-solana-lightclient-verify-v1.json` is RE-EMITTED a second time.
  * ⚑ **Rows that proved before now REFUSE.** Every witness at exactly `3·rooted = 2·total` — which is
    where a minimal-quorum filler naturally lands, and IS the row §7 shipped — has no satisfying
    assignment. `MIN_QUORUM` in the Rust harness moves up by ONE LAMPORT
    (`288433455950417058 → 288433455950417059`) and the old value becomes a REFUSAL fixture.
  * `solVerifyDecision` and `SolValidAt` in `Dregg2.Bridge.LightClientSolana` change with it
    (`2·total ≤ 3·rooted` → `<`), so `sol_no_forgery`'s conclusion is STRICTLY STRONGER than before;
    the two downstream hash-fold modules that take the threshold as a hypothesis
    (`Sha256HfoldDischarge`, `LightClientSolHashFold`) take the strict form now.
  * `bridge/src/solana_consensus.rs`'s `is_supermajority` (`:333`) carried the SAME non-strict `>=`
    and moves with them — it is the deployed node-side tally, and leaving it non-strict would put the
    hole back one layer down.

  Nothing refuses to LOAD (the descriptor's shape is identical), which is the one uncomfortable part
  of this flag day: a stale VK against the new bytes fails at VERIFY, not at parse.

⚑ **A THIRD FLAG DAY — 2026-08-04: THE FULL-WIDTH WS ANCHOR ROOT AND THE PINNED DENOMINATOR.**
Trace width `41 → 49`, PI count `11 → 23`, constraints `51 → 63`. Two changes, one re-emit:

  * **`ANCHOR_ROOT` was ONE column and is now NINE** (cols 30..38 → PI 0..8, radix-`2^31` MSB-first).
    It carried a 256-bit SHA-256 stake-table root as a single BabyBear element — 31 bits — which is
    the exact felt-width defect this file diagnosed and repaired for `BANK_ROOT`, on the other root in
    the same descriptor, and did not apply here. `BANK_ROOT` shifts `31..39 → 39..47` and `SLOT_COL`
    `40 → 48`; their PI slots shift `1..9 → 9..17` and `10 → 18`.
  * **The four `TOTAL_STK` limbs gain `.piBinding`s** to PI 19..22 (`totalStakePins`): the
    active-stake denominator is published rather than prover-chosen.

  What this costs, said out loud:

  * `dregg-solana-lightclient-verify::v1`'s VK **ROTATES** (a third time) and
    `circuit/descriptors/by-name/dregg-solana-lightclient-verify-v1.json` is RE-EMITTED.
    ⚠ Unlike the strictness repair, this one DOES refuse to LOAD: the trace width and PI count both
    move, so a stale 41-column row or an 11-element PI vector fails at parse, not at verify.
  * **Every caller must now supply 23 public inputs**, including the anchor's total active stake.
    `WeakSubjectivityAnchor` (`bridge/src/solana_provenance.rs`) pins `(epoch, stake_table_root)`
    today; the denominator PI is the value a light client must ALSO hold, and a caller that does not
    have it cannot state what it is asking. That is the intended shape — it is what stops the swap.
  * **A row that proved before now REFUSES** if its denominator is not the published one — which is
    the entire point, exhibited both ways in `circuit/tests/solana_lightclient_proves.rs`
    (`a_swapped_stake_table_is_arithmetically_perfect` /
    `a_swapped_stake_table_is_refused_against_the_pinned_denominator`).
  * **Two §6b tripwires FIRED and are GONE**, replaced by positive statements
    (`sol_quorum_reads_a_published_anchor`, `sol_denominator_is_fully_pinned`) plus two narrower
    tripwires for what is still open. `LightClientAnchorConnectivity`'s Solana literal and its
    six-chain census moved with them (`11 → 19` decorative, census `63 → 71`).

## Axiom hygiene
Definitional descriptor + non-vacuous per-gate `iff` lemmas (`omega`) + the load-bearing
`solLcAir_sound` / `solLcAir_no_forgery` refinement to `solVerifyDecision` / `sol_no_forgery`.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.RangeFieldContainment
import Dregg2.Circuit.LimbTally
import Dregg2.Bridge.LightClientSolana

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Dregg2.Circuit.Emit.LightClientSolanaAir

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Bridge.LightClientSolana

/-! ## §1 — the trace column layout (one logical row).

Columns 0..3 are the four boolean carrier/gate projections `solVerifyDecision` composes over.
Columns 4..29 are the TALLY BLOCK: the two `u64` stake vectors as four 16-bit limbs each, and the two
comparison chains (five difference limbs + four offset carries apiece). Columns 30..40 are the
published PUBLIC anchors: `ANCHOR_ROOT` (30), the NINE bank-root limbs `BANK_ROOT 0..8` (cols 31..39 —
the full 256-bit bank hash, radix-`2^31`, MSB-first), and `SLOT_COL` (40). -/

/-- **CARRIER** — the aggregate ed25519 verify RESULT (counted authorized voters signed the bank hash at
the slot); forced `= 1`. NAMED verified-FFI carrier. Witness. -/
def ED_OK : Nat := 0
/-- **CARRIER** — the stake-table-root compare RESULT (derived table binds the pinned WS anchor root);
forced `= 1`. NAMED carrier (the HOLE-2 denominator pin). Witness. -/
def STAKE_TABLE_OK : Nat := 1
/-- **GATE** — the ROOTED flag (every counted vote's tower root reaches the slot — HOLE-1); forced `= 1`. -/
def ROOTED_OK : Nat := 2
/-- **GATE** — the AUTHORIZED-voter binding (every counted signer is the on-chain authorized voter —
BR-2-A); forced `= 1`. -/
def AUTH_OK : Nat := 3

/-! ### ⚑ THE STAKE TALLIES, AS LIMB VECTORS — the capability this AIR did not have.

`ROOTED_STK` and `TOTAL_STK` used to be ONE COLUMN EACH. A column is one BabyBear felt and a felt holds
30.9 bits, so the deployed client could not represent mainnet-beta's active stake at all: measured live
2026-08-03, `432650183925625587` lamports = 2^58.586, which is 214.9 MILLION times the modulus. The
128-bit range declaration did not make that fit; it made the shortfall invisible, and the 29-bit repair
that closed the vacuity made it VISIBLE and no smaller.

They are now **four 16-bit limbs each, LEAST-significant first — exactly a `u64`**, which is exactly
Solana's own wire type for lamport stake. -/

/-- The tally limb width. `SOL_TALLY_LIMBS · SOL_LIMB_BITS = 64`. -/
def SOL_LIMB_BITS : Nat := LimbTally.TALLY_LIMB_BITS
/-- The number of tally limbs — four 16-bit limbs are a `u64`. -/
def SOL_TALLY_LIMBS : Nat := LimbTally.TALLY_LIMBS
/-- The carry width for the difference chains (the prover's own byte bus). -/
def SOL_CARRY_BITS : Nat := LimbTally.TALLY_CARRY_BITS

/-- **Limb `i` of the total ACTIVE stake** (`total_stake()`, the 2/3 denominator), LSB-first.
Columns 4..7. Witness. -/
def TOTAL_STK_LIMB (i : Nat) : Nat := 4 + i
/-- **Limb `i` of the counted rooted authorized voting stake** (`voted_stake`), LSB-first.
Columns 8..11. Its ed25519 provenance is the `ED_OK` carrier. Witness. -/
def ROOTED_STK_LIMB (i : Nat) : Nat := 8 + i

/-- **Limb `i` of the QUORUM difference `3·rooted − 2·total`**, LSB-first. FIVE limbs (columns
12..16), one more than the operands: `3·A` needs two bits beyond `A`. Every limb carries its own
16-bit range lookup, and THAT is the quorum tooth — a limb vector of non-negative limbs denotes a
non-negative value, so a sub-quorum (whose difference is negative) has no representation at all. -/
def QDIFF_LIMB (i : Nat) : Nat := 12 + i
/-- **Offset carry `i` of the quorum chain** (columns 17..20); denotes `col − 128`, since a difference
chain BORROWS and a field wire has no sign. Range-checked at 8 bits for the mod-`p` bridge ONLY —
`LimbTally.chain_recomposes` needs no bound on it whatsoever. -/
def QDIFF_CARRY (i : Nat) : Nat := 17 + i

/-- **Limb `i` of the EMPTY-STAKE-TABLE floor difference `total − 1`**, LSB-first. FIVE limbs
(columns 21..25) — the generator emits `k + 1` difference limbs for `k` rungs regardless of `α`, and
at `α = 1` the top limb is simply always zero on an honest fill. -/
def TPOS_LIMB (i : Nat) : Nat := 21 + i
/-- **Offset carry `i` of the floor chain** (columns 26..29). -/
def TPOS_CARRY (i : Nat) : Nat := 26 + i

/-- The number of ~31-bit limbs a FULL 256-bit root is exposed as: `⌈256 / 31⌉ = 9`. Eight 31-bit
limbs cover 248 bits; the ninth (most-significant) limb carries the remaining 8 bits. -/
def ROOT_LIMBS : Nat := 9

/-- ⚑ **PUBLIC ANCHOR (limb `i`) — the pinned WS stake-table root, AT FULL WIDTH.** The governance
trust anchor the whole light client is relative to, as its radix-`2^31` MOST-SIGNIFICANT-limb-first
decomposition: limb `i` is trace column `30 + i` (cols 30..38), PI-bound to slot `i`.

⚑ 2026-08-04 — **THIS WAS ONE COLUMN, AND THAT WAS THE SAME DEFECT THE BANK ROOT HAD.** The
felt-width close below (`BANK_ROOT`, nine limbs) was diagnosed and repaired in this very file for the
bank hash — *"a SINGLE anchor felt bound only a 31-bit PROJECTION, so two 256-bit roots agreeing in
31 bits both verified"* — and the OTHER 256-bit root in the SAME descriptor, the one the tally's whole
trust story hangs from, was left at one felt. `WeakSubjectivityAnchor.stake_table_root` is `[u8; 32]`
(`bridge/src/solana_provenance.rs:579`); `PI[0]` carried it reduced to a single BabyBear element, so a
light client comparing its pinned anchor against the proof's public statement compared **31 bits of
it**. Two stake tables whose SHA-256 roots agree in those 31 bits — findable in `2^31` hashes, minutes
of GPU — were the same anchor as far as this descriptor could tell. Nine limbs bind the whole root. -/
def ANCHOR_ROOT (i : Nat) : Nat := 30 + i

/-- The number of limbs the rooted bank hash is exposed as (`= ROOT_LIMBS`; kept as its own name
because the two roots are independent shapes that merely happen to share a width). -/
def BANK_ROOT_LIMBS : Nat := ROOT_LIMBS

/-- **PUBLIC ANCHOR (limb `i`)** — the claimed rooted bank/state root B as its radix-`2^31`,
MOST-SIGNIFICANT-limb-first decomposition. Limb `i` is trace column `39 + i` (cols 39..47); limb `0` is
the MSB (its top carries only 8 bits). PI-bound to slot `9 + i`, so the peer-wrap's radix-`2^31`
MSB-first pack over `PI[9..17]` recomposes the 256-bit bank hash exactly before its 128-bit split. -/
def BANK_ROOT (i : Nat) : Nat := 30 + ROOT_LIMBS + i

/-- **PUBLIC ANCHOR** — the rooted slot S (epoch/slot). PI-bound. -/
def SLOT_COL : Nat := 30 + ROOT_LIMBS + BANK_ROOT_LIMBS

/-- Total main-trace width: 4 carrier/gate columns + 4 total-stake limbs + 4 rooted-stake limbs +
5 quorum-difference limbs + 4 quorum carries + 5 floor-difference limbs + 4 floor carries +
9 anchor-root limbs + 9 bank-root limbs + 1 slot anchor = 49.

⚑ It was 19, then 41. The +22 was the tally becoming REPRESENTABLE: two `u64` operands and TWO
comparison chains (the quorum and the emptiness floor), each with its own difference vector and borrow
chain. The +8 is the WS anchor root ceasing to be a 31-bit projection of a 256-bit hash. -/
def SOL_LC_WIDTH : Nat := 49

/-- PI slot of anchor-root limb `i` (slots 0..8), MSB-first. -/
def PI_ANCHOR_ROOT (i : Nat) : Nat := i
/-- PI slot of bank-root limb `i` (slots 9..17), MSB-first. -/
def PI_BANK_ROOT (i : Nat) : Nat := ROOT_LIMBS + i
/-- PI slot of the rooted slot (slot 18). -/
def PI_SLOT : Nat := ROOT_LIMBS + BANK_ROOT_LIMBS

/-- ⚑ **PI slot of TOTAL-STAKE limb `i` (slots 19..22)** — the governance-pinned active-stake
DENOMINATOR. See `totalStakePins`: these slots are what stop the prover choosing the number its own
quorum is a fraction of. -/
def PI_TOTAL_STK (i : Nat) : Nat := ROOT_LIMBS + BANK_ROOT_LIMBS + 1 + i

/-- Number of public inputs: 9 anchor-root limbs + 9 bank-root limbs + slot + 4 total-stake limbs. -/
def PI_COUNT : Nat := 23

/-- ⚑ **THE HISTORICAL FELT-SLACK WIDTH — NO LONGER DECLARED BY THIS DESCRIPTOR.**

This was `128` (the `u128` width the Rust `is_supermajority` tally uses — a number that describes the
WIRE and says nothing about the domain the constraint is evaluated in), then `29` (the maximum
wrap-free width at BabyBear, `RangeFieldContainment.wrap_free_iff_le_29`). It is now the subject of the
RECORD theorems in §3b and NOTHING ELSE: both slacks that queried the `range` table are limbed chains,
so the descriptor declares no table at this width (`sol_range_table_is_not_declared`).

Kept rather than deleted because the pair it names — `p − 1` ADMITTED at 128, REFUSED at 29 — is the
measurement that made the narrowing a repair, and the limbed refusal that superseded it is only
legible against it. -/
def RANGE_BITS : Nat := 29

/-! ## §2 — the emitted gate bodies (the descriptor's OWN constraint polynomials).

### ⚑ The two comparisons, GENERATED rather than transcribed.

`LightClientMinaAir` set the bar — `EffectLower.lowerAir`-authored, no hand-written `VmConstraint2`.
Each comparison used to be ONE hand-written gate body plus ONE lookup, because a single-felt slack is
one gate. A limbed comparison is five gates and between nine and seventeen lookups (five difference
limbs, four carries, plus whichever operand limbs a sibling chain has not already checked), and
hand-writing those would be exactly the drift House Law #1 exists to stop.

`LimbTally.chainBodies` GENERATES them from the rung list, and `LimbTally.chainBodies_zero_iff` ties
what it generates back to `ChainOk` — so §5's soundness is about the bodies that ship. -/

/-- **The four rungs of the QUORUM difference chain**, LSB-first: at radix position `i` the
rooted-stake limb (the `α = 3` operand), the total-stake limb (the `β = 2` operand), the difference
limb and the offset carry out.

Written as an explicit literal (rather than `List.range`-mapped) so the byte-golden `#guard` reduces to
the exact wire string with no fold — the same discipline `bankRootPins` follows. -/
def qdiffRungs : List LimbTally.Rung :=
  [ ⟨ROOTED_STK_LIMB 0, TOTAL_STK_LIMB 0, QDIFF_LIMB 0, QDIFF_CARRY 0⟩
  , ⟨ROOTED_STK_LIMB 1, TOTAL_STK_LIMB 1, QDIFF_LIMB 1, QDIFF_CARRY 1⟩
  , ⟨ROOTED_STK_LIMB 2, TOTAL_STK_LIMB 2, QDIFF_LIMB 2, QDIFF_CARRY 2⟩
  , ⟨ROOTED_STK_LIMB 3, TOTAL_STK_LIMB 3, QDIFF_LIMB 3, QDIFF_CARRY 3⟩ ]

/-- The quorum difference vector's TOP limb — the chain's closure column. -/
def QDIFF_TOP : Nat := QDIFF_LIMB 4

/-- **The four rungs of the EMPTY-STAKE-TABLE FLOOR chain**, LSB-first, over the SAME total-stake limb
vector the quorum chain reads as its `β` operand.

⚠ **`bCol` POINTS AT `aCol` ON PURPOSE — this is not a copy-paste bug.** `LimbTally.Rung` carries a
`bCol` field at every rung because the general comparison is `α·A − β·B − γ`. Here `β = 0`, so the
emitted term is literally `.mul (.const 0) (.var (TOTAL_STK_LIMB i))` — a constant-zero factor, whose
value is zero whatever column it names — and `LimbTally.cmp_sound`'s conclusion is
`γ ≤ α·A − 0·B = α·A`. Pointing it at the total-stake limb costs nothing and needs no dedicated
zero column, which a fresh column would have had to be pinned to zero by yet another gate. -/
def tposRungs : List LimbTally.Rung :=
  [ ⟨TOTAL_STK_LIMB 0, TOTAL_STK_LIMB 0, TPOS_LIMB 0, TPOS_CARRY 0⟩
  , ⟨TOTAL_STK_LIMB 1, TOTAL_STK_LIMB 1, TPOS_LIMB 1, TPOS_CARRY 1⟩
  , ⟨TOTAL_STK_LIMB 2, TOTAL_STK_LIMB 2, TPOS_LIMB 2, TPOS_CARRY 2⟩
  , ⟨TOTAL_STK_LIMB 3, TOTAL_STK_LIMB 3, TPOS_LIMB 3, TPOS_CARRY 3⟩ ]

/-- The floor difference vector's TOP limb — the chain's closure column. -/
def TPOS_TOP : Nat := TPOS_LIMB 4

/-- The emitted QUORUM gate bodies: `α = 3` on rooted stake, `β = 2` on total stake, and ⚑ `γ = 1`
for agave's **STRICT** `> 2/3` (`get_highest_super_majority_root`'s `>`; the module header carries the
6.68-million-pair measurement that settled it) — the same constants Midnight and Tendermint already
carried. Five bodies from four rungs (one per rung plus the closure gate).

⚑ It was `γ = 0`. γ enters `LimbTally.chainBodies` as the initial `g` and NOWHERE else (every
recursive call re-seeds `g := 0`), so the whole difference in the EMITTED OBJECT is one constant on
the LSB rung: `coff·2^bits − γ` goes `8388608 → 8388607`. One literal — and it is the difference
between refusing a block signed by nobody and accepting one. -/
def qdiffChainBodies : List EmittedExpr :=
  LimbTally.chainBodies SOL_LIMB_BITS 3 2 1 LimbTally.TALLY_CARRY_OFF QDIFF_TOP qdiffRungs

/-- The emitted FLOOR gate bodies: `α = 1`, `β = 0`, `γ = 1` — i.e. `total − 1 ≥ 0`, the
`EmptyStakeTable` refusal. Five bodies from four rungs. -/
def tposChainBodies : List EmittedExpr :=
  LimbTally.chainBodies SOL_LIMB_BITS 1 0 1 LimbTally.TALLY_CARRY_OFF TPOS_TOP tposRungs

/-- `ED_OK − 1` — zero iff the ed25519 carrier bit is set. -/
def edBody : EmittedExpr := .add (.var ED_OK) (.const (-1))
/-- `STAKE_TABLE_OK − 1` — zero iff the stake-table-root carrier bit is set. -/
def stakeBody : EmittedExpr := .add (.var STAKE_TABLE_OK) (.const (-1))
/-- `ROOTED_OK − 1` — zero iff the rooted-flag gate bit is set. -/
def rootedBody : EmittedExpr := .add (.var ROOTED_OK) (.const (-1))
/-- `AUTH_OK − 1` — zero iff the authorized-voter-binding gate bit is set. -/
def authBody : EmittedExpr := .add (.var AUTH_OK) (.const (-1))

/-! ## §3 — the constraint list + descriptor.

### The two declared range tables, and the one that is gone.

The tally rides at 16 and its carries at 8, on WIDTH-TAGGED CUSTOM tables (`.custom (64 + b)`), which
is the mechanism the deployed availability-weld already uses for its 15-bit borrow limbs. The shared
`range` table at `RANGE_BITS` is NOT declared: both of its former lookups are limbed chains now, and a
declared table no constraint reads is a width nothing checks. -/

/-- The tally-limb range table: wire id `5 + 64 + 16 = 85`. -/
def TID_TALLY_LIMB : TableId := .custom (64 + SOL_LIMB_BITS)
/-- The chain-carry range table: wire id `5 + 64 + 8 = 77`. -/
def TID_TALLY_CARRY : TableId := .custom (64 + SOL_CARRY_BITS)

/-- ⚑ **THE TEETH: one range lookup PER LIMB, on BOTH chains.**

Eighteen 16-bit lookups (four total-stake limbs, four rooted-stake limbs, five quorum-difference
limbs, five floor-difference limbs) and eight 8-bit carry lookups. The load-bearing ones are the TEN
on the two differences: they are what forces `3·rooted − 2·total ≥ 0` and `total − 1 ≥ 0`, because a
limb vector of non-negative limbs denotes a non-negative value (`LimbTally.limbValue_nonneg`).

⚠ The eight OPERAND lookups are not part of that argument (`LimbTally.cmp_sound` does not use them);
they are there for the mod-`p` ↔ `ℤ` bridge (`LimbTally.rung_no_alias_at_deployed_constants`), which
needs every limb in `[0, 2^16)`. Two different jobs, said apart rather than blurred.

⚠ The total-stake limbs are looked up ONCE, not twice: both chains read the same four columns, and a
second identical lookup would be a duplicate constraint, not a second check. -/
def tallyRangeLookups : List VmConstraint2 :=
  [ .lookup ⟨TID_TALLY_LIMB, [.var (TOTAL_STK_LIMB 0)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TOTAL_STK_LIMB 1)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TOTAL_STK_LIMB 2)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TOTAL_STK_LIMB 3)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (ROOTED_STK_LIMB 0)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (ROOTED_STK_LIMB 1)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (ROOTED_STK_LIMB 2)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (ROOTED_STK_LIMB 3)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 0)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 1)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 2)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 3)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 4)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 0)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 1)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 2)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 3)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 4)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (QDIFF_CARRY 0)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (QDIFF_CARRY 1)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (QDIFF_CARRY 2)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (QDIFF_CARRY 3)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (TPOS_CARRY 0)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (TPOS_CARRY 1)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (TPOS_CARRY 2)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (TPOS_CARRY 3)]⟩ ]

/-- The generated QUORUM gates, wrapped into the target's constraint constructor. GENERATED — there is
no hand-written `VmConstraint2` in this block. -/
def qdiffChainGates : List VmConstraint2 :=
  qdiffChainBodies.map (fun b => .base (.gate b))

/-- The generated EMPTY-STAKE-TABLE FLOOR gates. GENERATED, from the same `LimbTally.chainBodies`
call at `α = 1, β = 0, γ = 1`. -/
def tposChainGates : List VmConstraint2 :=
  tposChainBodies.map (fun b => .base (.gate b))

def edGate : VmConstraint2 := .base (.gate edBody)
def stakeGate : VmConstraint2 := .base (.gate stakeBody)
def rootedGate : VmConstraint2 := .base (.gate rootedBody)
def authGate : VmConstraint2 := .base (.gate authBody)
/-- ⚑ **Published-anchor pins: the NINE WS stake-table-root limbs are `PI[0..8]` (MSB-first).** Each
limb rides its own PI slot, so a light client comparing its governance-pinned anchor against the
proof's public statement compares the FULL 256 bits — not the 31-bit projection a single felt carried.
Written as an explicit literal (limb `i` → col `30+i` → PI `i`) so the byte-golden `#guard` reduces to
the exact wire string with no fold. -/
def anchorRootPins : List VmConstraint2 :=
  [ .base (.piBinding VmRow.first (ANCHOR_ROOT 0) (PI_ANCHOR_ROOT 0))
  , .base (.piBinding VmRow.first (ANCHOR_ROOT 1) (PI_ANCHOR_ROOT 1))
  , .base (.piBinding VmRow.first (ANCHOR_ROOT 2) (PI_ANCHOR_ROOT 2))
  , .base (.piBinding VmRow.first (ANCHOR_ROOT 3) (PI_ANCHOR_ROOT 3))
  , .base (.piBinding VmRow.first (ANCHOR_ROOT 4) (PI_ANCHOR_ROOT 4))
  , .base (.piBinding VmRow.first (ANCHOR_ROOT 5) (PI_ANCHOR_ROOT 5))
  , .base (.piBinding VmRow.first (ANCHOR_ROOT 6) (PI_ANCHOR_ROOT 6))
  , .base (.piBinding VmRow.first (ANCHOR_ROOT 7) (PI_ANCHOR_ROOT 7))
  , .base (.piBinding VmRow.first (ANCHOR_ROOT 8) (PI_ANCHOR_ROOT 8)) ]
/-- Published-anchor pins: the NINE rooted-bank-root limbs are `PI[1..9]` (MSB-first). Each limb rides
its own PI slot, so the peer-wrap's radix-`2^31` pack over `PI[1..9]` recovers the FULL 256-bit bank
hash — not a 31-bit projection. Written as an explicit literal (limb `i` → col `31+i` → PI `1+i`) so
the byte-golden `#guard` reduces to the exact wire string with no fold. -/
def bankRootPins : List VmConstraint2 :=
  [ .base (.piBinding VmRow.first (BANK_ROOT 0) (PI_BANK_ROOT 0))
  , .base (.piBinding VmRow.first (BANK_ROOT 1) (PI_BANK_ROOT 1))
  , .base (.piBinding VmRow.first (BANK_ROOT 2) (PI_BANK_ROOT 2))
  , .base (.piBinding VmRow.first (BANK_ROOT 3) (PI_BANK_ROOT 3))
  , .base (.piBinding VmRow.first (BANK_ROOT 4) (PI_BANK_ROOT 4))
  , .base (.piBinding VmRow.first (BANK_ROOT 5) (PI_BANK_ROOT 5))
  , .base (.piBinding VmRow.first (BANK_ROOT 6) (PI_BANK_ROOT 6))
  , .base (.piBinding VmRow.first (BANK_ROOT 7) (PI_BANK_ROOT 7))
  , .base (.piBinding VmRow.first (BANK_ROOT 8) (PI_BANK_ROOT 8)) ]
/-- Published-anchor pin: the rooted slot is `PI[18]`. -/
def slotPin : VmConstraint2 :=
  .base (.piBinding VmRow.first SLOT_COL PI_SLOT)

/-- ⚑⚑ **THE DENOMINATOR PINS — the anchor→tally binding, and the whole point of this pass.**

The four TOTAL-STAKE limb columns the quorum chain divides by are PI-bound to slots `19..22`. The
prover no longer chooses them: they are part of the proof's PUBLIC STATEMENT, supplied by the light
client from its governance-pinned weak-subjectivity anchor
(`WeakSubjectivityAnchor.total_stake`, `bridge/src/solana_provenance.rs`) and compared there.

⚑ **Why the tally's OWN columns rather than a mirrored anchor block.** Pinning cols 4..7 directly —
instead of introducing separate `ANCHOR_TOTAL` columns forced equal to them by four gates — is not a
saving of four columns, it is the difference between a binding and a decoration. The quorum chain's
`β` operand IS the published value; there is no second copy that some later edit could leave
unforced. It is also what makes §6b's disconnection measurement flip honestly: the tally block now
genuinely reads a published anchor column, because its denominator IS one.

⚠ **Bound the claim.** This pins the DENOMINATOR, not the TABLE. The prover still chooses which
validators the numerator counts (`ROOTED_STK` is a witnessed projection, `ED_OK` a witnessed carrier),
so a swap to a different validator set with the SAME total active stake is NOT refused by this. What
IS refused is every swap that moves the total — which is what `STAKE_TABLE_OK` was named for (the
HOLE-2 denominator pin) and what the SHA-256 table fold is priced out of doing (§6c). -/
def totalStakePins : List VmConstraint2 :=
  [ .base (.piBinding VmRow.first (TOTAL_STK_LIMB 0) (PI_TOTAL_STK 0))
  , .base (.piBinding VmRow.first (TOTAL_STK_LIMB 1) (PI_TOTAL_STK 1))
  , .base (.piBinding VmRow.first (TOTAL_STK_LIMB 2) (PI_TOTAL_STK 2))
  , .base (.piBinding VmRow.first (TOTAL_STK_LIMB 3) (PI_TOTAL_STK 3)) ]

/-- **`solLcVerifyDesc`** — the Solana rooted-finality verify-decision as an emitted IR-v2 AIR. PIs
`[anchor_root[0..8], bank_root[0..8], slot, total_stk[0..3]]` (23 total — BOTH 256-bit roots are the
FULL value as nine radix-`2^31` MSB-first limbs, not a 31-bit projection, and the active-stake
DENOMINATOR is published rather than prover-chosen); the two `u64` stake tallies as 16-bit limb
vectors with their two GENERATED comparison chains, the four crypto/logic results as carrier bits. Two
declared range tables (16-bit limbs, 8-bit carries); the shared 29-bit `range` table is gone with the
felt slacks that queried it. -/
def solLcVerifyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-solana-lightclient-verify::v1"
  , traceWidth  := SOL_LC_WIDTH
  , piCount     := PI_COUNT
  , tables      := [⟨TID_TALLY_LIMB,  "range_w16", 1, .rangeLimb SOL_LIMB_BITS⟩
                   , ⟨TID_TALLY_CARRY, "range_w8",  1, .rangeLimb SOL_CARRY_BITS⟩]
  , constraints := tallyRangeLookups ++ qdiffChainGates ++ tposChainGates
                   ++ [edGate, stakeGate, rootedGate, authGate]
                   ++ anchorRootPins ++ bankRootPins ++ [slotPin] ++ totalStakePins
  , hashSites   := []
  , ranges      := [] }

/-! ## §3b — ⚑ THE HISTORICAL RECORD: what a felt-width slack could and could not refuse.

A narrowed constant is a constant. What made a range tooth an `≤` relation was exactly this pair: the
interval sits strictly INSIDE the field, and a slack the prover wanted negative lands OUTSIDE it. Both
were FALSE at `RANGE_BITS = 128`.

⚠ **These theorems no longer describe a table this descriptor declares** — §3c is where the live
refusal lives. They are kept because the value they exhibit, `p − 1`, is the exact deployed encoding of
the empty stake table's `TPOS = −1`, and it is the reason the repair happened. -/

/-- **THE INTERVAL WAS INSIDE THE FIELD.** `2^29 = 536870912 < p = 2013265921`. -/
theorem sol_range_is_inside_the_field :
    (2 : ℤ) ^ RANGE_BITS < Dregg2.Circuit.Emit.EffectLower.P := by
  norm_num [RANGE_BITS, Dregg2.Circuit.Emit.EffectLower.P]

/-- ⚑ **AND THE WRAP WAS REFUSED.** A slack the prover wanted to be `−k`, for any magnitude
`0 < k ≤ 2^29`, is in the deployed mod-`p` reading the element `p − k ≥ p − 2^29 = 1476395009` —
nearly three times the interval ceiling. ⚠ FALSE at 30, and catastrophically false at the shipped
128, where `p − 1` sat inside and every negative slack was admitted. -/
theorem sol_wrapped_slack_is_outside_the_range (k : ℤ) (hk : 0 < k)
    (hk' : k ≤ (2 : ℤ) ^ RANGE_BITS) :
    ¬ (0 ≤ Dregg2.Circuit.Emit.EffectLower.P - k
        ∧ Dregg2.Circuit.Emit.EffectLower.P - k < (2 : ℤ) ^ RANGE_BITS) := by
  rintro ⟨_, hlt⟩
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  have hb : ((2 : ℤ) ^ RANGE_BITS) = 536870912 := by norm_num [RANGE_BITS]
  rw [hp, hb] at hlt
  rw [hb] at hk'
  omega

/-- ⚑ **THE ADMITTED VALUE, EXHIBITED — AND IT IS THE EMPTY STAKE TABLE.** `2013265920` is `p − 1`,
the deployed encoding of `TPOS = TOTAL_STK − 1 = −1`, which is what `TOTAL_STK = 0` fills. The
shipped 128-bit table CONTAINED it, so the `EmptyStakeTable` floor admitted a stake table with no
stake in it. -/
theorem sol_empty_stake_table_was_admitted_at_128 :
    ([2013265920] : List ℤ) ∈ rangeRows 128 := by
  rw [range_row_mem_iff]; norm_num

/-- …and the 29-bit table REFUSED it. One value, admitted then refused — the pair that made the
narrowing a repair rather than a renumbering.

⚠ Note what this refusal RESTS ON: `2013265920 ≥ 2^29`, a fact about the FIELD SIZE. It is false at 30
and catastrophically false at 128. §3c's replacement rests on nothing of the kind. -/
theorem sol_empty_stake_table_was_refused_at_29_bits :
    ([2013265920] : List ℤ) ∉ rangeRows RANGE_BITS := by
  rw [range_row_mem_iff]; norm_num [RANGE_BITS]

/-- **THE LIMB TOOTH IS THE EMITTED ONE.** The interval `airAccepts` reads for every difference and
operand limb (§5) is exactly membership in the declared 16-bit table's rows — not a second, private
notion of "in range" that could be narrowed here while the descriptor keeps shipping the old one. -/
theorem sol_limb_inRange_iff_mem_rangeRows (v : ℤ) :
    (0 ≤ v ∧ v < (2 : ℤ) ^ SOL_LIMB_BITS) ↔ [v] ∈ rangeRows SOL_LIMB_BITS :=
  (range_row_mem_iff v SOL_LIMB_BITS).symm

/-- …and the tables the descriptor DECLARES are the two the teeth query, by `rfl` on the emitted
object: the 16-bit tally-limb table and the 8-bit chain-carry table. -/
theorem sol_declared_tables :
    solLcVerifyDesc.tables = [⟨TID_TALLY_LIMB, "range_w16", 1, .rangeLimb SOL_LIMB_BITS⟩
      , ⟨TID_TALLY_CARRY, "range_w8", 1, .rangeLimb SOL_CARRY_BITS⟩] := rfl

/-- ⚑ **AND THE SHARED `range` TABLE IS NOT AMONG THEM, NOR AMONG THE LOOKUPS.** Both former felt
slacks are limbed chains, so the 29-bit table would be declared-but-unqueried. This is the tripwire: a
future felt-width slack re-introduced on `TableId.range` reds here. -/
theorem sol_range_table_is_not_declared :
    (∀ t ∈ solLcVerifyDesc.tables, t.id ≠ TableId.range)
      ∧ TableId.range ∉ (solLcVerifyDesc.constraints.filterMap
          (fun c => match c with | .lookup l => some l.table | _ => none)) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The width-tagged wire ids the Rust decoder reads, pinned: `.custom n` serializes as `5 + n`, so
the 16-bit table is id 85 and the 8-bit table is id 77, and `range_bits_for` recovers each width from
its own declaration. A drift in either id changes the descriptor bytes and therefore the VK. -/
theorem sol_tally_table_wire_ids :
    TID_TALLY_LIMB.wireId = 85 ∧ TID_TALLY_CARRY.wireId = 77 := by decide

/-! ### ⚑ §3c — THE LIMBED COMPARISONS: the capability, and the teeth that survived it.

Everything in §3b is about a `rangeRows` interval over ONE felt. Neither comparison lives there any
more. These are the facts about the LIMBED versions, and the last two are the reason widening the
representable tally by 2^33× did not re-admit anything. -/

/-- ⚑ **THE CAPABILITY, AS THE MEASURED NUMBER.** Four 16-bit limbs represent every value in
`[0, 2^64)`, which contains mainnet-beta's LIVE active stake — `432650183925625587` lamports, measured
2026-08-03 via `getVoteAccounts` at epoch 1011 / slot 436,909,708 — and Solana's total supply
(`631503420149974995`) besides. -/
theorem sol_tally_capacity_holds_live_active_stake :
    (432650183925625587 : ℤ) < (2 : ℤ) ^ (SOL_LIMB_BITS * SOL_TALLY_LIMBS)
      ∧ (631503420149974995 : ℤ) < (2 : ℤ) ^ (SOL_LIMB_BITS * SOL_TALLY_LIMBS) := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [SOL_LIMB_BITS, SOL_TALLY_LIMBS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_LIMBS]

/-- ⚑ …and the SAME value does not fit one felt, at any declared width. This is the pair that makes
the widening a capability and not a preference: live active stake is **214.9 MILLION** BabyBear
moduli (`432650183925625587 / 2013265921 = 214899670.9`), so no `bits:` — 29, 30, 64 or the 128 that
shipped — ever made it representable. A width declares an interval; the wire is one field element. -/
theorem sol_live_active_stake_does_not_fit_a_felt :
    (214899670 : ℤ) * Dregg2.Circuit.Emit.EffectLower.P < 432650183925625587
      ∧ (432650183925625587 : ℤ) < 214899671 * Dregg2.Circuit.Emit.EffectLower.P := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- ⚑ **THE QUORUM REFUSAL NO LONGER MENTIONS THE FIELD.** If the true tallies fail the STRICT
`> 2/3` threshold, NO assignment satisfies the emitted quorum chain together with the
difference-limb containment — for EVERY limb width, including the widths at which the old single-felt
tooth was vacuous (`≥ 31`) and the width at which it was merely leaky (30). -/
theorem sol_quorum_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 3 * LimbTally.limbValue bits a (LimbTally.aCols qdiffRungs)
      - 2 * LimbTally.limbValue bits a (LimbTally.bCols qdiffRungs) < 1) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 3 2 1 LimbTally.TALLY_CARRY_OFF QDIFF_TOP qdiffRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols qdiffRungs QDIFF_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-- ⚑⚑ **THE SECOND TOOTH ON THE EMPTY STAKE TABLE — the quorum chain, not the floor.**

At `rooted = total = 0` the STRICT quorum difference is `3·0 − 2·0 − 1 = −1`, and no limb vector of
non-negative limbs denotes `−1`. So the QUORUM chain refuses a block signed by nobody **on its own**,
reading its own five difference limbs (cols 12..16) and its own four carries (cols 17..20) — columns
the emptiness floor never touches.

⚑ This is what `γ = 0` cost, stated as the thing that changed: at `γ = 0` the same row filled to
`3·0 − 2·0 = 0`, an honest, in-range, ACCEPTING fill, and `tposChainBodies` was the ONLY gate between
this descriptor and a block signed by nobody. It is now one of two.

⚠ Independence, honestly bounded: the two refusals read DISJOINT difference columns, are carried by
DISTINCT gate sets, and neither implies the other (the floor also refuses `total = 0` at any
`rooted > 0`, which the quorum admits; the quorum also refuses every sub-quorum at `total > 0`, which
the floor admits — `sol_two_teeth_are_independent`). They are NOT independent all the way down: both
bottom out in `LimbTally.limbValue_nonneg`, exactly as Midnight's pair does. Two gates, one lemma. -/
theorem solLcAir_quorum_also_refuses_the_empty_stake_table (a : Assignment) (bits : Nat)
    (hRooted : LimbTally.limbValue bits a (LimbTally.aCols qdiffRungs) = 0)
    (hTotal : LimbTally.limbValue bits a (LimbTally.bCols qdiffRungs) = 0) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 3 2 1 LimbTally.TALLY_CARRY_OFF QDIFF_TOP qdiffRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols qdiffRungs QDIFF_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hRooted, hTotal]; norm_num

/-- ⚑ **NEITHER TOOTH SUBSUMES THE OTHER — the arithmetic, so "depth" is not a mood.**

`(rooted, total) = (5, 0)`: the strict quorum is SATISFIED (`15 ≥ 1`) and the emptiness floor FAILS
(`0 < 1`) — a prover claiming rooted stake against a table with no stake in it is caught by the floor
alone. `(rooted, total) = (1, 3)`: the floor is SATISFIED (`3 ≥ 1`) and the quorum FAILS (`3 < 7`) —
a sub-quorum is caught by the quorum alone. And `(0, 0)` fails BOTH.

So the pair covers strictly more than either member, which is the whole claim `depth` is making. -/
theorem sol_two_teeth_are_independent :
    (1 ≤ 3 * 5 - 2 * 0 ∧ ¬ (1 ≤ (0 : ℤ)))
    ∧ (1 ≤ (3 : ℤ) ∧ ¬ (1 ≤ 3 * 1 - 2 * 3))
    ∧ (¬ (1 ≤ 3 * 0 - 2 * 0) ∧ ¬ (1 ≤ (0 : ℤ))) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩⟩

/-- ⚑ **AND SO DOES THE EMPTY-STAKE-TABLE REFUSAL — the check that actually FAILED.** At `total = 0`
the floor difference is `−1`; no limb vector of non-negative limbs denotes `−1`. Quantified over
EVERY limb width, so this is not "the wrapped value lands outside an interval at 29 bits". -/
theorem sol_empty_stake_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 1 * LimbTally.limbValue bits a (LimbTally.aCols tposRungs)
      - 0 * LimbTally.limbValue bits a (LimbTally.bCols tposRungs) < 1) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 1 0 1 LimbTally.TALLY_CARRY_OFF TPOS_TOP tposRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols tposRungs TPOS_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-- ⚑ **THE FLOOR CHAIN READS THE QUORUM CHAIN'S DENOMINATOR — the same four columns, by `rfl`.**

Without this the two chains could bound two DIFFERENT quantities while both looking correct: a prover
could satisfy `total ≥ 1` on one vector and `3·rooted ≥ 2·total` on another. `LimbTally.aCols
tposRungs` and `LimbTally.bCols qdiffRungs` are literally the same column list, so `total` means one
thing in this AIR. -/
theorem sol_tpos_reads_the_quorum_denominator :
    LimbTally.aCols tposRungs = LimbTally.bCols qdiffRungs := by decide

/-! ### ⚑ §3d — the mod-`p` ↔ `ℤ` bridge, DISCHARGED AT **THESE** CONSTANTS.

⚠ `LimbTally.rung_no_alias_at_deployed_constants` is stated at `α = 3, β = 2, γ = 1` — CometBFT's
STRICT supermajority, which ⚑ since the strictness repair is ALSO Solana's quorum. The floor chain
(`α = 1, β = 0`) still has its own constants, and both instances are proved below from the PARAMETRIC
`LimbTally.rung_value_bounds` rather than by citation: a local claim proved locally cannot silently
follow a sibling's constants if either drifts.

Both intervals are far inside the field, and the numbers are worth reading rather than taking on the
word "inside": the quorum rung's ℤ image sits in `(−16973953, 8585472)` — one wider at the bottom than
at `γ = 0`, since `γ` enters the lower bound as `−(β·2^bits + γ + coff + 2^bits + 2^carryBits·2^bits)`
— and the floor rung's in
`(−16842881, 8454400)`, against `p = 2013265921`. So a body that is `0 mod p` on a range-respecting
assignment IS `0` over `ℤ`, and `LimbTally.chain_recomposes` transfers to the deployed denotation. -/

/-- **NO ALIAS ON THE QUORUM CHAIN** (`α = 3, β = 2, γ = 1`, `coff = 128`, limbs 16, carries 8).

⚑ At `γ = 1` these are exactly `LimbTally.TALLY_*`'s deployed constants, so this instance now
COINCIDES with `LimbTally.rung_no_alias_at_deployed_constants` rather than needing its own reading of
the parametric bound. It is still proved here from `rung_value_bounds` — a local proof of a local
claim cannot silently inherit a sibling's constants if either drifts. -/
theorem sol_qdiff_rung_no_alias (x y d cin cout : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ SOL_LIMB_BITS) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ SOL_LIMB_BITS)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ SOL_LIMB_BITS)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ SOL_CARRY_BITS)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ SOL_CARRY_BITS) :
    -Dregg2.Circuit.Emit.EffectLower.P
        < 3 * x - 2 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
          - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ SOL_LIMB_BITS
    ∧ 3 * x - 2 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
          - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ SOL_LIMB_BITS
        < Dregg2.Circuit.Emit.EffectLower.P := by
  obtain ⟨hlo, hhi⟩ := LimbTally.rung_value_bounds SOL_LIMB_BITS SOL_CARRY_BITS 3 2 1
    LimbTally.TALLY_CARRY_OFF x y d cin cout (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LimbTally.TALLY_CARRY_OFF]) hx hy hd hcin hcout
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  simp only [SOL_LIMB_BITS, SOL_CARRY_BITS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_CARRY_BITS,
    LimbTally.TALLY_CARRY_OFF] at hlo hhi ⊢
  norm_num [hp] at hlo hhi ⊢
  constructor <;> linarith

/-- **NO ALIAS ON THE EMPTY-STAKE-TABLE FLOOR CHAIN** (`α = 1, β = 0, γ = 1`). The `β = 0` operand
term contributes nothing to the interval, which is why pointing `bCol` at `aCol` cannot widen it. -/
theorem sol_tpos_rung_no_alias (x y d cin cout : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ SOL_LIMB_BITS) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ SOL_LIMB_BITS)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ SOL_LIMB_BITS)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ SOL_CARRY_BITS)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ SOL_CARRY_BITS) :
    -Dregg2.Circuit.Emit.EffectLower.P
        < 1 * x - 0 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
          - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ SOL_LIMB_BITS
    ∧ 1 * x - 0 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
          - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ SOL_LIMB_BITS
        < Dregg2.Circuit.Emit.EffectLower.P := by
  obtain ⟨hlo, hhi⟩ := LimbTally.rung_value_bounds SOL_LIMB_BITS SOL_CARRY_BITS 1 0 1
    LimbTally.TALLY_CARRY_OFF x y d cin cout (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LimbTally.TALLY_CARRY_OFF]) hx hy hd hcin hcout
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  simp only [SOL_LIMB_BITS, SOL_CARRY_BITS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_CARRY_BITS,
    LimbTally.TALLY_CARRY_OFF] at hlo hhi ⊢
  norm_num [hp] at hlo hhi ⊢
  constructor <;> linarith

/-! ## §4 — non-vacuous per-gate lemmas (the emitted bodies bite, both directions). -/

/-- **THE QUORUM CHAIN'S GENERATED BODIES ARE EXACTLY `ChainOk`** — this module's instance of
`LimbTally.chainBodies_zero_iff`, so the soundness below is about the bodies that SHIP rather than a
private predicate resembling them. (The replacement for the old `qDiff_body_zero_iff`, which said the
same thing about the ONE hand-written felt gate.) -/
theorem sol_qdiff_chain_zero_iff (a : Assignment) :
    LimbTally.BodiesVanish a qdiffChainBodies
      ↔ LimbTally.ChainOk SOL_LIMB_BITS 3 2 LimbTally.TALLY_CARRY_OFF a QDIFF_TOP qdiffRungs 1 0 :=
  LimbTally.chainBodies_zero_iff SOL_LIMB_BITS 3 2 1 LimbTally.TALLY_CARRY_OFF a QDIFF_TOP qdiffRungs

/-- **THE FLOOR CHAIN'S GENERATED BODIES ARE EXACTLY `ChainOk`** — the replacement for the old
`tPos_body_zero_iff`. -/
theorem sol_tpos_chain_zero_iff (a : Assignment) :
    LimbTally.BodiesVanish a tposChainBodies
      ↔ LimbTally.ChainOk SOL_LIMB_BITS 1 0 LimbTally.TALLY_CARRY_OFF a TPOS_TOP tposRungs 1 0 :=
  LimbTally.chainBodies_zero_iff SOL_LIMB_BITS 1 0 1 LimbTally.TALLY_CARRY_OFF a TPOS_TOP tposRungs

/-- `edBody = 0 ↔ ED_OK = 1`. -/
theorem ed_body_zero_iff (a : Assignment) : edBody.eval a = 0 ↔ a ED_OK = 1 := by
  simp only [edBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `stakeBody = 0 ↔ STAKE_TABLE_OK = 1`. -/
theorem stake_body_zero_iff (a : Assignment) : stakeBody.eval a = 0 ↔ a STAKE_TABLE_OK = 1 := by
  simp only [stakeBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `rootedBody = 0 ↔ ROOTED_OK = 1`. -/
theorem rooted_body_zero_iff (a : Assignment) : rootedBody.eval a = 0 ↔ a ROOTED_OK = 1 := by
  simp only [rootedBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `authBody = 0 ↔ AUTH_OK = 1`. -/
theorem auth_body_zero_iff (a : Assignment) : authBody.eval a = 0 ↔ a AUTH_OK = 1 := by
  simp only [authBody, EmittedExpr.eval]; constructor <;> intro h <;> omega

/-! ## §5 — `airAccepts`: the descriptor's LOGIC-acceptance predicate + the REFINEMENT to
`solVerifyDecision`. -/

/-- **`airAccepts a`** — the emitted verify-logic gates all vanish on row `a`, and each of the two
comparisons' difference limbs lies in `[0, 2^16)` (the denotation `range_row_mem_iff` connects the
emitted lookups to). The published-anchor pins are the addressing layer, orthogonal to the logic.

⚑ Each single-felt slack conjunct became a PAIR: the generated chain's bodies vanish, and the
difference limb vector is contained. Together those are the inequality at ANY tally a `u64` holds —
see `LimbTally.cmp_sound`. -/
def airAccepts (a : Assignment) : Prop :=
  LimbTally.BodiesVanish a qdiffChainBodies
  ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols qdiffRungs QDIFF_TOP)
  ∧ LimbTally.BodiesVanish a tposChainBodies
  ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP)
  ∧ edBody.eval a = 0
  ∧ stakeBody.eval a = 0
  ∧ rootedBody.eval a = 0
  ∧ authBody.eval a = 0

/-- **THE REFINEMENT (soundness): a satisfying AIR witness ENTAILS `solVerifyDecision` accept.** Fed a
row `a` whose columns read the update's true projections (the honest-witness relation — the two stakes
as 16-bit LIMB VECTORS, the carrier/gate bits as `if · then 1 else 0`), if the emitted verify-logic
gates accept, then the exported scalar decision `solVerifyDecision` accepts.

⚑ The quorum chain discharges the `≥ 2/3` threshold and the floor chain discharges `total > 0`, and
NEITHER hypothesis bounds a tally: `LimbTally.emitted_chain_sound` reads the five generated gates and
the five difference-limb containments and returns the inequality over the LIMB VALUES. That bound was
the whole capability limit, and it is gone. -/
theorem solLcAir_sound (a : Assignment)
    (rootedStk totalStk : Nat) (edB stakeB rootedB authB : Bool)
    (hr : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols qdiffRungs) = (rootedStk : ℤ))
    (ht : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.bCols qdiffRungs) = (totalStk : ℤ))
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hstk : a STAKE_TABLE_OK = (if stakeB then (1 : ℤ) else 0))
    (hrooted : a ROOTED_OK = (if rootedB then (1 : ℤ) else 0))
    (hauth : a AUTH_OK = (if authB then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    solVerifyDecision rootedStk totalStk edB stakeB rootedB authB = true := by
  obtain ⟨hqBodies, hqLimbs, htBodies, htLimbs, hedB, hstkB, hrootedB, hauthB⟩ := hacc
  -- ⚑ Threshold: `1 ≤ 3·rooted − 2·total` — STRICT, AT ANY TALLY MAGNITUDE.
  have hthr : 2 * totalStk < 3 * rootedStk := by
    have hcmp := LimbTally.emitted_chain_sound hqBodies hqLimbs
    rw [hr, ht] at hcmp
    have : 2 * (totalStk : ℤ) < 3 * (rootedStk : ℤ) := by linarith
    exact_mod_cast this
  -- ⚑ Total positivity (the `EmptyStakeTable` floor): `1 ≤ 1·total − 0·total`.
  have hpos : 0 < totalStk := by
    have hcmp := LimbTally.emitted_chain_sound htBodies htLimbs
    rw [sol_tpos_reads_the_quorum_denominator, ht] at hcmp
    have hposZ : (1 : ℤ) ≤ (totalStk : ℤ) := by linarith
    have : 1 ≤ totalStk := by exact_mod_cast hposZ
    omega
  -- Carrier / gate bits.
  have hedTrue : edB = true := by
    have h : a ED_OK = 1 := (ed_body_zero_iff a).mp hedB
    rw [hed] at h; cases edB with | true => rfl | false => simp at h
  have hstkTrue : stakeB = true := by
    have h : a STAKE_TABLE_OK = 1 := (stake_body_zero_iff a).mp hstkB
    rw [hstk] at h; cases stakeB with | true => rfl | false => simp at h
  have hrootedTrue : rootedB = true := by
    have h : a ROOTED_OK = 1 := (rooted_body_zero_iff a).mp hrootedB
    rw [hrooted] at h; cases rootedB with | true => rfl | false => simp at h
  have hauthTrue : authB = true := by
    have h : a AUTH_OK = 1 := (auth_body_zero_iff a).mp hauthB
    rw [hauth] at h; cases authB with | true => rfl | false => simp at h
  -- Assemble.
  unfold solVerifyDecision
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hpos, hthr⟩, hedTrue⟩, hstkTrue⟩, hrootedTrue⟩, hauthTrue⟩

/-- **THE PAYOFF: a satisfying AIR witness ENTAILS Solana rooted-validity (no-forgery, routed through
the emitted AIR).** GIVEN the named stake-table CR carrier (`hcr`), if a row `a` reads update `u`'s true
projections under pinned anchor `ts` and the emitted verify-logic gates accept, then `u` is
Solana-ROOTED-VALID relative to `ts` — a ≥2/3 subset of the ACTIVE stake, each account's on-chain
AUTHORIZED voter genuinely signed the bank hash at the slot, each vote ROOTED, the denominator pinned to
the WS anchor. So a STARK proving `solLcVerifyDesc` carries `sol_no_forgery`: the portable, trustless
proof of Solana rooted finality — now at LIVE mainnet-beta stake magnitude rather than at tallies below
1.8e8. -/
theorem solLcAir_no_forgery (L : SolLeaf) (hcr : L.stakeTableCR)
    (ts : SolTrustedState L) (u : SolUpdate L) (a : Assignment)
    (hr : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols qdiffRungs)
      = (rootedStake L u : ℤ))
    (ht : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.bCols qdiffRungs)
      = (totalStake L u : ℤ))
    (hed : a ED_OK = (if edOk L u then (1 : ℤ) else 0))
    (hstk : a STAKE_TABLE_OK = (if stakeTableOk L ts u then (1 : ℤ) else 0))
    (hrooted : a ROOTED_OK = (if rootedOk L u then (1 : ℤ) else 0))
    (hauth : a AUTH_OK = (if authOk L u then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    SolValidAt L ts u := by
  have hdec := solLcAir_sound a (rootedStake L u) (totalStake L u)
    (edOk L u) (stakeTableOk L ts u) (rootedOk L u) (authOk L u)
    hr ht hed hstk hrooted hauth hacc
  exact solVerifyDecision_no_forgery L hcr ts u hdec

/-- **Completeness (the honest prover CAN fill the row).** For any decision-accepting projections, an
honest row that fills the two comparison chains with their true limbs and carries and the carrier/gate
bits with the true results is accepted by the emitted logic. The non-vacuity partner of soundness: the
AIR is satisfiable EXACTLY on accepted updates, not vacuously empty.

⚑ **WHAT IS NO LONGER A HYPOTHESIS, AND IT IS THE POINT OF THIS WHOLE CHANGE.** The previous version
required `3·rootedStk < 2^RANGE_BITS` AND `totalStk < 2^RANGE_BITS` — bounds on the TALLY, at 2^29 —
because each slack was one felt. Mainnet-beta's live active stake is `432650183925625587` (2^58.586);
it never satisfied either, at 29 bits or at the 128 that shipped, because a felt holds 30.9 bits
either way. **Both hypotheses are gone**, and no tally bound replaces them.

What replaces them is the honest chains themselves (`hQdiffChain`/`hQdiffLimbs`,
`hTposChain`/`hTposLimbs`), which an honest prover constructs by `LimbTally.fillDigit` /
`LimbTally.fillCarry` at ANY magnitude a `u64` holds — and `solLcAir_accepts_at_live_active_stake`
(§7) exhibits exactly that, cell for cell, at the measured live stake. -/
theorem solLcAir_complete (a : Assignment)
    (rootedStk totalStk : Nat) (edB stakeB rootedB authB : Bool)
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hstk : a STAKE_TABLE_OK = (if stakeB then (1 : ℤ) else 0))
    (hrooted : a ROOTED_OK = (if rootedB then (1 : ℤ) else 0))
    (hauth : a AUTH_OK = (if authB then (1 : ℤ) else 0))
    (hQdiffChain : LimbTally.BodiesVanish a qdiffChainBodies)
    (hQdiffLimbs :
      LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols qdiffRungs QDIFF_TOP))
    (hTposChain : LimbTally.BodiesVanish a tposChainBodies)
    (hTposLimbs : LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP))
    (hdec : solVerifyDecision rootedStk totalStk edB stakeB rootedB authB = true) :
    airAccepts a := by
  unfold solVerifyDecision at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨⟨⟨⟨_hpos, _hthr⟩, hedB⟩, hstkB⟩, hrootedB⟩, hauthB⟩ := hdec
  refine ⟨hQdiffChain, hQdiffLimbs, hTposChain, hTposLimbs, ?_, ?_, ?_, ?_⟩
  · rw [ed_body_zero_iff, hed]; simp [hedB]
  · rw [stake_body_zero_iff, hstk]; simp [hstkB]
  · rw [rooted_body_zero_iff, hrooted]; simp [hrootedB]
  · rw [auth_body_zero_iff, hauth]; simp [hauthB]

/-! ## §6 — the emitted wire JSON (byte-pinned golden) + shape pins. -/

-- The Rust decoder ingests THIS string (`parse_vm_descriptor2`); byte-pinned golden (a drift on either
-- side breaks this `#guard`). ⚑ RE-EMITTED 2026-08-03 for the limbed tallies: trace width 19 → 41,
-- constraints 19 → 51, the ONE 29-bit range table replaced by TWO width-tagged tables (16 / 8), and
-- the two hand-written felt slacks + their two lookups replaced by TEN GENERATED chain gates and
-- twenty-six per-limb lookups. Captured from this module's own `emitVmJson2`.
-- The Rust decoder ingests THIS string (`parse_vm_descriptor2`); byte-pinned golden (a drift on either
-- side breaks this `#guard`). ⚑ RE-EMITTED 2026-08-04 for the FULL-WIDTH WS anchor root and the PINNED
-- DENOMINATOR: trace width 41 → 49, PIs 11 → 23, constraints 51 → 63. The one 31-bit ANCHOR_ROOT column
-- became nine radix-`2^31` limbs (cols 30..38 → PI 0..8), the bank root and slot shifted up by 8, and the
-- four TOTAL_STK limbs gained `.piBinding`s to PI 19..22. Captured from this module's own `emitVmJson2`.
#guard emitVmJson2 solLcVerifyDesc ==
  "{\"name\":\"dregg-solana-lightclient-verify::v1\",\"ir\":2,\"trace_width\":49,\"public_input_count\":23,\"tables\":[{\"id\":85,\"name\":\"range_w16\",\"arity\":1,\"sem\":\"range\",\"bits\":16},{\"id\":77,\"name\":\"range_w8\",\"arity\":1,\"sem\":\"range\",\"bits\":8}],\"constraints\":[{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":4}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":5}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":6}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":7}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":8}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":9}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":10}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":11}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":12}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":13}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":14}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":15}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":21}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":22}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":23}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":24}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":25}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":17}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":18}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":19}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":20}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":26}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":27}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":28}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":29}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":17}}},\"r\":{\"t\":\"const\",\"v\":8388607}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":18}}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":19}}},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":11}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":7}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":20}}},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"const\",\"v\":-128}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"const\",\"v\":8388607}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":27}}},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":23}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"var\",\"v\":27}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":7}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":7}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":29}}},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}},\"r\":{\"t\":\"const\",\"v\":-128}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":30,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":31,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":32,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":33,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":34,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":35,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":36,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":37,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":38,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":39,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":40,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":41,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":42,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":43,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":44,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":45,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":46,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":47,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":48,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":19},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":20},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":21},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":22}],\"hash_sites\":[],\"ranges\":[]}"


/-- Shape pins (robust; a layout drift moves these). Converted from `#guard` per
`metatheory/docs/GUARD-DISCIPLINE.md` — a `#guard` is the same unsafe evaluation with the name, the
term and the axiom record deleted, and `decide` here is strictly stronger than the guard was. -/
theorem sol_shape_pins :
    solLcVerifyDesc.traceWidth = SOL_LC_WIDTH
      ∧ solLcVerifyDesc.piCount = PI_COUNT
      ∧ solLcVerifyDesc.constraints.length = 63
      ∧ solLcVerifyDesc.tables.length = 2 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  decide

/-- ⚑ **THE TALLY IS TWENTY-SIX LOOKUPS, NOT TWO.** Eighteen 16-bit limb checks plus eight 8-bit carry
checks, where the two single-felt slacks carried exactly ONE each. A re-emission that dropped a limb
moves this number; the old shape had no number to move. -/
theorem sol_tally_lookup_count : tallyRangeLookups.length = 26 := by decide

/-- …and each chain is FIVE generated gates for four rungs — one per rung plus the closure gate that
forces the final carry into the top difference limb. Without the closure gate the prover could dump a
residue into a carry nothing reads, and the recomposition would be off by `2^64`. -/
theorem sol_chain_gate_counts :
    qdiffChainGates.length = 5 ∧ tposChainGates.length = 5 := by decide

/-- The two crypto carriers and the two logic gates are real trace columns and none is PI-bound (the
results ride hidden). -/
theorem sol_carriers_are_hidden_columns :
    ED_OK < SOL_LC_WIDTH ∧ STAKE_TABLE_OK < SOL_LC_WIDTH
      ∧ ROOTED_OK < SOL_LC_WIDTH ∧ AUTH_OK < SOL_LC_WIDTH := by decide

/-- The tally block occupies columns 4..29 contiguously, below the published anchors: four total-stake
limbs, four rooted-stake limbs, five quorum-difference limbs, four quorum carries, five floor-difference
limbs, four floor carries. -/
theorem sol_tally_block_layout :
    TOTAL_STK_LIMB 0 = 4 ∧ TOTAL_STK_LIMB 3 = 7
      ∧ ROOTED_STK_LIMB 0 = 8 ∧ ROOTED_STK_LIMB 3 = 11
      ∧ QDIFF_LIMB 0 = 12 ∧ QDIFF_TOP = 16
      ∧ QDIFF_CARRY 0 = 17 ∧ QDIFF_CARRY 3 = 20
      ∧ TPOS_LIMB 0 = 21 ∧ TPOS_TOP = 25
      ∧ TPOS_CARRY 0 = 26 ∧ TPOS_CARRY 3 = 29
      ∧ TPOS_CARRY 3 < ANCHOR_ROOT 0 := by decide

/-- The widened rooted-bank-root anchor is unchanged by the tally work, only shifted: nine limbs,
contiguous cols 39..47 → PI 9..17, MSB-first, `⌈256/31⌉ = 9` covering the full 256 bits. -/
theorem sol_bank_root_anchor_layout :
    BANK_ROOT_LIMBS = 9 ∧ bankRootPins.length = BANK_ROOT_LIMBS
      ∧ BANK_ROOT 0 = 39 ∧ BANK_ROOT 8 = 47
      ∧ SLOT_COL = 48 ∧ PI_SLOT = 18
      ∧ PI_BANK_ROOT 0 = 9 ∧ PI_BANK_ROOT 8 = 17 ∧ PI_BANK_ROOT 8 < PI_SLOT
      ∧ BANK_ROOT 8 < SLOT_COL
      ∧ 31 * BANK_ROOT_LIMBS ≥ 256 := by decide

/-- ⚑⚑ **THE WS STAKE-TABLE ROOT IS NOW BOUND AT FULL WIDTH TOO — the felt-width close, finished.**

Nine limbs, contiguous cols 30..38 → PI 0..8, MSB-first, `31 · 9 = 279 ≥ 256`. The statement that
matters is the last conjunct: the anchor root and the bank root are bound by the SAME number of
limbs, because they are the same kind of object — a 256-bit hash — and until 2026-08-04 only one of
them was treated as one.

⚠ **This is the half of §6b's disconnection that PI width alone can close.** A full-width PI binding
stops a light client from accepting a proof whose anchor merely *collides in 31 bits* with the one
governance pinned. It does NOT make the anchor arithmetically live — see
`sol_bank_root_and_slot_remain_arithmetically_inert` for what is still open, and §6c for what closing
it would cost. -/
theorem sol_anchor_root_is_bound_at_full_width :
    ROOT_LIMBS = 9 ∧ anchorRootPins.length = ROOT_LIMBS
      ∧ ANCHOR_ROOT 0 = 30 ∧ ANCHOR_ROOT 8 = 38
      ∧ PI_ANCHOR_ROOT 0 = 0 ∧ PI_ANCHOR_ROOT 8 = 8
      ∧ ANCHOR_ROOT 8 < BANK_ROOT 0
      ∧ 31 * ROOT_LIMBS ≥ 256
      ∧ ROOT_LIMBS = BANK_ROOT_LIMBS := by decide

/-! ## §6b — ⚑⚑ WHAT THIS AIR DOES **NOT** BIND: the published anchors, measured rather than
described.

The header calls the anchor binding a "NOT-YET-CLOSED named residual". That was prose, and prose is
not a gate (`feedback-a-documented-wound-is-not-a-detected-one`). This section makes it a decidable
fact about the EMITTED object, so it reds the day the in-AIR-crypto iteration lands.

⚑ **The fact was stronger than the prose was.** The residual was written as "the anchors are published
but not yet arithmetically bound to the CARRIER BITS". Measured on the emitted constraint list, the
eleven PI-bound columns occurred in **no gate body and no lookup tuple at all** — not tied to the
carriers, not tied to the tally, not tied to EACH OTHER. `solLcVerifyDesc` decomposed into
arithmetically DISCONNECTED islands:

    {0} {1} {2} {3}            — four carrier/gate bits, each forced `= 1`, each alone
    {4 … 29}                   — the tally block: two u64 limb vectors + two comparison chains
    {30} {31} … {40}           — eleven published anchors, each a singleton pinned to one PI

So a verifying proof of this descriptor said: *the prover exhibited a `(total, rooted)` pair
satisfying `total ≥ 1` and `3·rooted > 2·total`, set four bits to 1, and separately exhibited eleven
public field elements.* **Nothing in the emitted object related those eleven values — the claimed
bank hash and slot — to the tally, or to anything.** The quorum arithmetic was real; what it was
arithmetic ABOUT was chosen by the prover.

⚑⚑ **2026-08-04 — ONE OF THE THREE ISLANDS IS NOW JOINED, AND BOTH TRIPWIRES FIRED SAYING SO.** The
denominator is PI-bound (`totalStakePins`), so the tally block and the anchor block share columns
4..7 and the decomposition is now:

    {0} {1} {2} {3}            — four carrier bits, each forced `= 1`, each alone (UNCHANGED)
    {4 … 29} ∪ {PI 19..22}     — the tally, whose DENOMINATOR is published
    {30 … 38}                  — nine WS anchor-root limbs (was ONE 31-bit column)
    {39 … 47} {48}             — bank-root limbs and slot, still singletons (UNCHANGED)

What a verifying proof now says that it did not before: *the total active stake this quorum is a
fraction of is the one in the public statement.* What it STILL does not say: which validators, or that
the bank hash is anything in particular.

⚠ This is not a defect in `solLcAir_no_forgery` — read that theorem's HYPOTHESES. `hr`, `ht`, `hed`,
`hstk`, `hrooted`, `hauth` say "row `a` reads update `u`'s TRUE projections", and they are supplied
from OUTSIDE the circuit. The theorem is exactly "if the trace honestly encodes the real update, then
acceptance entails validity", and the emitted object cannot check the antecedent. That is the whole
content of "witnessed carrier", and it is the same posture as `LightClientMinaAir`'s `LINK_OK` /
`PICKLES_OK`. Measured 2026-08-03, the identical decomposition holds for the Midnight and Tendermint
descriptors. -/

/-- The trace columns an `EmittedExpr` reads. -/
def exprCols : EmittedExpr → List Nat
  | .var c    => [c]
  | .const _  => []
  | .add l r  => exprCols l ++ exprCols r
  | .mul l r  => exprCols l ++ exprCols r

/-- The trace columns a constraint ARITHMETICALLY relates. A `piBinding` contributes NOTHING here on
purpose: it ties a column to a public input, not to another column, so it cannot connect the anchor
block to the tally. That asymmetry is exactly what this section is measuring. -/
def constraintCols : VmConstraint2 → List Nat
  | .base (.gate b)          => exprCols b
  | .base (.boundary _ b)    => exprCols b
  | .lookup l                => l.tuple.flatMap exprCols
  | _                        => []

/-- The twenty-three PI-bound columns: the NINE WS anchor-root limbs, the nine bank-root limbs, the
slot, and — since 2026-08-04 — the FOUR total-stake limbs the quorum divides by. -/
def publicAnchorCols : List Nat :=
  [ANCHOR_ROOT 0, ANCHOR_ROOT 1, ANCHOR_ROOT 2, ANCHOR_ROOT 3, ANCHOR_ROOT 4,
   ANCHOR_ROOT 5, ANCHOR_ROOT 6, ANCHOR_ROOT 7, ANCHOR_ROOT 8,
   BANK_ROOT 0, BANK_ROOT 1, BANK_ROOT 2, BANK_ROOT 3, BANK_ROOT 4,
   BANK_ROOT 5, BANK_ROOT 6, BANK_ROOT 7, BANK_ROOT 8, SLOT_COL,
   TOTAL_STK_LIMB 0, TOTAL_STK_LIMB 1, TOTAL_STK_LIMB 2, TOTAL_STK_LIMB 3]

/-! ### ⚑⚑ 2026-08-04 — THE TWO DISCONNECTION TRIPWIRES FIRED. This is what replaced them.

`sol_public_anchors_are_arithmetically_inert` and `sol_tally_block_reads_no_carrier_and_no_anchor`
were `by decide` and are GONE, because `decide` proved both FALSE the moment `totalStakePins` landed:

    error: Tactic `decide` proved that the proposition
      ∀ c ∈ solLcVerifyDesc.constraints, ∀ col ∈ constraintCols c, col ∉ publicAnchorCols
    is false

That is the mechanism working exactly as the lane that wrote them intended — they were built to red
on the day a published anchor became arithmetically live, and they did, without anyone remembering to
go looking. The replacements below are the POSITIVE form: not "nothing is connected" but "THIS is
connected, and THAT still is not." -/

/-- ⚑⚑ **THE QUORUM ARITHMETIC READS A PUBLISHED ANCHOR — the disconnection, broken.** There EXISTS a
quorum-chain gate whose body reads a column that is PI-bound. This is the exact negation of the
retired `sol_public_anchors_are_arithmetically_inert`, and it is the statement that lane asked for:
the tally block and the published-anchor block are no longer separate islands.

The column is `TOTAL_STK_LIMB 0` — the denominator. The prover exhibits a `(total, rooted)` pair, and
`total` is now part of what the proof PUBLICLY CLAIMS rather than something it privately picked. -/
theorem sol_quorum_reads_a_published_anchor :
    ∃ c ∈ solLcVerifyDesc.constraints, ∃ col ∈ constraintCols c, col ∈ publicAnchorCols := by
  decide

/-- ⚑ **EVERY TOTAL-STAKE LIMB IS PI-BOUND** — the denominator is published in full, not in part. Four
limbs, four distinct PI slots; a proof that pins three of four would let the prover move the fourth. -/
theorem sol_denominator_is_fully_pinned :
    totalStakePins.length = 4
      ∧ (∀ i ∈ [0, 1, 2, 3], TOTAL_STK_LIMB i ∈ publicAnchorCols)
      ∧ PI_TOTAL_STK 0 = 19 ∧ PI_TOTAL_STK 3 = 22
      ∧ PI_TOTAL_STK 3 < PI_COUNT := by decide

/-- ⚑ **AND THE HALF THAT IS STILL OPEN, KEPT AS A TRIPWIRE IN THE SAME SHAPE.** The nine bank-root
limbs and the slot are STILL read by no gate body and no lookup tuple: the claimed bank hash and
rooted slot are carried THROUGH the proof, not constrained BY it. `ED_OK` derived from the vote
message built on `BANK_ROOT` + `SLOT` is what would close this, and it is the Ed25519/EC arc — not
priced here.

⚠ **TRIPWIRE, and it is meant to go red**, on exactly the terms its predecessor did. Deleting it when
the Ed25519 arc lands is the correct move; weakening it is not. -/
theorem sol_bank_root_and_slot_remain_arithmetically_inert :
    ∀ c ∈ solLcVerifyDesc.constraints, ∀ col ∈ constraintCols c,
      col ∉ [BANK_ROOT 0, BANK_ROOT 1, BANK_ROOT 2, BANK_ROOT 3, BANK_ROOT 4,
             BANK_ROOT 5, BANK_ROOT 6, BANK_ROOT 7, BANK_ROOT 8, SLOT_COL] := by
  decide

/-- ⚑ **THE WS ANCHOR ROOT IS ALSO STILL ARITHMETICALLY INERT** — stated SEPARATELY from the bank
root because the two are closed by different work and must be able to red on different days. Widening
it to nine limbs (`sol_anchor_root_is_bound_at_full_width`) fixed what the light client COMPARES; it
did not make any gate read it. `STAKE_TABLE_OK` derived from the stake-table fold into `ANCHOR_ROOT`
is what would close this, and §6c is why that is not this commit. -/
theorem sol_anchor_root_remains_arithmetically_inert :
    ∀ c ∈ solLcVerifyDesc.constraints, ∀ col ∈ constraintCols c,
      col ∉ [ANCHOR_ROOT 0, ANCHOR_ROOT 1, ANCHOR_ROOT 2, ANCHOR_ROOT 3, ANCHOR_ROOT 4,
             ANCHOR_ROOT 5, ANCHOR_ROOT 6, ANCHOR_ROOT 7, ANCHOR_ROOT 8] := by
  decide

/-- ⚑ …and the four carrier/gate bits are still read by NOTHING but their own forcing gates, so no
arithmetic anywhere else in the descriptor depends on them. Each is a one-column island (`ED_OK` is
read only by `edBody`, and so on). This half of the old measurement is UNCHANGED by this pass. -/
theorem sol_carriers_are_one_column_islands :
    ∀ c ∈ (qdiffChainGates ++ tposChainGates ++ tallyRangeLookups),
      ∀ col ∈ constraintCols c,
        col ∉ [ED_OK, STAKE_TABLE_OK, ROOTED_OK, AUTH_OK] := by
  decide

/-! ## §6c — ⚑⚑ WHY `STAKE_TABLE_OK` IS STILL A CARRIER: the SHA-256 fold, PRICED.

`LightClientSolHashFold` computes the stake-table fold that would DERIVE `STAKE_TABLE_OK` from
`ANCHOR_ROOT`, and gives its exclusion as RESIDUAL #3 (`LightClientSolHashFold.lean:53-56`): *"the
chained SHA fold cannot be flat-merged into `solLcVerifyDesc`'s byte-golden `emitVmJson2` …
`solLcVerifyDesc` and its golden are UNTOUCHED — NO VK regen."*

⚠ **THAT REASON IS NOT THE REAL ONE, AND IT IS THE KIND THIS REPO FORBIDS.** "byte-golden", "UNTOUCHED",
"NO VK regen" are compatibility costs, and `CLAUDE.md` is explicit that a re-emit and a VK rotation are
ordinary work here, not objections. This descriptor's golden was re-emitted twice in the eight days
before this note. If a byte-golden were the only thing between us and the binding, the binding would
be in.

⚑ **The real reason is COST, and it was never stated as a number. Measured 2026-08-04**, by evaluating
the emitters in `Sha256MerkleFold` rather than reading their docblocks:

| object | constraints | trace columns |
|---|---|---|
| `feedForward` | 288 | — |
| `sha256Block` (schedule ‖ compress ‖ feed-forward) | **40,928** | **29,096** |
| `sha256PairHash` (2 blocks + IV/pad pins) | **82,648** | **59,216** |
| **this whole descriptor** | **63** | **49** |

⚠ The docblocks in `LightClientSolHashFold` and both ETH folds say *"~30k gates/block"*. The measured
figure is **40,928** — understated by 36%, and it is the number three files reason from.

At live validator count — **703 vote accounts** (691 current + 12 delinquent), measured 2026-08-04 via
`getVoteAccounts` on `api.mainnet-beta.solana.com`, the same query §7's stake figure comes from — the
deployed `EpochStakeTable::root` preimage (`bridge/src/solana_consensus.rs:196-206`: a 32-byte tag,
`epoch`, the row count, then 40 bytes per row) is 28,168 bytes = **441 SHA-256 blocks**:

  * **18,049,248 constraints / 12,831,336 columns.**

The Lean model's shape (`chainCommit ∘ map solRowLeaf`, one `pairHash` per row) is worse still —
**58,101,544 / 41,628,848** — because it spends two blocks on each 64-byte row-pair. (⚠ These are two
DIFFERENT functions: `root()` is a FLAT hash over one preimage, `chainCommit` a Merkle–Damgård chain
over per-row leaf digests. `LightClientSolHashFold` RESIDUAL #2 names the gap; the pricing above gives
both so neither reading flatters the result.)

Against the ceiling this stack has actually reached: **2,131 columns** parse, check and prove
(`circuit/tests/pasta_derive_prove.rs::the_v1_width_cap_does_not_bind_the_ir2_path`), and the widest
descriptor ever emitted in this tree is 15,611 (`shielded-whole-note-swap-substrate-v1`). **ONE
SHA-256 block is 29,096 columns — 13.6× the proved ceiling and 1.9× the widest object that exists.**
The fold is out of reach at 703 rows, at 2 rows, and at ONE block. `MAX_TRACE_WIDTH = 1024` is NOT
what excludes it (that cap is v1-DSL and advisory on the IR-v2 path, `PastaMsmAir` §5b item 5); the
gadget's own size is.

⚑ **AND THE CHEAP PATH EXISTS, IS NOT SHA, AND IS NOT MENTIONED ANYWHERE IN THE FOLD FILES.** A
Poseidon2 hash in this stack is **ONE `VmConstraint2.lookup`** on the `TID_P2_NARROW` chip bus — the
permutation lives in a separate chip AIR, so the main descriptor pays a lookup and an output column,
not 40,928 gates (`Poseidon2HashEmit.poseidon2HashDesc` is trace width **3**, four constraints, for a
whole hash). Poseidon2-over-BabyBear is the prover's OWN hash. A 703-row stake-table fold on that bus
is ~703 lookups — the scale of the descriptors this tree already emits and proves (1,604–1,817
constraints), not 18 million.

**So the honest status of `STAKE_TABLE_OK` is not "too expensive to derive" — it is "expensive in the
hash we happened to pick, and the commitment is ours to pick."** `EpochStakeTable::root` is
dregg-authored (`STAKE_TABLE_ROOT_TAG = b"dregg-solana-stake-table-root:v1"`), pinned by a
dregg-authored `WeakSubjectivityAnchor`, and greenfield says the format is not a constraint. Two named
things stand between here and that binding, and neither is a compatibility cost:

  1. **The chip's committed digest is ONE felt** — 31 bits, a `2^15.5` birthday bound, not a binding
     commitment. `CHIP_OUT_LANES = 8` lanes are carried and bound to the genuine permutation but
     *"NOT yet folded into any commitment"* (`DescriptorIR2.lean:169-176`, Phase B-ROTATION). An
     8-lane (248-bit) commitment is the prerequisite, and it is someone's named next phase.
  2. **The absorb arity is not free** — `Ir2Air::Chip` admits only `{0,2,3,4,7,11,16}` as a degree-7
     product, and a descriptor at any other arity is UNPROVABLE rather than merely inefficient
     (`DescriptorIR2.lean` §"THE ADMITTED ABSORB ARITIES"). A row of 9 pubkey limbs + 3 stake limbs is
     12 felts and must be laid out at 11 or 16.

That is the work. It is a re-commitment and a chip phase, not a research problem — and it is emphatically
not "the golden bytes are frozen." -/

/-! ## §7 — ⚑ THE MEASUREMENT: MAINNET-BETA'S LIVE ACTIVE STAKE, AT THE QUORUM BOUNDARY.

This is the section the whole change exists for. Everything below is a NAMED THEOREM over an explicit
row of the emitted descriptor — the same row, cell for cell, a Rust trace filler hands the deployed
prover.

`totalStk = 432650183925625587` is mainnet-beta's ACTIVE stake, MEASURED LIVE 2026-08-03 via
`getVoteAccounts` on `api.mainnet-beta.solana.com` (689 current + 14 delinquent vote accounts, epoch
1011, slot 436,909,708): 432.650M SOL, `2^58.586`, 214.9 million times the BabyBear modulus. It never
fit a column.

⚑ And the two cases below differ by **ONE LAMPORT OUT OF 4.3e17**: `rootedStk = 288433455950417059`
is the SMALLEST value satisfying agave's STRICT `3·rooted > 2·total`; `288433455950417058` is one
below it — the EXACT-2/3 point — and must be REJECTED. The first ACCEPTS, the second has no
satisfying assignment.

⚑⚑ **That one lamport is the whole strictness repair, exhibited.** `288433455950417058` is precisely
the value the shipped `γ = 0` accepted and agave refuses (`3·R = 865300367851251174 = 2·T` exactly),
so the refusal below is not a new boundary — it is the OLD boundary moved to where the reference
client's is. -/

/-- The honest row at live mainnet-beta scale, as the cell vector a Rust harness fills. Written as a
LIST so the Lean row and the Rust trace row are literally the same 41 numbers in the same order — a
divergence between the two is a diff on one object, not a comparison of two readings.

⚑ Note the QUORUM CARRIES: `[127, 127, 130, 128]` is `[−1, −1, +2, 0]` offset by 128 — two rungs
BORROW and one carries `+2`, so the chain is not trivially satisfied. ⚑ The quorum difference now
denotes `3·R − 2·T − 1 = 2` rather than the `0` the non-strict fill produced; live active stake is
divisible by 3, so the STRICT minimum overshoots the ratio by exactly one lamport of rooted stake
(three of difference, minus the `γ = 1`). -/
def solMaxScaleCells : List ℤ :=
  [ 1, 1, 1, 1                       -- ED_OK, STAKE_TABLE_OK, ROOTED_OK, AUTH_OK
  , 62195, 52452, 5388, 1537         -- TOTAL_STK  limbs = 432650183925625587 (live active stake)
  , 19619, 13123, 47283, 1024        -- ROOTED_STK limbs = 288433455950417059 (minimal STRICT quorum)
  , 2, 0, 0, 0, 0                    -- QDIFF      limbs = 3·R − 2·T − 1 = 2
  , 127, 127, 130, 128               -- QDIFF carries, offset (honest carries −1, −1, +2, 0)
  , 62194, 52452, 5388, 1537, 0      -- TPOS       limbs = T − 1 = 432650183925625586
  , 128, 128, 128, 128               -- TPOS carries, offset (honest carry 0 rides as 128)
  , 11, 22, 33, 44, 55, 66, 77, 88, 99  -- ANCHOR_ROOT limbs 0..8 (the WS stake-table root, MSB-first)
  , 1, 2, 3, 4, 5, 6, 7, 8, 9        -- BANK_ROOT limbs 0..8
  , 436909708 ]                      -- SLOT_COL (the measured live slot)

/-- The row is exactly as wide as the descriptor. -/
theorem solMaxScaleCells_width : solMaxScaleCells.length = SOL_LC_WIDTH := by decide

/-- The row as an `Assignment`. -/
def solMaxScaleRow : Assignment := fun i => solMaxScaleCells.getD i 0

/-- ⚑ **THE TALLY THE ROW DENOTES IS MAINNET-BETA'S LIVE ACTIVE STAKE.** Four 16-bit limbs, read by
`limbValue`, recompose to `432650183925625587` exactly. -/
theorem solMaxScaleRow_total_is_live_active_stake :
    LimbTally.limbValue SOL_LIMB_BITS solMaxScaleRow (LimbTally.bCols qdiffRungs)
      = 432650183925625587 := by decide

/-- …and the rooted stake is the SMALLEST STRICT `> 2/3` quorum of it. -/
theorem solMaxScaleRow_rooted_is_minimal_quorum :
    LimbTally.limbValue SOL_LIMB_BITS solMaxScaleRow (LimbTally.aCols qdiffRungs)
      = 288433455950417059 := by decide

/-- …which really is minimal: the STRICT `2·T < 3·R` holds at `R`, and FAILS one lamport below.

⚑ **And the value one lamport below is the EXACT-2/3 point** — `3 · 288433455950417058` is
`865300367851251174`, which is `2 · 432650183925625587` on the nose. So the third conjunct records
what the shipped non-strict rule did with it: ACCEPT. The repair is exactly this one row flipping. -/
theorem minimal_quorum_is_minimal :
    2 * 432650183925625587 < 3 * 288433455950417059
      ∧ ¬ (2 * 432650183925625587 < 3 * 288433455950417058)
      ∧ 3 * 288433455950417058 = 2 * 432650183925625587
      ∧ 2 * 432650183925625587 ≤ 3 * 288433455950417058 := by decide

/-- …and the floor chain's difference vector denotes `total − 1`, so the `EmptyStakeTable` floor is
carrying the same denominator the quorum does. -/
theorem solMaxScaleRow_floor_difference_is_total_minus_one :
    LimbTally.limbValue SOL_LIMB_BITS solMaxScaleRow (LimbTally.diffCols tposRungs TPOS_TOP)
      = 432650183925625586 := by decide

/-- ⚑⚑ **THE DELIVERABLE: THE EMITTED AIR ACCEPTS A VALIDATOR SET AT MAINNET-BETA'S LIVE STAKE.**

Every gate of `solLcVerifyDesc` vanishes on this row and every limb tooth admits it. At a single felt
this update could not be REPRESENTED, let alone accepted: `3·rootedStk = 865300367851251174` is 429.8
million times the BabyBear modulus, so no declared width — 29, 30, 64, or the 128 that shipped — ever
made it provable. -/
theorem solLcAir_accepts_at_live_active_stake : airAccepts solMaxScaleRow := by
  refine ⟨?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩
  · decide
  · decide
  · decide
  · decide

/-- ⚑⚑ **THE EXACT-2/3 POINT IS REFUSED AT LIVE MAINNET SCALE — the strictness repair, as a theorem
about the emitted object.**

At `rootedStk = 288433455950417058` the ratio is EXACTLY 2/3 (`3·R = 2·T = 865300367851251174`), so
the strict difference `3·R − 2·T − 1` is `−1`, and `LimbTally.emitted_chain_refuses` gives: NO
assignment of difference limbs and carries satisfies the chain together with the containments. There
is no limb vector of non-negative limbs denoting `−1`.

⚑ **This row PROVED before the repair.** It is the value the shipped `γ = 0` accepted, and the value
agave's `>` refuses. Below-the-boundary sub-quorums (`solLcAir_refuses_strict_sub_quorum`) were
already refused; this one was not. -/
theorem solLcAir_refuses_the_exact_two_thirds_point_at_live_active_stake (a : Assignment)
    (hTotal : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.bCols qdiffRungs)
      = 432650183925625587)
    (hRooted : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols qdiffRungs)
      = 288433455950417058) :
    ¬ (LimbTally.BodiesVanish a qdiffChainBodies
        ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols qdiffRungs QDIFF_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal, hRooted]; norm_num

/-- ⚑ **AND THE QUORUM TOOTH SURVIVED THE WIDENING, AT THE SAME SCALE.** Two lamports below the
minimal strict quorum (`rootedStk = 288433455950417057`) the strict difference is `−4`, refused for
the same structural reason. Not "the wrapped value lands outside an interval" — there is no limb
vector of non-negative limbs denoting `−4`.

⚠ This is the exact failure mode to watch for — a wider representation re-admitting the sub-quorum. It
does not, and the reason is structural rather than arithmetic-on-`p`. -/
theorem solLcAir_refuses_strict_sub_quorum (a : Assignment)
    (hTotal : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.bCols qdiffRungs)
      = 432650183925625587)
    (hRooted : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols qdiffRungs)
      = 288433455950417057) :
    ¬ (LimbTally.BodiesVanish a qdiffChainBodies
        ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols qdiffRungs QDIFF_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal, hRooted]; norm_num

/-- ⚑⚑ **THE EMPTY STAKE TABLE IS REFUSED — the check that FAILED, closed for a reason that does not
mention the field.**

At `totalStk = 0` the floor difference is `1·0 − 0·0 − 1 = −1`, and no limb vector of non-negative
limbs denotes `−1`. The 128-bit table ADMITTED this (`sol_empty_stake_table_was_admitted_at_128`: the
slack rode as `p − 1 = 2013265920`, inside `[0, 2^128)`), so a stake table with no stake in it passed
its own emptiness floor and — with `rootedStk = 0` too, giving quorum slack `0` at the then-`γ = 0` —
a block signed by nobody satisfied both teeth. The 29-bit narrowing refused it because `p − 1 ≥ 2^29`,
a fact about the FIELD. This refuses it because `1 ≤ 0` is false.

⚑ **This is no longer the only gate standing there.** `solLcAir_quorum_also_refuses_the_empty_stake_table`
refuses the same row from the QUORUM chain's own columns, once `γ = 1` made the quorum strict — and
`sol_two_teeth_are_independent` records that neither tooth subsumes the other. -/
theorem solLcAir_refuses_the_empty_stake_table (a : Assignment)
    (hTotal : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols tposRungs) = 0) :
    ¬ (LimbTally.BodiesVanish a tposChainBodies
        ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal]; norm_num

/-- …and the HONEST side of that same floor is admitted at live scale: the row above satisfies the
floor chain and its containments, at `total = 432650183925625587`. Both polarities on one tooth. -/
theorem solLcAir_admits_the_nonempty_stake_table :
    LimbTally.BodiesVanish solMaxScaleRow tposChainBodies
      ∧ LimbTally.LimbsInRange SOL_LIMB_BITS solMaxScaleRow
          (LimbTally.diffCols tposRungs TPOS_TOP) := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- ⚑ **THE CAPACITY PAIR, AS THE TWO NUMBERS THAT MATTER.** Live active stake fits a `u64` — that is
what four 16-bit limbs buy — and exceeds the BabyBear modulus by a factor of **214,899,670**, which is
what one column never could. Both halves stated together so the flattering one cannot be quoted
alone. -/
theorem sol_live_stake_capacity_pair :
    (432650183925625587 : ℤ) < (2 : ℤ) ^ 64
      ∧ (214899670 : ℤ) * Dregg2.Circuit.Emit.EffectLower.P < 432650183925625587 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- Carriers / gates: a set bit accepts; a cleared (forged / optimistic / imposter) bit is refused.
Converted from four `#guard` pairs into one named theorem with both polarities. -/
theorem sol_carrier_bits_discriminate :
    (edBody.eval (fun i => if i = ED_OK then 1 else 0) = 0 ∧ edBody.eval (fun _ => 0) ≠ 0)
      ∧ (stakeBody.eval (fun i => if i = STAKE_TABLE_OK then 1 else 0) = 0
          ∧ stakeBody.eval (fun _ => 0) ≠ 0)
      ∧ (rootedBody.eval (fun i => if i = ROOTED_OK then 1 else 0) = 0
          ∧ rootedBody.eval (fun _ => 0) ≠ 0)
      ∧ (authBody.eval (fun i => if i = AUTH_OK then 1 else 0) = 0
          ∧ authBody.eval (fun _ => 0) ≠ 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩⟩

/-! ## §8 — axiom hygiene. -/

#assert_axioms sol_qdiff_chain_zero_iff
#assert_axioms sol_tpos_chain_zero_iff
#assert_axioms ed_body_zero_iff
#assert_axioms stake_body_zero_iff
#assert_axioms rooted_body_zero_iff
#assert_axioms auth_body_zero_iff
#assert_axioms sol_limb_inRange_iff_mem_rangeRows
#assert_axioms sol_carriers_are_hidden_columns
#assert_axioms solLcAir_sound
#assert_axioms solLcAir_no_forgery
#assert_axioms solLcAir_complete
-- The HISTORICAL width record: both direction theorems + the exhibited admitted-then-refused value.
#assert_axioms sol_range_is_inside_the_field
#assert_axioms sol_wrapped_slack_is_outside_the_range
#assert_axioms sol_empty_stake_table_was_admitted_at_128
#assert_axioms sol_empty_stake_table_was_refused_at_29_bits
-- ⚑ The limbed tallies: capability, the field-free refusals, the emitted shape.
#assert_axioms sol_tally_capacity_holds_live_active_stake
#assert_axioms sol_live_active_stake_does_not_fit_a_felt
#assert_axioms sol_quorum_refusal_is_field_independent
#assert_axioms sol_empty_stake_refusal_is_field_independent
-- ⚑ THE SECOND TOOTH: the strict quorum refuses the empty stake table on its own, and neither
-- tooth subsumes the other.
#assert_axioms solLcAir_quorum_also_refuses_the_empty_stake_table
#assert_axioms sol_two_teeth_are_independent
#assert_axioms sol_tpos_reads_the_quorum_denominator
#assert_axioms sol_qdiff_rung_no_alias
#assert_axioms sol_tpos_rung_no_alias
#assert_axioms sol_declared_tables
#assert_axioms sol_range_table_is_not_declared
#assert_axioms sol_tally_table_wire_ids
#assert_axioms sol_shape_pins
#assert_axioms sol_tally_lookup_count
#assert_axioms sol_chain_gate_counts
#assert_axioms sol_tally_block_layout
#assert_axioms sol_bank_root_anchor_layout
-- ⚑ THE MEASUREMENT.
#assert_axioms solMaxScaleCells_width
#assert_axioms solMaxScaleRow_total_is_live_active_stake
#assert_axioms solMaxScaleRow_rooted_is_minimal_quorum
#assert_axioms minimal_quorum_is_minimal
#assert_axioms solMaxScaleRow_floor_difference_is_total_minus_one
#assert_axioms solLcAir_accepts_at_live_active_stake
#assert_axioms solLcAir_refuses_the_exact_two_thirds_point_at_live_active_stake
#assert_axioms solLcAir_refuses_strict_sub_quorum
#assert_axioms solLcAir_refuses_the_empty_stake_table
#assert_axioms solLcAir_admits_the_nonempty_stake_table
#assert_axioms sol_live_stake_capacity_pair
#assert_axioms sol_carrier_bits_discriminate
-- ⚑⚑ WHAT IS NOT BOUND — the residual, as a decidable fact about the emitted object rather than a
-- sentence in the header. Both are TRIPWIRES: they red when the in-AIR-crypto iteration lands.
#assert_axioms sol_anchor_root_is_bound_at_full_width
#assert_axioms sol_quorum_reads_a_published_anchor
#assert_axioms sol_denominator_is_fully_pinned
#assert_axioms sol_bank_root_and_slot_remain_arithmetically_inert
#assert_axioms sol_anchor_root_remains_arithmetically_inert
#assert_axioms sol_carriers_are_one_column_islands

#print axioms solLcAir_sound
#print axioms solLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientSolanaAir
