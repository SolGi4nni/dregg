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
  * IN-AIR since 2026-08-04 (the fold, absorbed): the STAKE TABLE ITSELF — one row per entry, two
    arity-16 Poseidon2 chip absorbs per row, a seeded eight-lane root chain and a four-limb `u64`
    accumulator. The published anchor root and the published denominator are both the LAST row's
    values, so the quorum's denominator is what the committed table adds up to.
  * NAMED verified CARRIERS (witnessed boolean columns, forced `= 1`):
      - `ED_OK`         — the aggregate ed25519 verify over the counted authorized voters + the vote
        message `(slot, bankHash)` (`ed25519_dalek` / a verified realization).
      ⚑ `STAKE_TABLE_OK` was the second one and is **DELETED**: the fold computes what it asserted.

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

## ⚑⚑ 2026-08-04, SECOND PASS: THE STAKE-TABLE FOLD IS **INSIDE** THIS DESCRIPTOR

This descriptor is **MULTI-ROW**: one row per stake-table entry. Its columns 0..43 are
`dregg-solana-stake-table-fold::v1`'s columns, built from the SAME source leg list (`foldLegs`), and
the two numbers a Solana light client's trust story hangs from are now DERIVED from those rows:

  * **`ANCHOR_ROOT` is the fold's eight `.last` output lanes** (`PI[0..7]`). The weak-subjectivity
    stake-table root the light client compares against governance is the IMAGE of the exhibited rows.
  * **The active-stake DENOMINATOR is the fold's accumulator** (`ACC`, `PI[18..21]`, `.last`). The
    quorum's `β` operand has no columns of its own; it reads what the rows add up to.

⚠ **`STAKE_TABLE_OK` IS DELETED.** It was a witnessed bit forced `= 1` asserting the sentence the
fold now computes, and this repo does not keep no-ops. `LightClientSolStakeFoldAir.
solLcAir_table_carrier_from_the_fold` discharges the bridge's `stakeTableOk` from the emitted pin.

## Public inputs (the addressing layer — what the proof is ABOUT)

`PI[0..7]  = ANCHOR_ROOT[0..7]` — ⚑⚑ the WS stake-table root, as the fold's EIGHT `.last` output
                            lanes. `8 · log₂ p = 247.255128` bits of image ⇒ the bound that governs an
                            equivocating prover (who needs two tables with one root) is the BIRTHDAY
                            COLLISION figure **`2^123.63`**. ⚠ NOT the `~2^247.3` second-preimage
                            figure for the same object.
                            ⚑ It was ONE column (a 256-bit SHA-256 root compared at 31 bits), then
                            NINE `.first` radix-`2^31` limbs that bound the full width and were read
                            by no constraint at all.
`PI[8..16] = BANK_ROOT[0..8]` — the claimed ROOTED bank/state hash B at slot S, as its NINE
                            radix-`2^31` MSB-first limbs (`⌈256/31⌉ = 9`). ⚠ STILL read by no gate.
`PI[17]    = SLOT`           — the rooted slot S. ⚠ STILL read by no gate.
`PI[18..21] = TOTAL_STK[0..3]` — ⚑⚑ the ACTIVE-STAKE DENOMINATOR, `.last`-pinned from the fold's
                            accumulator. Before 2026-08-04 morning the prover chose it; between then
                            and this commit it was published but not derived, so *a swap to a
                            different validator set with the SAME total was not refused*
                            (`solana_lightclient_proves.rs::a_swapped_stake_table_is_arithmetically
                            _perfect` exhibited one). It is refused now, because the table whose rows
                            sum to the published total is the table whose commitment is `PI[0..7]`.

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

Trace width `49 → 79`, PI count `23 → 22`, constraints `63 → 103`, declared tables `2 → 4`
(`range_w29` id 98 and `range_w24` id 93 join `range_w16` id 85 and `range_w8` id 77), and the
descriptor becomes MULTI-ROW. So:

  * `dregg-solana-lightclient-verify::v1`'s VK **ROTATES** and
    `circuit/descriptors/by-name/dregg-solana-lightclient-verify-v1.json` is **RE-EMITTED**. Both the
    trace width and the PI count move, so a stale 49-column row or a 23-element PI vector **refuses to
    LOAD** — at parse, not at verify.
  * **Every caller must now supply 22 public inputs, and the first eight are a POSEIDON2 root.**
    ⚑⚑ `EpochStakeTable::root` (`STAKE_TABLE_ROOT_TAG = b"dregg-solana-stake-table-root:v1"`,
    `bridge/src/solana_consensus.rs:118`) is a domain-separated SHA-256 and is **NOT** that value. It
    must be RE-ANCHORED to this Poseidon2 frame (tag → `:v2`) and every
    `WeakSubjectivityAnchor.stake_table_root` RE-DERIVED. Until that lands a caller passing the SHA
    root is REFUSED at the last-row pin — loudly, which is the intended behaviour of a shape change
    here. That commitment is dregg-authored; nothing on Solana's side computes it.
  * **A prover must now fill a TABLE, not a row.** The old single-logical-row filler has no
    completion: there are chip absorbs to serve, a seeded root chain to continue and an accumulator to
    carry. `circuit/tests/solana_lightclient_proves.rs` is the reference filler.
  * **`dregg-solana-stake-table-fold::v1` is UNCHANGED** — same 44 columns, 12 PIs, 58 constraints,
    same bytes, no VK rotation. It is now built from `LightClientSolanaAir.foldLegs`, the same term
    this descriptor absorbs, so the two cannot drift.
  * **Three tripwires FIRED and were replaced by positive statements.**
    `sol_anchor_root_remains_arithmetically_inert` is GONE (the anchor is derived now);
    `LightClientAnchorConnectivity`'s `sol_decorative_anchors` went `19 → 10` and its six-chain census
    `71 → 62`. `scripts/descriptor-anchor-inertness-baseline.txt` moves DOWN by nine.

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
import Dregg2.Circuit.Emit.EffectLowerCore
import Dregg2.Circuit.GateExpr
import Dregg2.Bridge.LightClientSolana

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Dregg2.Circuit.Emit.LightClientSolanaAir

open Dregg2.Circuit (Assignment Expr)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId TableDef WindowExpr rangeTableDef emitVmJson2
   rangeRows range_row_mem_iff)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg PiPinLeg LimbsLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Bridge.LightClientSolana

/-! ## §1 — the trace column layout. ⚑ **THIS DESCRIPTOR IS MULTI-ROW SINCE 2026-08-04: ONE ROW PER
STAKE-TABLE ENTRY.**

Columns **0..43** are the STAKE-TABLE FOLD, laid out at exactly the offsets
`dregg-solana-stake-table-fold::v1` uses — the two rungs share ONE source leg list
(`foldLegs`), so they cannot drift apart. Its LAST-row eight-lane output IS this descriptor's
`ANCHOR_ROOT`, and its LAST-row four-limb accumulator IS the quorum's denominator.

Columns **44..46** are the three boolean carrier/gate projections that remain; **47..68** the quorum
block (the rooted-stake numerator and the two comparison chains); **69..78** the two published
values that are still only carried: the nine bank-root limbs and the slot.

⚑ **`STAKE_TABLE_OK` IS GONE, AND ITS DELETION IS THE POINT.** It was a witnessed bit forced `= 1`
standing for *"the derived stake table binds the pinned WS anchor root"* — the sentence the fold now
COMPUTES. `LightClientSolStakeFoldAir.solLcAir_table_carrier_from_the_fold` discharges the bridge's
`stakeTableOk` from the last-row root pin instead. Keeping the bit beside the gate that checks it
would be a no-op retained for familiarity, and the next reader would not know which one was
load-bearing. -/

/-! ### §1a — the FOLD block (columns 0..43). One row per stake-table entry.

`ROOT_IN ‖ VOTER ‖ STAKE ‖ MID ‖ ROOT_OUT ‖ ACC ‖ CARRY`, exactly the layout the standalone fold rung
carries. Every column index below is the SAME number in both descriptors, and both build their legs
from `foldLegs`. -/

/-- Lane `j` of the running eight-felt table root ENTERING this row. Columns 0..7. -/
def ROOT_IN (j : Nat) : Nat := j
/-- Lane `j` of this entry's vote-account pubkey — nine radix-`2^29` lanes (`8·29 + 24 = 256`).
Columns 8..16. -/
def VOTER (j : Nat) : Nat := 8 + j
/-- Limb `i` of this entry's active stake, LSB-first, four 16-bit limbs = a `u64`. Columns 17..20. -/
def STAKE (i : Nat) : Nat := 17 + i
/-- Lane `j` of the INTERMEDIATE state, after the row's first message block. Columns 21..28. -/
def MID (j : Nat) : Nat := 21 + j
/-- ⚑ Lane `j` of the running table root LEAVING this row. Columns 29..36. **Its LAST-row value is
`ANCHOR_ROOT`** — the light client's weak-subjectivity trust anchor, DERIVED from the exhibited rows
rather than carried past every gate. -/
def ROOT_OUT (j : Nat) : Nat := 29 + j
/-- ⚑ Limb `i` of the running TOTAL active stake, LSB-first. Columns 37..40. **Its LAST-row value is
the quorum's DENOMINATOR** and the published `PI_TOTAL_STK`. -/
def ACC (i : Nat) : Nat := 37 + i
/-- Carry `i` of the accumulator's limb addition, boolean-pinned on EVERY row. Columns 41..43. -/
def CARRY (i : Nat) : Nat := 41 + i

/-- The fold block's width: `8 + 9 + 4 + 8 + 8 + 4 + 3`. -/
def FOLD_WIDTH : Nat := 44

/-! ### §1b — the quorum block and the two values still merely carried. -/

/-- **CARRIER** — the aggregate ed25519 verify RESULT (counted authorized voters signed the bank hash at
the slot); forced `= 1`. NAMED verified-FFI carrier. Witness. -/
def ED_OK : Nat := 44
/-- **GATE** — the ROOTED flag (every counted vote's tower root reaches the slot — HOLE-1); forced `= 1`. -/
def ROOTED_OK : Nat := 45
/-- **GATE** — the AUTHORIZED-voter binding (every counted signer is the on-chain authorized voter —
BR-2-A); forced `= 1`. -/
def AUTH_OK : Nat := 46

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

/-- ⚑⚑ **Limb `i` of the total ACTIVE stake** (`total_stake()`, the 2/3 denominator), LSB-first —
**and it IS the fold's accumulator column** (`ACC i`, cols 37..40), not a separate witness.

⚑ 2026-08-04, the second pass: this used to be four columns of its own (4..7) PI-bound to the light
client's anchor. That stopped the prover CHOOSING the denominator; it did not make the denominator
DERIVED. Pointing the name at `ACC` is the difference: the number the quorum divides by is now the
running total the fold's own limb-addition chain accumulates over the exhibited rows, so a prover that
wants a smaller universe has to exhibit a smaller TABLE — and the table's commitment is published in
the same statement. There is no second copy to leave unforced. -/
def TOTAL_STK_LIMB (i : Nat) : Nat := ACC i
/-- **Limb `i` of the counted rooted authorized voting stake** (`voted_stake`), LSB-first.
Columns 47..50. Its ed25519 provenance is the `ED_OK` carrier. ⚠ Still a WITNESSED PROJECTION: the
prover chooses which of the bound validators it claims voted. -/
def ROOTED_STK_LIMB (i : Nat) : Nat := 47 + i

/-- **Limb `i` of the QUORUM difference `3·rooted − 2·total`**, LSB-first. FIVE limbs (columns
51..55), one more than the operands: `3·A` needs two bits beyond `A`. Every limb carries its own
16-bit range lookup, and THAT is the quorum tooth — a limb vector of non-negative limbs denotes a
non-negative value, so a sub-quorum (whose difference is negative) has no representation at all. -/
def QDIFF_LIMB (i : Nat) : Nat := 51 + i
/-- **Offset carry `i` of the quorum chain** (columns 56..59); denotes `col − 128`, since a difference
chain BORROWS and a field wire has no sign. Range-checked at 8 bits for the mod-`p` bridge ONLY —
`LimbTally.chain_recomposes` needs no bound on it whatsoever. -/
def QDIFF_CARRY (i : Nat) : Nat := 56 + i

/-- **Limb `i` of the EMPTY-STAKE-TABLE floor difference `total − 1`**, LSB-first. FIVE limbs
(columns 60..64) — the generator emits `k + 1` difference limbs for `k` rungs regardless of `α`, and
at `α = 1` the top limb is simply always zero on an honest fill. -/
def TPOS_LIMB (i : Nat) : Nat := 60 + i
/-- **Offset carry `i` of the floor chain** (columns 65..68). -/
def TPOS_CARRY (i : Nat) : Nat := 65 + i

/-- The number of ~31-bit limbs a FULL 256-bit root is exposed as: `⌈256 / 31⌉ = 9`. Eight 31-bit
limbs cover 248 bits; the ninth (most-significant) limb carries the remaining 8 bits. ⚑ It survives
only for the BANK root now; the WS anchor root is EIGHT fold lanes (§1c). -/
def ROOT_LIMBS : Nat := 9

/-- ⚑⚑ **PUBLIC ANCHOR (lane `j`) — the pinned WS stake-table root, AND IT IS THE FOLD'S OUTPUT.**

`ANCHOR_ROOT j` is `ROOT_OUT j`: the light client's weak-subjectivity trust anchor is the LAST row's
eight-lane Poseidon2 commitment to the stake table this very proof exhibited. The PI pin is on
`VmRow.last`, so what the light client compares against its governance-pinned anchor is the IMAGE of
the rows, not a value the prover wrote into nine columns nothing reads.

⚑ **The three shapes this column has had, in order, because only the sequence makes the last one
legible:**

  * **ONE column** (until 2026-08-04 morning): a 256-bit SHA-256 root reduced to a single BabyBear
    element. *The light client was comparing 31 bits of its own trust anchor* — a colliding pair
    findable in `2^31`.
  * **NINE radix-`2^31` `.first` limbs** (2026-08-04 midday): the full 256 bits COMPARED, and read by
    no constraint of any kind (`LightClientAnchorConnectivity.sol_anchors_are_unread`). A root that
    binds nothing at any width, because nothing derives it.
  * **EIGHT `.last`-pinned fold lanes** (this commit): `8 · log₂ p = 247.255128` bits of image, so
    the relevant figure — a fold over a table, where an equivocating prover needs two tables with one
    root — is the **BIRTHDAY COLLISION** bound `2^123.63`. ⚠ The second-preimage figure for the same
    object is `~2^247.3` and is NOT the number that governs here; quoting it would be the flattering
    half of a pair. -/
def ANCHOR_ROOT (j : Nat) : Nat := ROOT_OUT j

/-- The number of lanes the WS anchor root is bound at: EIGHT, the chip's squeeze width. -/
def ANCHOR_LANES : Nat := 8

/-- The number of limbs the rooted bank hash is exposed as (`= ROOT_LIMBS`; kept as its own name
because the two roots are independent shapes — and since this commit they no longer even share a
width, which is the point of keeping the names apart). -/
def BANK_ROOT_LIMBS : Nat := ROOT_LIMBS

/-- **PUBLIC ANCHOR (limb `i`)** — the claimed rooted bank/state root B as its radix-`2^31`,
MOST-SIGNIFICANT-limb-first decomposition. Limb `i` is trace column `69 + i` (cols 69..77); limb `0` is
the MSB (its top carries only 8 bits). PI-bound to slot `8 + i`, so the peer-wrap's radix-`2^31`
MSB-first pack over `PI[8..16]` recomposes the 256-bit bank hash exactly before its 128-bit split.

⚠ **STILL DECORATIVE**, and deliberately kept as a tripwire: no gate reads it
(`sol_bank_root_and_slot_remain_arithmetically_inert`). `ED_OK` derived from the vote message built on
`BANK_ROOT` + `SLOT` is the Ed25519/EC arc, and that is what closes it. -/
def BANK_ROOT (i : Nat) : Nat := 69 + i

/-- **PUBLIC ANCHOR** — the rooted slot S (epoch/slot). PI-bound, and read by no gate. -/
def SLOT_COL : Nat := 78

/-- Total main-trace width: 44 fold columns + 3 carrier/gate columns + 4 rooted-stake limbs +
5 quorum-difference limbs + 4 quorum carries + 5 floor-difference limbs + 4 floor carries +
9 bank-root limbs + 1 slot anchor = **79**.

⚑ It was 19, then 41, then 49. **The +44 − 9 − 4 − 1 = +30 of this pass** is the fold absorbed
(`+44`), the nine `.first` anchor-root limbs DELETED (`−9`, replaced by the fold's eight `.last`
outputs, which are already inside the 44), the four separate total-stake columns DELETED (`−4`,
replaced by the fold's accumulator) and `STAKE_TABLE_OK` DELETED (`−1`, replaced by the pin). -/
def SOL_LC_WIDTH : Nat := 79

/-- PI slot of anchor-root LANE `j` (slots 0..7) — pinned on the LAST row from `ROOT_OUT j`. -/
def PI_ANCHOR_ROOT (j : Nat) : Nat := j
/-- PI slot of bank-root limb `i` (slots 8..16), MSB-first. -/
def PI_BANK_ROOT (i : Nat) : Nat := ANCHOR_LANES + i
/-- PI slot of the rooted slot (slot 17). -/
def PI_SLOT : Nat := ANCHOR_LANES + BANK_ROOT_LIMBS

/-- ⚑ **PI slot of TOTAL-STAKE limb `i` (slots 18..21)** — the active-stake DENOMINATOR, pinned on the
LAST row from the fold's accumulator. The light client supplies the number from its
weak-subjectivity anchor and the fold has to REACH it by adding up the rows it published a commitment
to. -/
def PI_TOTAL_STK (i : Nat) : Nat := ANCHOR_LANES + BANK_ROOT_LIMBS + 1 + i

/-- Number of public inputs: 8 anchor-root lanes + 9 bank-root limbs + slot + 4 total-stake limbs. -/
def PI_COUNT : Nat := 22

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
/-- `ROOTED_OK − 1` — zero iff the rooted-flag gate bit is set. -/
def rootedBody : EmittedExpr := .add (.var ROOTED_OK) (.const (-1))
/-- `AUTH_OK − 1` — zero iff the authorized-voter-binding gate bit is set. -/
def authBody : EmittedExpr := .add (.var AUTH_OK) (.const (-1))

/-! ## §3 — ⚑ THE SOURCE AIR, and the descriptor as the COMPILER'S OUTPUT.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): since 2026-08-04 this descriptor is **`lowerAir` of an
`EffectAir` source** — the same entry point `dregg-solana-stake-table-fold::v1` and
`dregg-mina-lightclient-link::v1` go through. There is **no hand-written `VmConstraint2` below.**
`solLcVerifyAir_mainRailOk = true` by `rfl` records that every leg was expressible on the deployed
main rail; a leg the rail cannot hold lowers to an UNSATISFIABLE pair rather than to silence.

### The four declared range tables.

The fold's three (`range_w29` id 98 for pubkey lanes, `range_w24` id 93 for the top lane,
`range_w16` id 85 for stake limbs) plus the quorum's carry table (`range_w8` id 77). ⚑ `range_w16` is
SHARED: the fold's accumulator limbs and the quorum's difference limbs query one table, which is what
it means for them to be the same kind of number. The shared 29-bit felt-wide `range` table (wire id 2)
is still NOT declared — both former felt slacks are limbed chains
(`sol_range_table_is_not_declared`). -/

/-- The tally-limb range table: wire id `5 + 64 + 16 = 85`. Shared with the fold's stake and
accumulator limbs. -/
def TID_TALLY_LIMB : TableId := .custom (64 + SOL_LIMB_BITS)
/-- The chain-carry range table: wire id `5 + 64 + 8 = 77`. -/
def TID_TALLY_CARRY : TableId := .custom (64 + SOL_CARRY_BITS)

/-! ### §3a — the FOLD legs. ⚑ ONE source list, TWO descriptors.

`foldLegs` is the leg list `dregg-solana-stake-table-fold::v1` is built from
(`LightClientSolStakeFoldAir.solStakeFoldAir = ⟨foldTables, foldLegs ++ rootPins ++ totalPins⟩`) and
the list this descriptor absorbs. They are the SAME TERM, so the standalone rung and the light
client's in-proof fold cannot disagree about what a stake-table row is — the failure mode
`CLAUDE.md` names as *"two shapes that agree today are two shapes that will disagree later"*, removed
by construction rather than by a differential test.

⚑ Every inter-row law is a `WindowLeg` at `.transition` — the ONE `RowSel` where `nxt` is the genuine
successor. The seeds are `.first`, the boolean pins are `.all`. -/

open Dregg2.Circuit.DescriptorIR2.WindowExpr (loc nxt)

/-- Pubkey lane width. **29 is the last wrap-free width at BabyBear**
(`RangeFieldContainment.wrap_free_iff_le_29`). -/
def LANE_BITS : Nat := 29
/-- The TOP pubkey lane's width: `8·29 + 24 = 256`, exactly a 32-byte pubkey and no more. -/
def TOP_LANE_BITS : Nat := 24

/-- Width-tagged range table id. -/
def rangeTid (bits : Nat) : TableId := .custom (64 + bits)

def laneTable : TableDef := ⟨rangeTid LANE_BITS, "range_w29", 1, .rangeLimb LANE_BITS⟩
def topLaneTable : TableDef := ⟨rangeTid TOP_LANE_BITS, "range_w24", 1, .rangeLimb TOP_LANE_BITS⟩
def stakeTable : TableDef := ⟨TID_TALLY_LIMB, "range_w16", 1, .rangeLimb SOL_LIMB_BITS⟩
def carryTable : TableDef := ⟨TID_TALLY_CARRY, "range_w8", 1, .rangeLimb SOL_CARRY_BITS⟩

/-- The fold's own three tables, in the order the standalone rung declares them. -/
def foldTables : List TableDef := [laneTable, topLaneTable, stakeTable]

/-- The FOLD's domain tag, lane 0 of the initial state — ASCII `SSTF` ("solana stake table fold"). -/
def FOLD_TAG : ℤ := 0x53535446

/-- `2^16`, the accumulator's limb radix. -/
def RADIX : ℤ := 65536

/-- The eight lanes of the running root entering a row. -/
def rootInCols : List Nat := [ROOT_IN 0, ROOT_IN 1, ROOT_IN 2, ROOT_IN 3,
                              ROOT_IN 4, ROOT_IN 5, ROOT_IN 6, ROOT_IN 7]
/-- The eight lanes of the intermediate state. -/
def midCols : List Nat := [MID 0, MID 1, MID 2, MID 3, MID 4, MID 5, MID 6, MID 7]
/-- The eight lanes of the running root leaving a row. -/
def rootOutCols : List Nat := [ROOT_OUT 0, ROOT_OUT 1, ROOT_OUT 2, ROOT_OUT 3,
                               ROOT_OUT 4, ROOT_OUT 5, ROOT_OUT 6, ROOT_OUT 7]
/-- The eight LOW pubkey lanes — the row's FIRST message block. -/
def voterLowCols : List Nat := [VOTER 0, VOTER 1, VOTER 2, VOTER 3,
                                VOTER 4, VOTER 5, VOTER 6, VOTER 7]

/-- The arity-16 chip absorb tuple `[16, in₀ … in₁₅, out₀ … out₇]`, in SOURCE `Expr`.
⚑ **16 is an ADMITTED absorb arity** (`CHIP_ADMITTED_ARITIES = [0,2,3,4,7,11,16]`), and it is the
`node8` full-width seed — the one arity at which all sixteen input lanes genuinely enter the
preimage. A descriptor at a NON-admitted arity is UNPROVABLE rather than merely inefficient.

⚑ **THE ARITY CHECK IS BACK (2026-08-06), AND WHY IT WAS EVER MISSING.** This file works in
`Circuit.Expr` while the three checked chip-tuple constructors (`chipLookupTupleN`,
`chipLookupTuple`, `chipLookupTupleNarrow`) are `EmittedExpr`, so it could not consume any of them
and a fourth constructor was written here instead. The re-typing dropped two things:

* the `hAdm : ChipArityAdmitted ins.length` `autoParam` — a site at arity 8, 9 or 14 **failed to
  elaborate** on the three checked rails and elaborated fine here;
* the tie between the arity TAG and the input list — the tag was the literal `16` regardless of
  `ins.length`, so a fifteen-lane block would have ridden out claiming sixteen.

Both call sites happen to pass exactly sixteen today, which is why this was an unenforced invariant
rather than a live defect. It is now `GateExpr.gChipTuple` at the `toSource` view — the SAME
constructor `chipLookupTupleN` is (`GateExpr.gChipTuple_emitted`, `rfl`), so the check is inherited
rather than re-implemented, and `chipTuple16_absorbA_unmoved` / `_absorbB_unmoved` pin that no
emitted byte moved. -/
def chipTuple16 (ins : List Expr) (outs : List Nat)
    (hAdm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted ins.length :=
      by chip_arity_admitted) : List Expr :=
  Dregg2.Circuit.GateExpr.gChipTuple Dregg2.Circuit.GateExpr.toSource ins outs hAdm

/-- **The row's FIRST message block** — `chipAbsorb16(ROOT_IN8 ‖ voter₀…voter₇) = MID8`. -/
def absorbA : AirLeg :=
  .lookup { table := TableId.poseidon2
          , tuple := chipTuple16 ((rootInCols ++ voterLowCols).map Expr.var) midCols }

/-- **The row's SECOND message block** — `chipAbsorb16(MID8 ‖ [voter₈, stake₀…stake₃, 0,0,0]) =
ROOT_OUT8`. The three trailing zeros are `Expr.const 0`, i.e. STRUCTURE in the tuple and not
witnessed columns, so the per-entry frame is a fixed sixteen felts. -/
def absorbB : AirLeg :=
  .lookup { table := TableId.poseidon2
          , tuple := chipTuple16
              (midCols.map Expr.var
                ++ [Expr.var (VOTER 8), Expr.var (STAKE 0), Expr.var (STAKE 1),
                    Expr.var (STAKE 2), Expr.var (STAKE 3),
                    Expr.const 0, Expr.const 0, Expr.const 0])
              rootOutCols }

/-! ⚑ **ZERO BYTES MOVED BY THE ARITY REPAIR.** Both deployed tuples, pinned against the literal
shape the unchecked constructor emitted. `rfl`, on the emitted object. -/

theorem chipTuple16_absorbA_unmoved :
    chipTuple16 ((rootInCols ++ voterLowCols).map Expr.var) midCols
      = Expr.const 16 :: (((rootInCols ++ voterLowCols).map Expr.var) ++ midCols.map Expr.var) :=
  rfl

theorem chipTuple16_absorbB_unmoved :
    chipTuple16
        (midCols.map Expr.var
          ++ [Expr.var (VOTER 8), Expr.var (STAKE 0), Expr.var (STAKE 1),
              Expr.var (STAKE 2), Expr.var (STAKE 3),
              Expr.const 0, Expr.const 0, Expr.const 0])
        rootOutCols
      = Expr.const 16 :: ((midCols.map Expr.var
          ++ [Expr.var (VOTER 8), Expr.var (STAKE 0), Expr.var (STAKE 1),
              Expr.var (STAKE 2), Expr.var (STAKE 3),
              Expr.const 0, Expr.const 0, Expr.const 0]) ++ rootOutCols.map Expr.var) :=
  rfl

/-- ⚑ **AND THE CHECK CAN GO RED.** The arity the repair exists to refuse is not admitted — so a
nine-lane absorb block behind this constructor fails to elaborate rather than emitting a tuple whose
tag lies about its own contents. -/
theorem chipTuple16_refuses_nine :
    ¬ Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted 9 := by decide

/-- **The seed** — lane 0 of the first row's running root is the domain tag. -/
def firstRootTag : AirLeg :=
  .window ⟨RowSel.first, .add (loc (ROOT_IN 0)) (.const (-FOLD_TAG))⟩

/-- **The seed, lanes 1..7** — pinned to zero, so the initial state is fully named by the
descriptor. -/
def firstRootZero (j : Nat) : AirLeg := .window ⟨RowSel.first, loc (ROOT_IN j)⟩

/-- **State continuity** — `ROOT_OUT[i] = ROOT_IN[i+1]`, one leg per lane. -/
def rootContinuity (j : Nat) : AirLeg :=
  .window ⟨RowSel.transition,
    .add (loc (ROOT_OUT j)) (.mul (.const (-1)) (nxt (ROOT_IN j)))⟩

/-- **`CARRY i` is boolean on EVERY row.** ⚑ `.all`, not `.transition`: a transition-scoped boolean
pin is vacuous on the last row, which is exactly where an unbooleanised carry would hide the
published total. -/
def carryBoolean (i : Nat) : AirLeg :=
  .window ⟨RowSel.all, .mul (loc (CARRY i)) (.add (loc (CARRY i)) (.const (-1)))⟩

/-- **Seed the tally** — on the first row `ACC = 0 + STAKE`, carrying. -/
def firstAcc (i : Nat) : AirLeg :=
  .window ⟨RowSel.first,
    if i = 0 then
      .add (loc (ACC 0)) (.add (.mul (.const RADIX) (loc (CARRY 0)))
        (.mul (.const (-1)) (loc (STAKE 0))))
    else if i = 3 then
      .add (loc (ACC 3)) (.add (.mul (.const (-1)) (loc (STAKE 3)))
        (.mul (.const (-1)) (loc (CARRY 2))))
    else
      .add (loc (ACC i)) (.add (.mul (.const RADIX) (loc (CARRY i)))
        (.add (.mul (.const (-1)) (loc (STAKE i))) (.mul (.const (-1)) (loc (CARRY (i - 1))))))⟩

/-- **Accumulate** — `ACC'[i] + 2^16·C'[i] = ACC[i] + STAKE'[i] + C'[i−1]` across a transition, with
the top limb carrying out nowhere. -/
def accStep (i : Nat) : AirLeg :=
  .window ⟨RowSel.transition,
    if i = 0 then
      .add (nxt (ACC 0)) (.add (.mul (.const RADIX) (nxt (CARRY 0)))
        (.add (.mul (.const (-1)) (loc (ACC 0))) (.mul (.const (-1)) (nxt (STAKE 0)))))
    else if i = 3 then
      .add (nxt (ACC 3)) (.add (.mul (.const (-1)) (loc (ACC 3)))
        (.add (.mul (.const (-1)) (nxt (STAKE 3))) (.mul (.const (-1)) (nxt (CARRY 2)))))
    else
      .add (nxt (ACC i)) (.add (.mul (.const RADIX) (nxt (CARRY i)))
        (.add (.mul (.const (-1)) (loc (ACC i)))
          (.add (.mul (.const (-1)) (nxt (STAKE i))) (.mul (.const (-1)) (nxt (CARRY (i - 1)))))))⟩

/-- The eight LOW pubkey lanes as ONE `.limbs` leg at 29 bits. -/
def voterLowLeg : AirLeg :=
  .limbs { cols := voterLowCols, bits := LANE_BITS, table := rangeTid LANE_BITS }

/-- The TOP pubkey lane, on the narrower 24-bit table — the leg that separates "well-formed 32-byte
pubkey" from "any nine felts". -/
def voterTopLeg : AirLeg :=
  .lookup { table := rangeTid TOP_LANE_BITS, tuple := [Expr.var (VOTER 8)] }

/-- The four per-row stake limbs at 16 bits. -/
def stakeLeg : AirLeg :=
  .limbs { cols := [STAKE 0, STAKE 1, STAKE 2, STAKE 3], bits := SOL_LIMB_BITS
         , table := TID_TALLY_LIMB }

/-- ⚑ The four accumulator limbs at 16 bits — the leg that makes the running total a `u64`, forbids
the top limb carrying out, AND supplies the quorum chain's denominator range bound. It is the same
leg for both jobs because it is the same four columns. -/
def accLeg : AirLeg :=
  .limbs { cols := [ACC 0, ACC 1, ACC 2, ACC 3], bits := SOL_LIMB_BITS
         , table := TID_TALLY_LIMB }

/-- ⚑ **THE FOLD'S SOURCE LEGS — the shared list.** Four range legs, two chip absorbs, eight `.first`
seeds, eight `.transition` continuities, three `.all` carry pins, four `.first` tally seeds and four
`.transition` tally steps: **33 legs, 46 emitted constraints**, at ANY number of validators, because
the validators are ROWS and not columns. -/
def foldLegs : List AirLeg :=
  [ voterLowLeg, voterTopLeg, stakeLeg, accLeg
  , absorbA, absorbB
  , firstRootTag
  , firstRootZero (ROOT_IN 1), firstRootZero (ROOT_IN 2), firstRootZero (ROOT_IN 3)
  , firstRootZero (ROOT_IN 4), firstRootZero (ROOT_IN 5), firstRootZero (ROOT_IN 6)
  , firstRootZero (ROOT_IN 7)
  , rootContinuity 0, rootContinuity 1, rootContinuity 2, rootContinuity 3
  , rootContinuity 4, rootContinuity 5, rootContinuity 6, rootContinuity 7
  , carryBoolean 0, carryBoolean 1, carryBoolean 2
  , firstAcc 0, firstAcc 1, firstAcc 2, firstAcc 3
  , accStep 0, accStep 1, accStep 2, accStep 3 ]

/-! ### §3b — the QUORUM legs, and the ONE thing that had to change about them.

Every quorum gate is now scoped `.last` instead of holding on every row. That is not a weakening
dressed as a re-scope, it is the only scope the statement HAS once the trace is a table: the
denominator is the accumulator's FINAL value, so "this rooted stake clears two thirds of the active
stake" is a fact about the last row and about no other row. A `.all`-scoped quorum over a fold would
assert the threshold against every PREFIX total — an assertion the honest prover cannot satisfy and
the descriptor never meant.

The per-limb range lookups stay unscoped (they lower to `.lookup`, which every row carries), so a
prover cannot park an out-of-range residue on a non-final row. -/

/-- A row-local `EmittedExpr` as a `WindowExpr`. `LimbTally.chainBodies` speaks the target's gate AST;
a `.last`-scoped leg speaks the two-row one. This is the injection, and `locExpr_roundtrips` proves
`lowerWindowLeg` recovers the ORIGINAL body — so the `.last` re-scope is byte-identical algebra and
not a new polynomial. -/
def locExpr : EmittedExpr → WindowExpr
  | .var c   => .loc c
  | .const k => .const k
  | .add a b => .add (locExpr a) (locExpr b)
  | .mul a b => .mul (locExpr a) (locExpr b)

/-- ⚑ **THE RE-SCOPE CHANGED NO ALGEBRA.** `lowerWindowLeg` at `.last` lowers through
`windowToLocal?`, and that function inverts `locExpr` exactly — so every `.last` boundary body this
descriptor emits IS the `EmittedExpr` `LimbTally.chainBodies` generated, node for node. The gates
`airAccepts` reads and the gates the wire carries are one object. -/
theorem locExpr_roundtrips (e : EmittedExpr) :
    Dregg2.Circuit.Emit.EffectLower.windowToLocal? (locExpr e) = some e := by
  induction e with
  | var c => rfl
  | const k => rfl
  | add a b iha ihb =>
      simp only [locExpr, Dregg2.Circuit.Emit.EffectLower.windowToLocal?, iha, ihb]
  | mul a b iha ihb =>
      simp only [locExpr, Dregg2.Circuit.Emit.EffectLower.windowToLocal?, iha, ihb]

/-- One `.last`-scoped gate leg from an emitted body. -/
def lastGate (b : EmittedExpr) : AirLeg := .window ⟨RowSel.last, locExpr b⟩

/-- ⚑ **THE TEETH: one range lookup PER LIMB, on BOTH chains.** Fourteen 16-bit limb legs beyond the
fold's own (four rooted-stake limbs, five quorum-difference limbs, five floor-difference limbs) and
eight 8-bit carries. The load-bearing ones are the TEN on the two differences: they force
`3·rooted − 2·total ≥ 0` and `total − 1 ≥ 0`, because a limb vector of non-negative limbs denotes a
non-negative value (`LimbTally.limbValue_nonneg`).

⚠ The DENOMINATOR's four 16-bit lookups are not here — they are `accLeg`, in the fold block. That is
the change, stated where it is easy to miss: the quorum's `β` operand has no lookup of its own because
it has no columns of its own. -/
def quorumRangeLegs : List AirLeg :=
  [ .limbs { cols := [ROOTED_STK_LIMB 0, ROOTED_STK_LIMB 1, ROOTED_STK_LIMB 2, ROOTED_STK_LIMB 3]
           , bits := SOL_LIMB_BITS, table := TID_TALLY_LIMB }
  , .limbs { cols := [QDIFF_LIMB 0, QDIFF_LIMB 1, QDIFF_LIMB 2, QDIFF_LIMB 3, QDIFF_LIMB 4]
           , bits := SOL_LIMB_BITS, table := TID_TALLY_LIMB }
  , .limbs { cols := [TPOS_LIMB 0, TPOS_LIMB 1, TPOS_LIMB 2, TPOS_LIMB 3, TPOS_LIMB 4]
           , bits := SOL_LIMB_BITS, table := TID_TALLY_LIMB }
  , .limbs { cols := [QDIFF_CARRY 0, QDIFF_CARRY 1, QDIFF_CARRY 2, QDIFF_CARRY 3]
           , bits := SOL_CARRY_BITS, table := TID_TALLY_CARRY }
  , .limbs { cols := [TPOS_CARRY 0, TPOS_CARRY 1, TPOS_CARRY 2, TPOS_CARRY 3]
           , bits := SOL_CARRY_BITS, table := TID_TALLY_CARRY } ]

/-- The generated QUORUM legs, `.last`-scoped. GENERATED — there is no hand-written body here. -/
def qdiffChainLegs : List AirLeg := qdiffChainBodies.map lastGate

/-- The generated EMPTY-STAKE-TABLE FLOOR legs, from the same `LimbTally.chainBodies` call at
`α = 1, β = 0, γ = 1`. -/
def tposChainLegs : List AirLeg := tposChainBodies.map lastGate

/-- The three carrier/gate bits, forced `= 1` on EVERY row (`.all`, not `.last`) — the same discipline
`carryBoolean` follows and for the same reason: a boundary-scoped bit pin is silent on every row but
one, and there is no reason to give a padded trace somewhere to hide one. They are one-column islands
and `sol_carriers_are_one_column_islands` says so. -/
def allGate (b : EmittedExpr) : AirLeg := .window ⟨RowSel.all, locExpr b⟩

def carrierLegs : List AirLeg := [allGate edBody, allGate rootedBody, allGate authBody]

/-! ### §3c — the PIN block. Which row a pin sits on is the whole content of this pass. -/

/-- ⚑⚑ **THE ANCHOR PINS — the eight `.last` fold lanes, and this is the commit's deliverable.**

`PI[0..7]` are `ROOT_OUT[0..7]` on the LAST ROW: the light client's weak-subjectivity stake-table
anchor is the fold's OUTPUT. A prover that wants a different validator set has to move the root
(`LightClientSolStakeFoldAir.FoldScheme.same_tally_moves_the_root`), and the root is the number the
light client already compares against governance.

⚑ **What each of the three shapes was worth, side by side, because only the pair is honest:** one
column = `2^31` (a colliding anchor findable in minutes of GPU); nine `.first` limbs = the full 256
bits COMPARED and read by nothing, so the number that governs is not a hash bound at all but "the
prover chose nine felts"; eight `.last` fold lanes = **`2^123.63`**, the birthday-collision bound on
`8 · 30.906891 = 247.255128` bits of image. ⚠ NOT the `~2^247.3` second-preimage figure for the same
object; that is the flattering half of the pair. -/
def anchorRootPins : List AirLeg :=
  [ .pin ⟨VmRow.last, ANCHOR_ROOT 0, PI_ANCHOR_ROOT 0⟩
  , .pin ⟨VmRow.last, ANCHOR_ROOT 1, PI_ANCHOR_ROOT 1⟩
  , .pin ⟨VmRow.last, ANCHOR_ROOT 2, PI_ANCHOR_ROOT 2⟩
  , .pin ⟨VmRow.last, ANCHOR_ROOT 3, PI_ANCHOR_ROOT 3⟩
  , .pin ⟨VmRow.last, ANCHOR_ROOT 4, PI_ANCHOR_ROOT 4⟩
  , .pin ⟨VmRow.last, ANCHOR_ROOT 5, PI_ANCHOR_ROOT 5⟩
  , .pin ⟨VmRow.last, ANCHOR_ROOT 6, PI_ANCHOR_ROOT 6⟩
  , .pin ⟨VmRow.last, ANCHOR_ROOT 7, PI_ANCHOR_ROOT 7⟩ ]

/-- Published-anchor pins: the NINE rooted-bank-root limbs are `PI[8..16]` (MSB-first), on the FIRST
row. Each limb rides its own PI slot, so the peer-wrap's radix-`2^31` pack recovers the FULL 256-bit
bank hash — not a 31-bit projection. ⚠ Still read by no gate; see
`sol_bank_root_and_slot_remain_arithmetically_inert`. -/
def bankRootPins : List AirLeg :=
  [ .pin ⟨VmRow.first, BANK_ROOT 0, PI_BANK_ROOT 0⟩
  , .pin ⟨VmRow.first, BANK_ROOT 1, PI_BANK_ROOT 1⟩
  , .pin ⟨VmRow.first, BANK_ROOT 2, PI_BANK_ROOT 2⟩
  , .pin ⟨VmRow.first, BANK_ROOT 3, PI_BANK_ROOT 3⟩
  , .pin ⟨VmRow.first, BANK_ROOT 4, PI_BANK_ROOT 4⟩
  , .pin ⟨VmRow.first, BANK_ROOT 5, PI_BANK_ROOT 5⟩
  , .pin ⟨VmRow.first, BANK_ROOT 6, PI_BANK_ROOT 6⟩
  , .pin ⟨VmRow.first, BANK_ROOT 7, PI_BANK_ROOT 7⟩
  , .pin ⟨VmRow.first, BANK_ROOT 8, PI_BANK_ROOT 8⟩ ]

/-- Published-anchor pin: the rooted slot is `PI[17]`. -/
def slotPin : AirLeg := .pin ⟨VmRow.first, SLOT_COL, PI_SLOT⟩

/-- ⚑⚑ **THE DENOMINATOR PINS — now `.last` on the FOLD'S ACCUMULATOR.**

The four limbs the quorum chain divides by are PI-bound to slots `18..21` from `ACC` on the last row.
The prover neither chooses the denominator (it is in the public statement) NOR asserts it (the fold's
limb-addition chain has to reach it by adding up the exhibited rows, whose commitment is published in
the same statement).

⚑ **What changed from the pins this replaces, said as the forgery each admits.** The `.first` pins on
four dedicated columns refused every swap that MOVED the total and admitted every swap that preserved
it — `circuit/tests/solana_lightclient_proves.rs::a_swapped_stake_table_is_arithmetically_perfect`
exhibited a forged validator set satisfying every gate. These pins refuse that one too, because the
table whose rows sum to the published total is the table whose commitment is `PI[0..7]`. -/
def totalStakePins : List AirLeg :=
  [ .pin ⟨VmRow.last, TOTAL_STK_LIMB 0, PI_TOTAL_STK 0⟩
  , .pin ⟨VmRow.last, TOTAL_STK_LIMB 1, PI_TOTAL_STK 1⟩
  , .pin ⟨VmRow.last, TOTAL_STK_LIMB 2, PI_TOTAL_STK 2⟩
  , .pin ⟨VmRow.last, TOTAL_STK_LIMB 3, PI_TOTAL_STK 3⟩ ]

/-- ⚑ **THE SOURCE.** The fold's 33 legs, the quorum's five range legs, its ten generated chain legs,
three carrier pins and 22 PI pins — **73 legs, 103 emitted constraints.** -/
def solLcVerifyAir : EffectAir :=
  { tables := foldTables ++ [carryTable]
  , legs   := foldLegs ++ quorumRangeLegs ++ qdiffChainLegs ++ tposChainLegs ++ carrierLegs
              ++ anchorRootPins ++ bankRootPins ++ [slotPin] ++ totalStakePins }

/-- ⚑ **THE COMPILER ACCEPTED EVERY LEG.** `mainRailOk` is the decidable verdict that each leg is
EXPRESSIBLE on the deployed main rail — unit multiplicity, `.query` side, no `nxt` under `.all` /
`.first` / `.last`, no limb width at or above the wrap-free ceiling 29. -/
theorem solLcVerifyAir_mainRailOk : solLcVerifyAir.mainRailOk = true := by rfl

/-- …and every PI pin indexes a slot the descriptor declares. A pin past `piCount` is a wire-format
defect the Rust decoder would read as an out-of-range public input. -/
theorem solLcVerifyAir_pinsFit : solLcVerifyAir.pinsFit PI_COUNT = true := by rfl

/-- **`solLcVerifyDesc`** — the Solana rooted-finality verify-decision as an emitted IR-v2 AIR, ONE
ROW PER STAKE-TABLE ENTRY. PIs `[table_root[0..7], bank_root[0..8], slot, total_stk[0..3]]` (22
total): the eight-lane Poseidon2 commitment to the stake table the proof exhibited, the full 256-bit
bank hash as nine radix-`2^31` MSB-first limbs, the rooted slot, and the `u64` active-stake
denominator — **the first and the last DERIVED from the same rows.** -/
def solLcVerifyDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-solana-lightclient-verify::v1" SOL_LC_WIDTH PI_COUNT [] solLcVerifyAir

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

/-- …and the tables the descriptor DECLARES are the four the teeth query, by `rfl` on the emitted
object: the fold's 29-bit pubkey-lane table, its 24-bit top-lane table, the SHARED 16-bit limb table
(stake limbs, accumulator limbs, rooted-stake limbs, both difference vectors) and the 8-bit chain-carry
table. -/
theorem sol_declared_tables :
    solLcVerifyDesc.tables = [laneTable, topLaneTable, stakeTable, carryTable] := rfl

/-- ⚑ **THE FOLD BLOCK IS ONE SOURCE LIST, NOT A COPY.** `solLcVerifyAir`'s legs BEGIN with exactly
`foldLegs` — the same term `LightClientSolStakeFoldAir.solStakeFoldAir` is built from. A drift in the
standalone rung's fold is a drift in this descriptor's fold, by construction, so the two cannot state
different things about what a stake-table row is. -/
theorem sol_fold_block_is_the_shared_source :
    solLcVerifyAir.legs.take foldLegs.length = foldLegs ∧ foldLegs.length = 33 := by
  refine ⟨?_, by decide⟩
  simp [solLcVerifyAir, List.take_left']

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
see `LimbTally.cmp_sound`.

⚑ **AND IT IS ABOUT THE LAST ROW.** Every gate it names is `.last`-scoped in the emitted object
(§3b), because the quantity they are about — the fold's final accumulator — exists on that row and
nowhere else. `airAccepts a` where `a` is the trace's last row is exactly "the emitted verify logic
accepts this trace".

⚑ **`stakeBody` IS GONE FROM THIS CONJUNCTION.** The stake-table carrier is no longer a bit the
prover sets; it is `anchorRootPins` — the eight last-row root lanes pinned to the light client's
public statement. `LightClientSolStakeFoldAir.solLcAir_table_carrier_from_the_fold` is what discharges
`stakeTableOk` now, and it reads the PIN and the fold, not a witness. -/
def airAccepts (a : Assignment) : Prop :=
  LimbTally.BodiesVanish a qdiffChainBodies
  ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols qdiffRungs QDIFF_TOP)
  ∧ LimbTally.BodiesVanish a tposChainBodies
  ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP)
  ∧ edBody.eval a = 0
  ∧ rootedBody.eval a = 0
  ∧ authBody.eval a = 0

/-- **THE REFINEMENT (soundness): a satisfying AIR witness ENTAILS `solVerifyDecision` accept.** Fed a
row `a` whose columns read the update's true projections (the honest-witness relation — the two stakes
as 16-bit LIMB VECTORS, the carrier/gate bits as `if · then 1 else 0`), if the emitted verify-logic
gates accept, then the exported scalar decision `solVerifyDecision` accepts.

⚑ The quorum chain discharges the `≥ 2/3` threshold and the floor chain discharges `total > 0`, and
NEITHER hypothesis bounds a tally: `LimbTally.emitted_chain_sound` reads the five generated gates and
the five difference-limb containments and returns the inequality over the LIMB VALUES. That bound was
the whole capability limit, and it is gone.

⚑ **`stakeB` IS NO LONGER READ OFF A COLUMN.** It arrives as `hstkTrue`, and the theorem that supplies
it is `LightClientSolStakeFoldAir.solLcAir_table_carrier_from_the_fold`, which reads the emitted
LAST-ROW anchor pin and the fold's own binding — not a bit the prover set. The hypothesis is stated
rather than derived HERE only because `FoldScheme` lives one module up (it needs `Digest8`); this
file is where the pin is emitted, and that file is where the pin is spent. -/
theorem solLcAir_sound (a : Assignment)
    (rootedStk totalStk : Nat) (edB stakeB rootedB authB : Bool)
    (hr : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols qdiffRungs) = (rootedStk : ℤ))
    (ht : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.bCols qdiffRungs) = (totalStk : ℤ))
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hstkTrue : stakeB = true)
    (hrooted : a ROOTED_OK = (if rootedB then (1 : ℤ) else 0))
    (hauth : a AUTH_OK = (if authB then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    solVerifyDecision rootedStk totalStk edB stakeB rootedB authB = true := by
  obtain ⟨hqBodies, hqLimbs, htBodies, htLimbs, hedB, hrootedB, hauthB⟩ := hacc
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
    (hstk : stakeTableOk L ts u = true)
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
  obtain ⟨⟨⟨⟨⟨_hpos, _hthr⟩, hedB⟩, _hstkB⟩, hrootedB⟩, hauthB⟩ := hdec
  refine ⟨hQdiffChain, hQdiffLimbs, hTposChain, hTposLimbs, ?_, ?_, ?_⟩
  · rw [ed_body_zero_iff, hed]; simp [hedB]
  · rw [rooted_body_zero_iff, hrooted]; simp [hrootedB]
  · rw [auth_body_zero_iff, hauth]; simp [hauthB]

/-! ## §6 — the emitted wire JSON (byte-pinned golden) + shape pins. -/

/-- **THE BYTE GOLDEN.** The Rust decoder ingests THIS string (`parse_vm_descriptor2`); a drift on
either side breaks this theorem.

⚑ **RE-EMITTED 2026-08-04 (the second flag day of the day): THE FOLD ABSORBED.** Trace width
`49 → 79`, PIs `23 → 22`, constraints `63 → 103`, declared tables `2 → 4`, and the descriptor is now
MULTI-ROW. `ANCHOR_ROOT` stopped being nine `.first` limbs nothing reads and became the fold's eight
`.last` output lanes; the denominator stopped being four dedicated `.first` columns and became the
fold's accumulator on the last row; `STAKE_TABLE_OK` was DELETED.

⚑ It is a **named theorem**, not a `#guard` (`metatheory/docs/GUARD-DISCIPLINE.md`): a guard is the
same unsafe compiled evaluation with the name, the term and the axiom record deleted. ⚠ MEASURED, so
the label is right — the ~11 KB string is built by too many appends for the kernel, so this stays on
the compiled evaluator and `#assert_compiled` says so, exactly as
`EffectLower.transferLoweredDesc_emits_golden_json` does. -/
theorem solLcVerifyDesc_emits_golden_json :
    emitVmJson2 solLcVerifyDesc =
  "{\"name\":\"dregg-solana-lightclient-verify::v1\",\"ir\":2,\"trace_width\":79,\"public_input_count\":22,\"challenges\":0,\"tables\":[{\"id\":98,\"name\":\"range_w29\",\"arity\":1,\"sem\":\"range\",\"bits\":29},{\"id\":93,\"name\":\"range_w24\",\"arity\":1,\"sem\":\"range\",\"bits\":24},{\"id\":85,\"name\":\"range_w16\",\"arity\":1,\"sem\":\"range\",\"bits\":16},{\"id\":77,\"name\":\"range_w8\",\"arity\":1,\"sem\":\"range\",\"bits\":8}],\"constraints\":[{\"t\":\"lookup\",\"table\":98,\"tuple\":[{\"t\":\"var\",\"v\":8}]},{\"t\":\"lookup\",\"table\":98,\"tuple\":[{\"t\":\"var\",\"v\":9}]},{\"t\":\"lookup\",\"table\":98,\"tuple\":[{\"t\":\"var\",\"v\":10}]},{\"t\":\"lookup\",\"table\":98,\"tuple\":[{\"t\":\"var\",\"v\":11}]},{\"t\":\"lookup\",\"table\":98,\"tuple\":[{\"t\":\"var\",\"v\":12}]},{\"t\":\"lookup\",\"table\":98,\"tuple\":[{\"t\":\"var\",\"v\":13}]},{\"t\":\"lookup\",\"table\":98,\"tuple\":[{\"t\":\"var\",\"v\":14}]},{\"t\":\"lookup\",\"table\":98,\"tuple\":[{\"t\":\"var\",\"v\":15}]},{\"t\":\"lookup\",\"table\":93,\"tuple\":[{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":17}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":18}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":19}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":20}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":37}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":38}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":39}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":40}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":29},{\"t\":\"var\",\"v\":30},{\"t\":\"var\",\"v\":31},{\"t\":\"var\",\"v\":32},{\"t\":\"var\",\"v\":33},{\"t\":\"var\",\"v\":34},{\"t\":\"var\",\"v\":35},{\"t\":\"var\",\"v\":36}]},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1397969990}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":1}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":2}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":3}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":4}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":5}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":6}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":7}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":0}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":30},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":32},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":3}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":34},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":36},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":7}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":41},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":41},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":42},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":42},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":43},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":43},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":17}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":42}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":41}}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":37},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"nxt\",\"c\":41}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":37}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":17}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"nxt\",\"c\":42}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":38}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":18}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":41}}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":39},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"nxt\",\"c\":43}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":39}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":19}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":42}}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":40},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":40}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":43}}}}}},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":47}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":48}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":49}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":50}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":51}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":52}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":53}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":54}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":55}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":60}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":61}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":62}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":63}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":64}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":56}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":57}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":58}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":59}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":65}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":66}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":67}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":68}]},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":47}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":37}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":51}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":56}}},\"r\":{\"t\":\"const\",\"v\":8388607}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":48}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":38}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":52}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":57}}},\"r\":{\"t\":\"var\",\"v\":56}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":49}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":39}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":53}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":58}}},\"r\":{\"t\":\"var\",\"v\":57}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":50}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":40}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":59}}},\"r\":{\"t\":\"var\",\"v\":58}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"const\",\"v\":-128}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":37}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":37}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":60}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":65}}},\"r\":{\"t\":\"const\",\"v\":8388607}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":38}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":38}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":61}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":66}}},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":39}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":62}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":67}}},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":40}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":63}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":68}}},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":64}}},\"r\":{\"t\":\"const\",\"v\":-128}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":44},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":45},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":46},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":29,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":30,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":31,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":32,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":33,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":34,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":35,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":36,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":69,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":70,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":71,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":72,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":73,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":74,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":75,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":76,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":77,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":78,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":37,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":38,\"pi_index\":19},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":39,\"pi_index\":20},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":40,\"pi_index\":21}],\"hash_sites\":[],\"ranges\":[]}" := by
  native_decide

#assert_compiled solLcVerifyDesc_emits_golden_json


/-- Shape pins (robust; a layout drift moves these). Converted from `#guard` per
`metatheory/docs/GUARD-DISCIPLINE.md` — a `#guard` is the same unsafe evaluation with the name, the
term and the axiom record deleted, and `decide` here is strictly stronger than the guard was. -/
theorem sol_shape_pins :
    solLcVerifyDesc.traceWidth = SOL_LC_WIDTH
      ∧ solLcVerifyDesc.piCount = PI_COUNT
      ∧ solLcVerifyDesc.constraints.length = 103
      ∧ solLcVerifyDesc.tables.length = 4 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  decide

/-- ⚑ **THE LEG CENSUS, SO A DROPPED LEG MOVES A NUMBER.** Thirty-three fold legs, five quorum range
legs, ten generated chain legs, three carrier pins and twenty-two PI pins — and the emitted constraint
count is 103 because a `.limbs` leg is one lookup PER LIMB and a chip absorb is one lookup. A
re-emission that silently dropped a limb moves `totalRangeLookups`; the old shape had no number
to move. -/
theorem sol_leg_census :
    solLcVerifyAir.legs.length = 73
      ∧ solLcVerifyAir.lookupCount = 3
      ∧ solLcVerifyAir.limbsCount = 8
      ∧ solLcVerifyAir.windowCount = 40
      ∧ solLcVerifyAir.pinCount = 22
      ∧ solLcVerifyAir.totalRangeLookups = 38 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- …and the two PI-pin ROWS, which is the whole content of this pass: **twelve `.last` pins** (the
eight fold root lanes and the four accumulator limbs — the values DERIVED from the exhibited rows) and
**ten `.first` pins** (the nine bank-root limbs and the slot — the values still merely carried). A pin
that drifted from `.last` back to `.first` would be a root that binds nothing again, and it would move
this number. -/
theorem sol_pin_rows :
    solLcVerifyAir.pinCountRow VmRow.last = 12
      ∧ solLcVerifyAir.pinCountRow VmRow.first = 10 := by
  refine ⟨by decide, by decide⟩

/-- …and each chain is FIVE generated legs for four rungs — one per rung plus the closure gate that
forces the final carry into the top difference limb. Without the closure gate the prover could dump a
residue into a carry nothing reads, and the recomposition would be off by `2^64`. -/
theorem sol_chain_gate_counts :
    qdiffChainLegs.length = 5 ∧ tposChainLegs.length = 5 := by decide

/-- The three carrier/gate bits are real trace columns and none is PI-bound (the results ride hidden).
⚑ There were FOUR; `STAKE_TABLE_OK` is gone, replaced by `anchorRootPins`. -/
theorem sol_carriers_are_hidden_columns :
    ED_OK < SOL_LC_WIDTH ∧ ROOTED_OK < SOL_LC_WIDTH ∧ AUTH_OK < SOL_LC_WIDTH := by decide

/-- ⚑⚑ **THE DENOMINATOR IS THE FOLD'S ACCUMULATOR — by `rfl`, not by a gate that could be dropped.**

`TOTAL_STK_LIMB i` and `ACC i` are the SAME COLUMN, and `LimbTally.bCols qdiffRungs` — the column list
the quorum chain's `β` operand reads — is literally the accumulator's four columns. There is no
equality gate here to weaken and no second copy to leave unforced: the number the quorum divides by
IS the number the fold's limb-addition chain accumulates over the exhibited rows. -/
theorem sol_denominator_is_the_fold_accumulator :
    (∀ i ∈ [0, 1, 2, 3], TOTAL_STK_LIMB i = ACC i)
      ∧ LimbTally.bCols qdiffRungs = [ACC 0, ACC 1, ACC 2, ACC 3]
      ∧ LimbTally.aCols tposRungs = [ACC 0, ACC 1, ACC 2, ACC 3] := by decide

/-- The quorum block occupies columns 47..68 contiguously, above the fold and below the two values
still merely carried: four rooted-stake limbs, five quorum-difference limbs, four quorum carries, five
floor-difference limbs, four floor carries. ⚑ The DENOMINATOR is not in this range — it is cols 37..40,
inside the fold. -/
theorem sol_tally_block_layout :
    TOTAL_STK_LIMB 0 = 37 ∧ TOTAL_STK_LIMB 3 = 40
      ∧ ROOTED_STK_LIMB 0 = 47 ∧ ROOTED_STK_LIMB 3 = 50
      ∧ QDIFF_LIMB 0 = 51 ∧ QDIFF_TOP = 55
      ∧ QDIFF_CARRY 0 = 56 ∧ QDIFF_CARRY 3 = 59
      ∧ TPOS_LIMB 0 = 60 ∧ TPOS_TOP = 64
      ∧ TPOS_CARRY 0 = 65 ∧ TPOS_CARRY 3 = 68
      ∧ TPOS_CARRY 3 < BANK_ROOT 0 := by decide

/-- The rooted-bank-root anchor is unchanged in shape and only shifted: nine limbs, contiguous cols
69..77 → PI 8..16, MSB-first, `⌈256/31⌉ = 9` covering the full 256 bits. -/
theorem sol_bank_root_anchor_layout :
    BANK_ROOT_LIMBS = 9 ∧ bankRootPins.length = BANK_ROOT_LIMBS
      ∧ BANK_ROOT 0 = 69 ∧ BANK_ROOT 8 = 77
      ∧ SLOT_COL = 78 ∧ PI_SLOT = 17
      ∧ PI_BANK_ROOT 0 = 8 ∧ PI_BANK_ROOT 8 = 16 ∧ PI_BANK_ROOT 8 < PI_SLOT
      ∧ BANK_ROOT 8 < SLOT_COL
      ∧ 31 * BANK_ROOT_LIMBS ≥ 256 := by decide

/-- ⚑⚑⚑ **THE WS STAKE-TABLE ROOT IS THE FOLD'S OUTPUT — this replaces
`sol_anchor_root_is_bound_at_full_width`, which was a statement about WIDTH.**

Eight lanes, contiguous cols 29..36 → PI 0..7, pinned on the LAST ROW, and every one of them is a
`ROOT_OUT` column of the fold. The conjunct that carries the change is the last one: the anchor lanes
and the accumulator limbs are BOTH `.last`, so the commitment and the denominator the light client
compares against governance are read off the same row of the same fold.

⚠ **Say the number, and say the right half of the pair.** Eight BabyBear lanes are
`8 · 30.906891 = 247.255128` bits of image; the bound that governs an equivocating prover — who needs
TWO tables with ONE root — is the BIRTHDAY COLLISION figure `2^123.63`, not the `~2^247.3`
second-preimage figure for the same object. `LightClientSolStakeFoldAir.FoldScheme` carries the
binding whose residual is exactly that collision, named as a PAIR the extractor returns rather than
assumed away. -/
theorem sol_anchor_root_is_the_fold_output :
    ANCHOR_LANES = 8 ∧ anchorRootPins.length = ANCHOR_LANES
      ∧ (∀ j ∈ [0, 1, 2, 3, 4, 5, 6, 7], ANCHOR_ROOT j = ROOT_OUT j)
      ∧ ANCHOR_ROOT 0 = 29 ∧ ANCHOR_ROOT 7 = 36
      ∧ PI_ANCHOR_ROOT 0 = 0 ∧ PI_ANCHOR_ROOT 7 = 7
      ∧ anchorRootPins = [.pin ⟨VmRow.last, ROOT_OUT 0, 0⟩, .pin ⟨VmRow.last, ROOT_OUT 1, 1⟩
                         , .pin ⟨VmRow.last, ROOT_OUT 2, 2⟩, .pin ⟨VmRow.last, ROOT_OUT 3, 3⟩
                         , .pin ⟨VmRow.last, ROOT_OUT 4, 4⟩, .pin ⟨VmRow.last, ROOT_OUT 5, 5⟩
                         , .pin ⟨VmRow.last, ROOT_OUT 6, 6⟩, .pin ⟨VmRow.last, ROOT_OUT 7, 7⟩]
      ∧ totalStakePins = [.pin ⟨VmRow.last, ACC 0, 18⟩, .pin ⟨VmRow.last, ACC 1, 19⟩
                         , .pin ⟨VmRow.last, ACC 2, 20⟩, .pin ⟨VmRow.last, ACC 3, 21⟩] := by
  refine ⟨rfl, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **AND THE 247.26-BIT / 2^123.63 PAIR, AS ARITHMETIC RATHER THAN AS A SENTENCE.**
`2^247 < p^8 < 2^248` pins the image width between the two integers it sits between, and the two
`2^k` witnesses below it pin the collision bound: `2^123` squared is under the image and `2^124`
squared is over it, so the birthday figure is strictly between 123 and 124 — and the second-preimage
figure, which is the WHOLE 247, is the one this theorem refuses to state alone. -/
theorem sol_anchor_lane_bound_is_the_collision_figure :
    (2 : ℤ) ^ 247 < Dregg2.Circuit.Emit.EffectLower.P ^ 8
      ∧ Dregg2.Circuit.Emit.EffectLower.P ^ 8 < (2 : ℤ) ^ 248
      ∧ ((2 : ℤ) ^ 123) ^ 2 < Dregg2.Circuit.Emit.EffectLower.P ^ 8
      ∧ Dregg2.Circuit.Emit.EffectLower.P ^ 8 < ((2 : ℤ) ^ 124) ^ 2 := by
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hp] <;> norm_num

/-! ## §6b — ⚑⚑ WHAT THIS AIR BINDS AND WHAT IT STILL ONLY CARRIES: measured, not described.

The header used to call the anchor binding a "NOT-YET-CLOSED named residual". That was prose, and
prose is not a gate (`feedback-a-documented-wound-is-not-a-detected-one`). This section makes it a
decidable fact about the EMITTED object, and it has now gone red TWICE and been rewritten twice — once
when the denominator was published, once when the fold landed. That is the mechanism, not a defect in
it.

⚑ **THE THREE DECOMPOSITIONS, IN ORDER.** Measured on the emitted constraint list, columns adjacent
iff one constraint names both.

    2026-08-03   {0}{1}{2}{3}  {4…29}  {30}{31}…{40}
                 four carrier bits · the tally · ELEVEN published singletons

    2026-08-04a  {0}{1}{2}{3}  {4…29}∪{PI 19..22}  {30…38}  {39…47}{48}
                 the DENOMINATOR joined the tally; the anchor root widened to nine limbs
                 and stayed a set of singletons

    2026-08-04b  {0…68}  {69}{70}…{78}          ← THIS COMMIT
                 the fold, the tally and the published root and denominator are ONE component;
                 the bank root and the slot are the only singletons left

What a verifying proof NOW says that it did not: *the eight-lane commitment in the public statement is
the image of the stake-table rows this trace exhibited, and the denominator the quorum divided by is
what those same rows add up to.* What it STILL does not say: that the bank hash is anything in
particular.

⚠ This is not a defect in `solLcAir_no_forgery` — read its HYPOTHESES. `hr`, `ht`, `hed`, `hrooted`,
`hauth` say "row `a` reads update `u`'s TRUE projections", and they are supplied from OUTSIDE the
circuit. What CHANGED is `hstk`: it used to be that same kind of relation on a witnessed bit, and it
is now discharged by `LightClientSolStakeFoldAir.solLcAir_table_carrier_from_the_fold` from the
emitted last-row pin. -/

/-- The trace columns an `EmittedExpr` reads. -/
def exprCols : EmittedExpr → List Nat
  | .var c    => [c]
  | .const _  => []
  | .add l r  => exprCols l ++ exprCols r
  | .mul l r  => exprCols l ++ exprCols r

/-- The trace columns a two-row `WindowExpr` reads. ⚑ `loc c` and `nxt c` are the SAME column: the
question is which columns a constraint JOINS. -/
def windowCols : WindowExpr → List Nat
  | .loc c   => [c]
  | .nxt c   => [c]
  | .const _ => []
  | .add l r => windowCols l ++ windowCols r
  | .mul l r => windowCols l ++ windowCols r

/-- The trace columns a constraint ARITHMETICALLY relates. A `piBinding` contributes NOTHING here on
purpose: it ties a column to a public input, not to another column, so it cannot connect the anchor
block to the evidence. That asymmetry is exactly what this section measures.

⚑ **THE `.windowGate` ARM IS NEW AND IT HAD TO BE.** Until this commit this descriptor emitted no
window gates, so the catch-all `| _ => []` was harmless. It is not harmless now: the fold's eight
continuity gates and four accumulator steps are `windowGate`s, and a census that returned `[]` for
them would UNDER-report — which, for the `∉` tripwires below, means reporting a stronger result than
the object supports. A measurement that gets easier to pass as the object grows is not a
measurement. -/
def constraintCols : VmConstraint2 → List Nat
  | .base (.gate b)          => exprCols b
  | .base (.boundary _ b)    => exprCols b
  | .base (.transition hi lo) => [hi, lo]
  | .lookup l                => l.tuple.flatMap exprCols
  | .windowGate w            => windowCols w.body
  | _                        => []

/-- The twenty-two PI-bound columns: the EIGHT fold root lanes, the nine bank-root limbs, the slot,
and the four accumulator limbs the quorum divides by. -/
def publicAnchorCols : List Nat :=
  [ANCHOR_ROOT 0, ANCHOR_ROOT 1, ANCHOR_ROOT 2, ANCHOR_ROOT 3,
   ANCHOR_ROOT 4, ANCHOR_ROOT 5, ANCHOR_ROOT 6, ANCHOR_ROOT 7,
   BANK_ROOT 0, BANK_ROOT 1, BANK_ROOT 2, BANK_ROOT 3, BANK_ROOT 4,
   BANK_ROOT 5, BANK_ROOT 6, BANK_ROOT 7, BANK_ROOT 8, SLOT_COL,
   TOTAL_STK_LIMB 0, TOTAL_STK_LIMB 1, TOTAL_STK_LIMB 2, TOTAL_STK_LIMB 3]

/-! ### ⚑⚑ THE TRIPWIRE THAT FIRED THIS TIME, AND WHAT REPLACED IT.

`sol_anchor_root_remains_arithmetically_inert` was `by decide` and is GONE, because `decide` proved it
FALSE the moment the fold landed:

    error: Tactic `decide` proved that the proposition
      ∀ c ∈ solLcVerifyDesc.constraints, ∀ col ∈ constraintCols c,
        col ∉ [ANCHOR_ROOT 0, …, ANCHOR_ROOT 8]
    is false

That is the mechanism working exactly as the lane that wrote it intended — *"the day any of them
lands, the corresponding theorem FAILS. Shrinking its literal is then the correct move; weakening the
statement is not."* Its replacement is the POSITIVE form, and it is strictly more specific than the
negation: not "something reads the anchor" but "the anchor lane is the OUTPUT of a chip absorb whose
input tuple carries this row's pubkey lanes and stake limbs". -/

/-- ⚑⚑⚑ **THE ANCHOR ROOT IS DERIVED, AND THE CONSTRAINT THAT DERIVES IT NAMES THE EVIDENCE.**

For every one of the eight published root lanes there is a SINGLE constraint of `solLcVerifyDesc` that
names that lane, a pubkey lane and a stake limb together — the second chip absorb's tuple
`[16, MID₀…MID₇, VOTER₈, STAKE₀…STAKE₃, 0, 0, 0, ROOT_OUT₀…ROOT_OUT₇]`. The light client's trust
anchor and the row's own evidence are ADJACENT, not merely in one component after a long walk.

⚠ Connectivity is co-occurrence, not derivation — the standing caveat, and it binds here. What
upgrades this particular co-occurrence to derivation is `DescriptorIR2.chip_lookup_sound_N` at the
emitted tuple: the eight output columns are FORCED against the chip table the genuine Poseidon2
permutation serves, so the published root is not equal to a witness, it is the IMAGE of one. -/
theorem sol_anchor_root_is_derived_from_the_stake_rows :
    ∀ j ∈ [0, 1, 2, 3, 4, 5, 6, 7],
      solLcVerifyDesc.constraints.any (fun c =>
        ANCHOR_ROOT j ∈ constraintCols c
          && VOTER 8 ∈ constraintCols c
          && STAKE 0 ∈ constraintCols c) = true := by
  decide

/-- ⚑⚑ **AND THE DENOMINATOR IS DERIVED FROM THE SAME ROWS.** Every published accumulator limb
co-occurs with the row's own stake limb in an accumulator gate — so the number the quorum divides by
is the number these rows add up, not a number the light client and the prover merely agree to write
down. -/
theorem sol_denominator_is_derived_from_the_stake_rows :
    ∀ i ∈ [0, 1, 2, 3],
      solLcVerifyDesc.constraints.any (fun c =>
        TOTAL_STK_LIMB i ∈ constraintCols c && STAKE i ∈ constraintCols c) = true := by
  decide

/-- ⚑ **THE QUORUM ARITHMETIC READS THE DERIVED DENOMINATOR.** There EXISTS a quorum-chain gate whose
body names both a published accumulator limb and a quorum-difference limb — so the fold's total and
the threshold comparison are one component, and not two blocks that happen to publish compatible
numbers. -/
theorem sol_quorum_reads_the_derived_denominator :
    solLcVerifyDesc.constraints.any (fun c =>
      TOTAL_STK_LIMB 0 ∈ constraintCols c && QDIFF_LIMB 0 ∈ constraintCols c) = true := by
  decide

/-- ⚑ **EVERY TOTAL-STAKE LIMB IS PI-BOUND, ON THE LAST ROW** — the denominator is published in full,
not in part, and from the row where the fold has finished. A proof that pinned three of four would let
the prover move the fourth; a proof that pinned them on the FIRST row would publish a prefix total. -/
theorem sol_denominator_is_fully_pinned :
    totalStakePins.length = 4
      ∧ (∀ i ∈ [0, 1, 2, 3], TOTAL_STK_LIMB i ∈ publicAnchorCols)
      ∧ PI_TOTAL_STK 0 = 18 ∧ PI_TOTAL_STK 3 = 21
      ∧ PI_TOTAL_STK 3 < PI_COUNT := by decide

/-- ⚑ **AND THE HALF THAT IS STILL OPEN, KEPT AS A TRIPWIRE IN THE SAME SHAPE — now NARROWER.**

The nine bank-root limbs and the slot are STILL read by no gate body, no boundary body, no window-gate
body and no lookup tuple: the claimed bank hash and rooted slot are carried THROUGH the proof, not
constrained BY it. `ED_OK` derived from the vote message built on `BANK_ROOT` + `SLOT` is what would
close this, and it is the Ed25519/EC arc.

⚠ **TRIPWIRE, and it is meant to go red.** Its predecessor covered eleven columns, then nineteen; this
one covers TEN, because nine of them stopped being carried and started being computed. Deleting it
when the Ed25519 arc lands is the correct move; weakening it is not. -/
theorem sol_bank_root_and_slot_remain_arithmetically_inert :
    ∀ c ∈ solLcVerifyDesc.constraints, ∀ col ∈ constraintCols c,
      col ∉ [BANK_ROOT 0, BANK_ROOT 1, BANK_ROOT 2, BANK_ROOT 3, BANK_ROOT 4,
             BANK_ROOT 5, BANK_ROOT 6, BANK_ROOT 7, BANK_ROOT 8, SLOT_COL] := by
  decide

/-- ⚑ …and the three carrier/gate bits are still read by NOTHING but their own forcing gates, so no
arithmetic anywhere else in the descriptor depends on them. Each is a one-column island. ⚑ There were
FOUR of these islands; `STAKE_TABLE_OK` is not one of them any more because it is not a column any
more. -/
theorem sol_carriers_are_one_column_islands :
    ∀ c ∈ solLcVerifyDesc.constraints, ∀ col ∈ constraintCols c,
      col ∈ [ED_OK, ROOTED_OK, AUTH_OK] → constraintCols c = [col] := by
  decide

/-! ## §6c — ⚑⚑ THE RECORD OF WHY `STAKE_TABLE_OK` WAS A CARRIER, AND WHAT ACTUALLY CLOSED IT.

Kept, because the reasoning that DELAYED this binding is more instructive than the binding.

`LightClientSolHashFold` gave the exclusion as RESIDUAL #3: *"the chained SHA fold cannot be
flat-merged into `solLcVerifyDesc`'s byte-golden `emitVmJson2` … `solLcVerifyDesc` and its golden are
UNTOUCHED — NO VK regen."*

⚠ **THAT REASON WAS NOT THE REAL ONE, AND IT IS THE KIND THIS REPO FORBIDS.** "byte-golden",
"UNTOUCHED", "NO VK regen" are compatibility costs, and `CLAUDE.md` is explicit that a re-emit and a
VK rotation are ordinary work here. This descriptor's golden has now been re-emitted FOUR times in
nine days.

⚑ **The real reason was COST, and it was never stated as a number until 2026-08-04.** Measured by
evaluating the emitters in `Sha256MerkleFold` rather than reading their docblocks:

| object | constraints | trace columns |
|---|---|---|
| `sha256Block` (schedule ‖ compress ‖ feed-forward) | **40,928** | **29,096** |
| `sha256PairHash` (2 blocks + IV/pad pins) | **82,648** | **59,216** |
| `EpochStakeTable::root` at 703 live vote accounts (441 blocks) | **18,049,248** | **12,831,336** |
| the widest descriptor this tree has ever EMITTED | — | 15,611 |
| the widest that parses, checks and **PROVES** | — | **2,131** |
| ⚑ **this whole descriptor, after absorbing the fold** | **103** | **79** |

⚠ The docblocks in `LightClientSolHashFold` and both ETH folds say *"~30k gates/block"*. The measured
figure is **40,928** — understated by 36%, and it was the number three files reasoned from.

⚑⚑ **AND THE CHEAP PATH WAS NOT SHA, WHICH IS THE WHOLE FINDING.** A Poseidon2 absorb on this stack is
ONE `VmConstraint2.lookup` on the chip bus — the permutation lives in a separate chip AIR, so the main
descriptor pays a lookup and eight output columns, not 40,928 gates. The stake-table commitment is
**dregg-authored** (`STAKE_TABLE_ROOT_TAG = b"dregg-solana-stake-table-root:v1"`,
`bridge/src/solana_consensus.rs:118`), pinned by a **dregg-authored** `WeakSubjectivityAnchor`
(`bridge/src/solana_provenance.rs:574`). Nothing on Solana's side computes it. **The commitment was
ours to pick and we had picked the one hash the prover cannot afford.**

So the honest status of `STAKE_TABLE_OK` was never "too expensive to derive"; it was "expensive in the
hash we happened to pick". Re-picking it cost **44 columns and 46 constraints**, and the carrier is
gone.

### ⚑ WHAT RE-ANCHORS — the flag day, stated so it is findable

* **`EpochStakeTable::root` must move to this Poseidon2 frame** (tag → `dregg-solana-stake-table-
  root:v2`) and every `WeakSubjectivityAnchor.stake_table_root` must be RE-DERIVED. Until it does, a
  caller that supplies the SHA-256 root as `PI[0..7]` gets a REFUSAL at the last-row pin — not a
  silent accept, which is the behaviour this repo asks for from a shape change.
* **`SolLeaf.tableCommit` should be INSTANTIATED at `FoldScheme.tableRoot`**, at which point
  `SolLeaf.noTableCollision` is no longer a named `Prop` carrier: it is
  `FoldScheme.tableRoot_binds_or_collides`, whose residual is a SPECIFIC pair a total extractor
  returns at `2^123.63`. That instantiation is the remaining half of the carrier retirement, and it is
  a Lean-side construction with no Rust or wire consequence at all.

### ⚠ WHAT IS STILL A CARRIER, SO THE CLOSE IS NOT READ WIDER THAN IT IS

* **`ED_OK`** — no in-AIR ed25519. The numerator's signatures are asserted.
* **`ROOTED_STK`** — a witnessed projection. The prover still chooses WHICH of the bound validators it
  claims voted; the fold binds WHO IS IN THE TABLE and WHAT THE TOTAL IS, and neither of those is the
  numerator.
* **`BANK_ROOT` / `SLOT`** — carried, not constrained (`sol_bank_root_and_slot_remain_arithmetically
  _inert`).
* **The FRI floor** — a dregg-side STARK inherits it, unchanged by any of this. -/

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

/-- The honest LAST ROW at live mainnet-beta scale, as the cell vector a Rust harness fills. Written
as a LIST so the Lean row and the Rust trace row are literally the same 79 numbers in the same order —
a divergence between the two is a diff on one object, not a comparison of two readings.

⚑ It is the LAST row of a table whose ONE non-zero entry is that last row: a single vote account
holding all of mainnet-beta's active stake, with every earlier row the canonical ZERO ENTRY. That is
not a realistic validator set and is not meant to be — it is the smallest arrangement whose
ACCUMULATOR reaches the live figure ON THE ROW THE QUORUM READS. The Rust release harness proves the
same statement over a many-row table with real members.

⚠ **THE TWENTY-FOUR CHIP-CHAIN CELLS (`ROOT_IN`, `MID`, `ROOT_OUT`) ARE ZERO HERE, AND THAT IS A
STATEMENT ABOUT LEAN, NOT ABOUT THE ROW.** They are the deployed Poseidon2 chip's running images, and
nothing in this file models Poseidon2 (`LightClientSolStakeFoldAir` §4 carries it as an OPAQUE
`List ℤ → Digest8` for exactly this reason). No conjunct of `airAccepts` reads them: what Lean checks
here is the QUORUM block plus the accumulator, and what fills those lanes with the genuine permutation
output — and refuses a forged one — is `circuit/tests/solana_lightclient_proves.rs` on the deployed
prover. Saying "the Lean row and the Rust row are the same 79 numbers" without this caveat would be
false for twenty-four of them, and `the_honest_fill_reproduces_the_lean_row` compares the other
fifty-five rather than pretending otherwise.

⚑ Note the QUORUM CARRIES: `[127, 127, 130, 128]` is `[−1, −1, +2, 0]` offset by 128 — two rungs
BORROW and one carries `+2`, so the chain is not trivially satisfied. The quorum difference denotes
`3·R − 2·T − 1 = 2`; live active stake is divisible by 3, so the STRICT minimum overshoots the ratio
by exactly one lamport of rooted stake. -/
def solMaxScaleCells : List ℤ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0            -- ROOT_IN  0..7 — the chip's running image, NOT modelled in Lean
  , 11, 22, 33, 44, 55, 66, 77, 88, 99 -- VOTER    0..8 (a canonical nonet; the fold binds ROWS)
  , 62195, 52452, 5388, 1537          -- STAKE    0..3 = 432650183925625587 (live active stake)
  , 0, 0, 0, 0, 0, 0, 0, 0            -- MID      0..7 — the chip's image, NOT modelled in Lean
  , 0, 0, 0, 0, 0, 0, 0, 0            -- ROOT_OUT 0..7 — the chip's image, NOT modelled in Lean
  , 62195, 52452, 5388, 1537          -- ACC      0..3 = the DENOMINATOR, and PI 18..21
  , 0, 0, 0                           -- CARRY    0..2 (a one-entry table carries nothing)
  , 1, 1, 1                           -- ED_OK, ROOTED_OK, AUTH_OK
  , 19619, 13123, 47283, 1024         -- ROOTED_STK limbs = 288433455950417059 (minimal STRICT quorum)
  , 2, 0, 0, 0, 0                     -- QDIFF      limbs = 3·R − 2·T − 1 = 2
  , 127, 127, 130, 128                -- QDIFF carries, offset (honest carries −1, −1, +2, 0)
  , 62194, 52452, 5388, 1537, 0       -- TPOS       limbs = T − 1 = 432650183925625586
  , 128, 128, 128, 128                -- TPOS carries, offset (honest carry 0 rides as 128)
  , 1, 2, 3, 4, 5, 6, 7, 8, 9         -- BANK_ROOT limbs 0..8
  , 436909708 ]                       -- SLOT_COL (the measured live slot)

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
  refine ⟨?_, ?_, ?_, ?_, by decide, by decide, by decide⟩
  · decide
  · decide
  · decide
  · decide

/-- ⚑ **AND THE ROW IS A GENUINE FOLD ROW, not a quorum block with the fold columns left blank.** On a
row whose predecessors are all ZERO ENTRIES the accumulator IS this entry's stake and every carry is
zero — which is the `accStep` identity at a zero incoming total, discharged on the exhibited cells
rather than asserted. So the denominator the quorum reads above is the value the fold's own
limb-addition chain puts there, and the row's OWN stake limbs denote it. -/
theorem solMaxScaleRow_accumulator_is_the_row_stake :
    (∀ i ∈ [0, 1, 2, 3], solMaxScaleRow (ACC i) = solMaxScaleRow (STAKE i))
      ∧ (∀ i ∈ [0, 1, 2], solMaxScaleRow (CARRY i) = 0)
      ∧ LimbTally.limbValue SOL_LIMB_BITS solMaxScaleRow
          [STAKE 0, STAKE 1, STAKE 2, STAKE 3] = 432650183925625587 := by
  refine ⟨by decide, by decide, by decide⟩

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
      ∧ (rootedBody.eval (fun i => if i = ROOTED_OK then 1 else 0) = 0
          ∧ rootedBody.eval (fun _ => 0) ≠ 0)
      ∧ (authBody.eval (fun i => if i = AUTH_OK then 1 else 0) = 0
          ∧ authBody.eval (fun _ => 0) ≠ 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## §8 — axiom hygiene. -/

#assert_axioms sol_qdiff_chain_zero_iff
#assert_axioms sol_tpos_chain_zero_iff
#assert_axioms ed_body_zero_iff
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
#assert_axioms sol_leg_census
#assert_axioms sol_pin_rows
#assert_axioms sol_fold_block_is_the_shared_source
#assert_axioms sol_denominator_is_the_fold_accumulator
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
#assert_axioms solMaxScaleRow_accumulator_is_the_row_stake
#assert_axioms solLcAir_refuses_the_exact_two_thirds_point_at_live_active_stake
#assert_axioms solLcAir_refuses_strict_sub_quorum
#assert_axioms solLcAir_refuses_the_empty_stake_table
#assert_axioms solLcAir_admits_the_nonempty_stake_table
#assert_axioms sol_live_stake_capacity_pair
#assert_axioms sol_carrier_bits_discriminate
-- ⚑⚑ WHAT IS NOT BOUND — the residual, as a decidable fact about the emitted object rather than a
-- sentence in the header. Both are TRIPWIRES: they red when the in-AIR-crypto iteration lands.
#assert_axioms solLcVerifyAir_mainRailOk
#assert_axioms solLcVerifyAir_pinsFit
#assert_axioms locExpr_roundtrips
#assert_axioms sol_anchor_root_is_the_fold_output
#assert_axioms sol_anchor_lane_bound_is_the_collision_figure
#assert_axioms sol_anchor_root_is_derived_from_the_stake_rows
#assert_axioms sol_denominator_is_derived_from_the_stake_rows
#assert_axioms sol_quorum_reads_the_derived_denominator
#assert_axioms sol_denominator_is_fully_pinned
#assert_axioms sol_bank_root_and_slot_remain_arithmetically_inert
#assert_axioms sol_carriers_are_one_column_islands

#print axioms solLcAir_sound
#print axioms solLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientSolanaAir
