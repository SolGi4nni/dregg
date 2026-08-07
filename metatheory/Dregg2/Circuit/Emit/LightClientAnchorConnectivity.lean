/-
# `Dregg2.Circuit.Emit.LightClientAnchorConnectivity` — WHICH light clients relate their claimed block
to the evidence they check. Measured on all seven served descriptors, as named theorems.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this file authors NO AIR. It reads seven already-emitted
`EffectVmDescriptor2` values and states decidable facts about them. Nothing here changes a shipped
object, so nothing here rotates a VK or re-genesises anything.

## The measurement, and why it is a measurement and not an opinion

A `pi_binding` ties one trace column to one public input. It ties it to **nothing else**. So build the
COLUMN-CONNECTIVITY GRAPH of an emitted descriptor — two columns adjacent iff they co-occur in one
constraint that RELATES them: a gate body, a boundary body, a window-gate body, a lookup tuple, a
transition pair, a hash site, a mem/map/umem/proof bus op — and read off the connected components.

**A PI-bound column whose component is a SINGLETON is related to nothing the circuit checks.** The
proof carries its value; no gate is about it. `decorativeAnchors` computes exactly that list, and the
six theorems below pin it, per descriptor, to an explicit literal.

`loc c` and `nxt c` are the SAME column: a window gate relating `loc 9` to `nxt 0` is a genuine edge
`9—0`. That is how `dregg-mina-lightclient-link::v1` earns its `[]`.

⚠ **AN ARITY-1 RANGE LOOKUP READS A COLUMN AND RELATES IT TO NOTHING.** It bounds a shape; it does
not tie a value to the evidence. Counting a 29-bit lane bound as "bound" is exactly the laundering
this file refuses — so `relatedCols` returns a constraint's columns and the predicate additionally
demands there be **two of them**. `LightClientSolanaAir`'s §6b `constraintCols` does not draw that
line (its anchors carry no lookups at all, so it never had to); `minaLcVerifyDesc`'s eighteen state
limbs DO carry lane lookups, and they are decorative all the same.

## ⚑ THE ANSWER, IN THE REGISTER THE MEASUREMENT SUPPORTS

Seven served descriptors. **Three of them relate their published values to anything, and only one of
those two relates them to something the prover did not choose.**

* the Mina LINK rung joins twenty published columns to a chain of WITNESSED lane values;
* ⚑ the Solana STAKE-TABLE FOLD (2026-08-04) joins twelve to the output columns of two deployed
  Poseidon2 chip absorbs. Its published root is the IMAGE of the exhibited rows, not a value equal
  to another witness — which is the distinction this file's `minaLink_decorative_anchors` caveat was
  written to keep visible, now on the other side of it;
* ⚑⚑ and **the Solana VERIFY rung**, which absorbed that fold the same day: twelve of its
  twenty-two published columns are the fold's, and the ten that are not are the bank root and the
  slot.

⚑⚑ **2026-08-04, SECOND PASS: THE SOLANA VERIFY RUNG ABSORBED THE FOLD, AND THREE THEOREMS IN THIS
FILE WENT RED SAYING SO** (`sol_decorative_anchors`, `sol_anchors_are_unread`, the census). That is
the mechanism, not a defect in it. Solana is `19 → 10` and the census `71 → 62`; the nine `.first`
anchor-root limbs are gone and the light client's trust anchor is the fold's eight `.last` output
lanes. A fourth, `sol_pinned_denominator_is_not_decorative`, stayed GREEN while ceasing to be about
the denominator — its columns `[4,5,6,7]` are now `ROOT_IN 4..7` — and repointing it at `[37,38,39,40]`
is the repair that a red would not have prompted.

**The other four VERIFY descriptors are unchanged: fifty-two decorative anchors, none of their
literals moved.** What repairing them costs is the same shape as what repairing Solana's cost: pick a
commitment the prover can afford, and derive the anchor instead of publishing it.

* **`dregg-eth-lightclient-verify::v1`** — `{0} / {1..3}{9} / {4} / {5} / {6} / {7} / {8} / {10}…{20}`.
  ELEVEN of eleven anchors inert, and UNREAD: no constraint of any kind names them, not even a width
  lookup. *The prover exhibited a participation count between 342 and 512 against a committee size it
  also pinned to 512, set three bits to 1, chose a branch depth from `{6,7}` and one equal to 4, and
  separately exhibited eleven public field elements.* Nothing relates the claimed sync-committee root
  or the nine finalized-state-root limbs to the count.

* **`dregg-tm-lightclient-verify::v1`** — `{0..1} / {2..3} / {4..11} / {12} / {13} / {14} / {15..49} /
  {50}…{60}`. ELEVEN of eleven inert and UNREAD. *The prover exhibited two voting-power limb vectors
  satisfying `1 ≤ total`, `signed ≤ total` and `3·signed > 2·total`, exhibited five more numbers
  standing in a time-window relation with three range-checked slacks, asserted that two columns it
  chose are equal and that two others differ by one, set three bits to 1, and separately exhibited
  eleven public field elements.* ⚑ Sharpest here: the chain-id equality holds between **two witnessed
  columns** (`CHAIN_ID` 0, `TS_CHAIN_ID` 1) while the PUBLIC chain-id domain is column 60, in no gate.
  The circuit checks that the prover agreed with itself about which chain this is.

* **`dregg-midnight-lightclient-verify::v1`** — `{0} / {1} / {2} / {3} / {4..38} / {39}…{50}`. TWELVE
  of twelve inert and UNREAD. *The prover exhibited two weight limb vectors satisfying `1 ≤ total`,
  `signed ≤ total` and `3·signed > 2·total`, set four bits to 1, and separately exhibited twelve
  public field elements.* ⚑ `ROUND_OK` (col 2) and `ERA_OK` (col 3) are forced bits; the PUBLISHED
  round and era are columns 49 and 50 and appear in no gate. Nothing relates the bit that is named
  "this precommit names the claimed round" to the claimed round.

* **`dregg-solana-lightclient-verify::v1`** — ⚑ **THE ONE THAT MOVED (2026-08-04).** It read
  `{0}{1}{2}{3} / {4..29} / {30}…{40}`, eleven of eleven inert and UNREAD. It now reads
  `{0}{1}{2}{3} / {4..29} / {30}…{48}`, and the tally component `{4..29}` CONTAINS FOUR PI-BOUND
  COLUMNS — the total-stake limbs 4..7 (`LightClientSolanaAir.totalStakePins`). *The prover exhibits a
  `(total, rooted)` pair clearing `total ≥ 1` and `3·rooted > 2·total`, sets four bits to 1, and
  exhibits nineteen public values — **but `total` is no longer one of the numbers it gets to choose**;
  it is in the public statement, supplied by the light client from its weak-subjectivity anchor.* The
  nineteen decorative anchors are the nine `ANCHOR_ROOT` limbs (widened from ONE 31-bit column in the
  same commit — a 256-bit SHA-256 root that had been bound at 31 bits), the nine `BANK_ROOT` limbs and
  `SLOT_COL`. ⚠ The denominator is pinned; the stake TABLE is not (`LightClientSolanaAir` §6c prices
  the fold that would).

* ⚑⚑ **`dregg-mina-lightclient-verify::v1` — THE SECOND VERIFY RUNG TO MOVE, AND IT MOVED BY HALF
  (2026-08-05, second pass).** It read `{0..7}{11} / {8} / {9} / {10} / {12}…{29}`, EIGHTEEN of
  twenty inert. It now carries **NINE**: the `TIP_STATE` lanes (cols 21..29) left the decorative set
  when `LightClientMinaAir` §2c made them the `commit` vector of a `LINK_OK`-guarded `proofBind`
  pinned to `dregg-mina-lightclient-link::v1`. *The prover exhibits a segment length, an anchor
  height, a submission height and three range-checked slacks in an additive relation; publishes the
  derived block length, the required depth and the anchor height; sets four bits to 1; exhibits nine
  anchor lane values bounded to 29 or 22 bits and tied to nothing — **and names a verifying sub-proof
  of the segment program whose public-input commitment is the nine tip lanes it publishes.***
  ⚑ **PIs did NOT grow.** The tip block was already published; what changed is that a constraint now
  names it. That is the shape of move this file's own §3 asks for — the decorative SHARE fell without
  the denominator moving, which is not what happened when Solana widened a root.
  ⚠ And the caveat that governs is the one `minaLink_decorative_anchors` already carries: the bound
  sub-proof chains WITNESSED lane values. The tip is now the last element of a committed chain whose
  SHAPE is gated; its HASH is still the prover's (`LinkHashResidual`).
  ⚑ Corrections the measurement forced, ONE OF WHICH IS NOW REPAIRED (2026-08-05):
  - ✅ the anchor HEIGHT (`ANCHOR_H`, col 1) WAS a free witness — not PI-bound, not range-looked-up,
    and pinned to no constant, while `LightClientMinaAir` called it "the pinned weak-subjectivity
    anchor's blockchain length". It is now **PI-bound at slot 29**
    (`minaVerify_anchor_height_is_published`), so the consumer can refuse it against the height the
    operator pinned instead of seeing only the sum;
  - ⚠ **STILL OPEN, and the pin did not touch it:** the anchor STATE HASH (cols 12..20) and the
    anchor HEIGHT (col 1) share no constraint at all, because a `piBinding` contributes no edge by
    construction. "The published height is the pinned anchor plus the exhibited segment" is now a
    relation among two prover-chosen numbers and one PUBLISHED one, and nothing in-circuit says the
    published height is the height OF the published hash
    (`minaVerify_anchor_height_shares_no_constraint_with_the_hash`).
  The lane bounds are real and strictly stronger than canonicality (`8·29 + 22 = 254`,
  `2^254 < p_Pasta`) — but they bound each lane of a value tied to nothing.

* ⚑ **`dregg-solana-stake-table-fold::v1`** — `{0..43}`, ONE component, **zero of twelve anchors
  decorative**. *The prover exhibits a sequence of rows, each absorbing the running eight-lane state
  and its own pubkey lanes into an arity-16 Poseidon2 chip row, then that result and its own stake
  limbs into a second — and publishes the LAST row's state as the table's commitment and the LAST
  row's four-limb accumulator as the active-stake denominator.* ⚑ The two publications come from the
  SAME rows, which is what makes a swapped validator set with an IDENTICAL tally move the root
  (`FoldScheme.same_tally_moves_the_root`; on the deployed prover,
  `circuit/tests/solana_stake_table_fold.rs`, 11/11 release).
  ⚠ It binds the DENOMINATOR's provenance and nothing else: `ED_OK` is still a witnessed carrier in
  the sibling rung, the numerator is still a witnessed projection, and the join between the two rungs
  is at the PUBLIC STATEMENT (the verifier compares four felts), not inside one proof.

* **`dregg-mina-lightclient-link::v1`** — `{0}{9} / {1}{10} / … / {8}{17} / {18}{21} / {19..20}`.
  **ZERO decorative anchors: all twenty PI-bound columns are related.** *The prover exhibited a
  sequence of rows in which each row's nine-lane `OWNHASH` equals the next row's nine-lane `PARENT`,
  the heights tick by one from a first-row anchor height, a boolean `IS_REAL` is monotone and its
  running sum is published as the segment length — and the anchor and tip it publishes are the two
  ends of that chain.*
  ⚑ **2026-08-06 — `OWNHASH` STOPPED BEING A FREE WITNESS.** This bullet used to read *"nothing
  forces it to be `Poseidon(stateRow)` (`LinkHashResidual`, priced at ~5·10⁵ BabyBear constraints per
  block hash)"*; the price was wrong by 26× and the rung landed as a `proof_bind` against
  `dregg-pasta-fp-absorb::v1` (`minaLink_the_seam_joins_the_preimage_to_the_image`, below). Every lane
  pair is still its own island for the CHAINING gates — lane `j` chains to lane `j` and never crosses
  — but the seam names all thirty-six columns of the row in ONE constraint.
  ⚠ **AND THAT IS STILL NOT A BINDING TO MINA.** What the seam takes as an ARGUMENT is `BODYHASH`,
  which this descriptor neither derives nor publishes. ⚑ 2026-08-07 it acquired a derivation —
  `MinaStateBodyHashChain`, 25 links of `dregg-pasta-fp-chainlink::v1` from the pinned
  `MinaProtoStateBody` salt — but **OFF THIS DESCRIPTOR**, so no constraint here relates the nonet to
  that chain's root and `minaLink_body_hash_is_joined_but_not_published` did NOT fire. **Connectivity
  is co-occurrence, not derivation**, and the tie that would upgrade this one needs `BODYHASH`
  PUBLISHED so a fold can reach it.

## ⚑ WHY THESE ARE THEOREMS AND NOT A COMMENT — they are meant to go RED

The in-AIR-crypto iteration is exactly the change that makes an anchor column appear beside another
column in a gate: `BLS_OK` derived from `COMMITTEE_ROOT`, `STAKE_TABLE_OK` from the table fold into
`ANCHOR_ROOT`, `AUTHSET_OK` from the set fold, `LINK_OK` from the Poseidon chain. **The day any of
them lands, the corresponding theorem below FAILS.** Shrinking its literal is then the correct move;
weakening the statement is not. A comment saying the same thing rots silently.

The predicate is SATISFIABLE, REFUTABLE and NOT PROVABLE in general
(`feedback-prove-the-floor-false`): `minaLink_decorative_anchors` exhibits `[]`, the other five
exhibit non-empty lists, and no lemma here derives either from the shape of a descriptor.

Companion gate: `scripts/check-descriptor-anchor-inertness.py` runs the same decomposition over all
84 served descriptors as a ratchet (`scripts/descriptor-anchor-inertness-baseline.txt`), so a NEW
descriptor cannot be served with unbound public inputs without moving a committed number.
-/
import Dregg2.Circuit.Emit.LightClientEthAir
import Dregg2.Circuit.Emit.LightClientTendermintAir
import Dregg2.Circuit.Emit.LightClientMidnightAir
import Dregg2.Circuit.Emit.LightClientSolanaAir
import Dregg2.Circuit.Emit.LightClientMinaLinkAir
import Dregg2.Circuit.Emit.LightClientSolStakeFoldAir

set_option autoImplicit false
set_option maxHeartbeats 1600000
-- ⚑ 2026-08-05: `minaVerify_anchor_height_shares_no_constraint_with_the_hash` decides a nested
-- quantifier over (nine columns × every constraint of the Mina head descriptor), and the segment
-- bind took that descriptor to 63 constraints — one past the default depth. `set_option` does not
-- cross an import, so it is stated here rather than inherited from `LightClientMinaAir`.
set_option maxRecDepth 4000

namespace Dregg2.Circuit.Emit.LightClientAnchorConnectivity

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2

/-! ## §1 — the graph. Which columns does one constraint RELATE? -/

/-- Duplicate-free `cons` — keeps the column lists small enough that the arity test below is a
length test rather than a set comparison. -/
def nub : List Nat → List Nat
  | []      => []
  | c :: cs => let r := nub cs; if c ∈ r then r else c :: r

/-- The trace columns a row-local `EmittedExpr` reads. -/
def exprCols : EmittedExpr → List Nat
  | .var c   => [c]
  | .const _ => []
  | .add l r => exprCols l ++ exprCols r
  | .mul l r => exprCols l ++ exprCols r

/-- The trace columns a two-row `WindowExpr` reads. ⚑ `loc c` and `nxt c` are the SAME column: the
question is which columns a constraint JOINS, and a window gate relating `loc 9` to `nxt 0` joins
columns 9 and 0. -/
def windowCols : WindowExpr → List Nat
  | .loc c   => [c]
  | .nxt c   => [c]
  | .const _ => []
  | .add l r => windowCols l ++ windowCols r
  | .mul l r => windowCols l ++ windowCols r

/-- ⚑ **THE COLUMNS A CHALLENGE BODY NAMES** (2026-08-05). `ChalExpr` is `WindowExpr` plus a `chal i`
leaf, and that leaf is **NOT A COLUMN**: it is a value the VERIFIER draws after the trace is
committed. Folding it in as a column would make every challenge gate join every other one through a
phantom node and silently connect anchors that share nothing — the exact laundering this file exists
to refuse. So `chal` contributes `[]`.

⚠ This replaces `windowCols w.body` in the `.chalGate` arm, which did not typecheck (`w.body` is a
`ChalExpr`) and left the whole module red once `TableAirIR` was rebuilt against the widened
`VmRowEnv`. -/
def chalCols : ChalExpr → List Nat
  | .loc c   => [c]
  | .nxt c   => [c]
  | .const _ => []
  | .chal _  => []
  | .add l r => chalCols l ++ chalCols r
  | .mul l r => chalCols l ++ chalCols r

/-- ⚑ **THE COLUMNS ONE CONSTRAINT RELATES.** A `piBinding` contributes NOTHING on purpose: it ties a
column to a PUBLIC INPUT, not to another column, so it cannot connect an anchor to the evidence. That
asymmetry is the whole thing being measured. Every OTHER form contributes all the columns it reads —
including the bus ops, so a descriptor that grows one cannot slip past this as a silent `[]`. -/
def relatedCols : VmConstraint2 → List Nat
  | .base (.gate b)          => nub (exprCols b)
  | .base (.boundary _ b)    => nub (exprCols b)
  | .base (.transition hi lo) => nub [hi, lo]
  | .base (.piBinding _ _ _) => []
  | .lookup l                => nub (l.tuple.flatMap exprCols)
  | .windowGate w            => nub (windowCols w.body)
  | .chalGate w              => nub (chalCols w.body)
  | .memOp m                 => nub ((exprCols m.guard) ++ (exprCols m.addr) ++ (exprCols m.value) ++
                                     (exprCols m.prevValue) ++ (exprCols m.prevSerial))
  | .umemOp m                => nub ((exprCols m.guard) ++ (exprCols m.key) ++ (exprCols m.present) ++
                                     (exprCols m.value) ++ (exprCols m.prevPresent) ++
                                     (exprCols m.prevValue) ++ (exprCols m.prevSerial))
  | .mapOp m                 => nub ((exprCols m.guard) ++ (exprCols m.key) ++ (exprCols m.value) ++
                                     ((List.ofFn m.root).flatMap exprCols) ++
                                     ((List.ofFn m.newRoot).flatMap exprCols))
  -- ⚑ **LANE VECTORS, NOT ONE LIMB EACH** (the `ProofBind` widening, 2026-08-05). `commit`/`vk`/
  -- `bound` are `List EmittedExpr` now, and this arm read them as if each were a single expression —
  -- which is a TYPE error here and so left the module red, but is the same UNDER-READ that in an
  -- untyped instrument goes silent: `scripts/check-descriptor-anchor-inertness.py` walked only the
  -- operands that are themselves an expression and scored nine BOUND commitment lanes as DECORATIVE
  -- ANCHORS (18 → 27) with no anchor having changed, and `circuit-prove/tests/fold_claim_pin_liveness.rs`
  -- read lane 0 alone and would declare a live pin dead. Three instruments, one blindness; Lean is
  -- the one that could not compile through it.
  --
  -- `bound` is included because `ProofBind.holdsAt` asserts `g·(commitᵢ − boundᵢ) ≡ 0` lane by lane:
  -- those row-local expressions are tied to the commitment by the seam itself, so a walker that
  -- omitted them would under-read exactly the tie this file exists to measure. Every seam served
  -- today declares `bound := none`, so no committed count moves with this — it closes the hole
  -- ahead of the first descriptor that uses it rather than after.
  | .proofBind m             => nub ((exprCols m.guard) ++ (m.commit.flatMap exprCols) ++
                                     (m.vk.flatMap exprCols) ++
                                     ((m.bound.getD []).flatMap exprCols))

/-- A constraint RELATES iff it names at least two distinct columns. ⚑ An arity-1 range lookup and a
one-column forcing gate (`ED_OK − 1`) both fail this, and both should: neither joins anything. -/
def joins (c : VmConstraint2) : Bool := 2 ≤ (relatedCols c).length

/-- Column `col` is PI-bound in `d`. -/
def isPiBound (d : EffectVmDescriptor2) (col : Nat) : Bool :=
  d.constraints.any fun
    | .base (.piBinding _ c _) => c == col
    | _                        => false

/-- Column `col` is READ by some constraint — any constraint, including an arity-1 range lookup. -/
def isRead (d : EffectVmDescriptor2) (col : Nat) : Bool :=
  d.constraints.any fun c => col ∈ relatedCols c

/-- Column `col` is RELATED: some constraint names it alongside another column. This is adjacency in
the connectivity graph, i.e. `col`'s component is not a singleton. -/
def isRelated (d : EffectVmDescriptor2) (col : Nat) : Bool :=
  d.constraints.any fun c => joins c && col ∈ relatedCols c

/-- ⚑⚑ **THE DECORATIVE ANCHORS OF `d`**, ascending: every PI-bound column that no constraint joins
to any other column. The proof carries these values; nothing in the circuit is about them. -/
def decorativeAnchors (d : EffectVmDescriptor2) : List Nat :=
  (List.range d.traceWidth).filter fun col => isPiBound d col && !isRelated d col

/-! ## §2 — the six served descriptors, each pinned to its exact list.

Every theorem below FAILS the day an anchor column enters a gate beside another column. That is the
point of them. -/

/-- ⚑ **ETHEREUM: all eleven published anchors are decorative.** Columns 10..20 —
`COMMITTEE_ROOT`, the nine `FIN_STATE_ROOT` limbs, `DOMAIN_GVR`. ⚠ TRIPWIRE: `BLS_OK` derived from
`COMMITTEE_ROOT`, or `EXEC_OK` from the execution branch fold, reds this. -/
theorem eth_decorative_anchors :
    decorativeAnchors LightClientEthAir.ethLcVerifyDesc = [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by
  decide

/-- …and Ethereum's are not merely unjoined, they are UNREAD: no constraint of any kind names them,
not even a width lookup. So the nine "radix-`2^31` MSB-first limbs" carry no limb-width bound either;
a prover may write any field element into each. -/
theorem eth_anchors_are_unread :
    ∀ col ∈ [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
      isRead LightClientEthAir.ethLcVerifyDesc col = false := by
  decide

/-- ⚑ **TENDERMINT: all eleven published anchors are decorative.** Columns 50..60 —
`TRUSTED_NEXT_VALS_ROOT`, the nine `COMMITTED_APP_HASH` limbs, `CHAIN_ID_DOMAIN`. -/
theorem tm_decorative_anchors :
    decorativeAnchors LightClientTendermintAir.tmLcVerifyDesc = [50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60] := by
  decide

/-- …and unread, so the app-hash widening from one felt to nine limbs added nine columns and no
constraint. -/
theorem tm_anchors_are_unread :
    ∀ col ∈ [50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60],
      isRead LightClientTendermintAir.tmLcVerifyDesc col = false := by
  decide

/-- ⚑ **AND THE CHAIN-ID EQUALITY IS BETWEEN TWO WITNESSES.** `CHAIN_ID` (0) and `TS_CHAIN_ID` (1) are
joined to each other and to nothing else; the PUBLIC `CHAIN_ID_DOMAIN` (60) is joined to nothing. So
the cross-chain-replay gate compares the prover's two copies of a number the verifier never sees. -/
theorem tm_chain_id_domain_is_not_the_chain_id_gate :
    isRelated LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.CHAIN_ID = true ∧
    isRelated LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.TS_CHAIN_ID = true ∧
    isPiBound LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.CHAIN_ID = false ∧
    isPiBound LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.TS_CHAIN_ID = false ∧
    isRead LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.CHAIN_ID_DOMAIN = false := by
  decide

/-- ⚑ **MIDNIGHT: all twelve published anchors are decorative.** Columns 39..50 — `ANCHOR_ROOT`, the
nine `TARGET_ROOT` limbs, `ROUND_COL`, `ERA_COL`. -/
theorem mid_decorative_anchors :
    decorativeAnchors LightClientMidnightAir.midLcVerifyDesc = [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50] := by
  decide

/-- …and unread. -/
theorem mid_anchors_are_unread :
    ∀ col ∈ [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50],
      isRead LightClientMidnightAir.midLcVerifyDesc col = false := by
  decide

/-- ⚑ **AND `ROUND_OK` / `ERA_OK` ARE NOT ABOUT THE PUBLISHED ROUND AND ERA.** The two bits are
columns 2 and 3, each forced `= 1` by a gate naming only itself; the published round and era are
columns 49 and 50 and are read by nothing. `LightClientMidnightAir:198-202` calls these the
"cross-round" and "stale-authority-set" bindings. They bind nothing. -/
theorem mid_round_and_era_bits_are_not_joined_to_the_published_round_and_era :
    isRead LightClientMidnightAir.midLcVerifyDesc LightClientMidnightAir.ROUND_COL = false ∧
    isRead LightClientMidnightAir.midLcVerifyDesc LightClientMidnightAir.ERA_COL = false ∧
    isRelated LightClientMidnightAir.midLcVerifyDesc LightClientMidnightAir.ROUND_OK = false ∧
    isRelated LightClientMidnightAir.midLcVerifyDesc LightClientMidnightAir.ERA_OK = false := by
  decide

/-- ⚑⚑⚑ **SOLANA — THIS LITERAL FIRED TWICE IN ONE DAY, AND THE SECOND TIME IT SHRANK BY NINE.**

Three readings, in order, because only the sequence makes the last one legible:

  * `[30 … 40]` — ELEVEN of eleven anchors decorative, every published column a singleton.
  * `[30 … 48]` — NINETEEN. `totalStakePins` took four columns OUT of the decorative set (the first
    columns in this census ever to leave it) while `ANCHOR_ROOT` widened from ONE 31-bit column to
    nine limbs, putting eight unrelated ones IN. *A raw count is the wrong summary of that change*,
    and the baseline header says so at length.
  * ⚑ **`[69 … 78]` — TEN, and this time the count and the meaning move together.** The nine
    `.first` anchor-root limbs are GONE — replaced by the stake-table fold's eight `.last` output
    lanes, which sit in the one component that contains the whole trace — and the denominator is the
    fold's accumulator. What remains decorative is the bank root (cols 69..77) and the slot (78).

*The prover exhibits a sequence of stake-table rows, absorbing each into an arity-16 Poseidon2 chip
row and accumulating its lamports; publishes the LAST row's eight-lane state as the light client's
weak-subjectivity anchor and the LAST row's four-limb accumulator as the denominator; exhibits a
rooted-stake numerator clearing `3·rooted > 2·total` against THAT denominator; sets three bits to 1;
and separately exhibits ten public field elements.* The ten are what is left. -/
theorem sol_decorative_anchors :
    decorativeAnchors LightClientSolanaAir.solLcVerifyDesc
      = [69, 70, 71, 72, 73, 74, 75, 76, 77, 78] := by
  decide

/-- …and those ten are unread: no constraint of any kind names them, not even a width lookup. -/
theorem sol_anchors_are_unread :
    ∀ col ∈ [69, 70, 71, 72, 73, 74, 75, 76, 77, 78],
      isRead LightClientSolanaAir.solLcVerifyDesc col = false := by
  decide

/-- ⚑⚑ **THE PUBLISHED TRUST ANCHOR IS RELATED — and this is the first anchor ROOT in the census that
is.** Each of the eight `ANCHOR_ROOT` lanes (cols 29..36) is PI-bound, READ, and RELATED, so none is
decorative. Mina-link's twenty joined columns were chained WITNESSES; these eight are the OUTPUT
columns of a deployed Poseidon2 chip absorb whose input tuple carries the stake rows.

⚠ The standing caveat still binds — connectivity is co-occurrence, not derivation. What upgrades
THESE eight is `DescriptorIR2.chip_lookup_sound_N` at the emitted tuple plus
`LightClientSolStakeFoldAir.FoldScheme.tableRoot_binds_or_collides`, and the number that governs is
`2^123.63` (birthday, over `8 · 30.906891 = 247.26` bits) — **not** the `2^247.3` second-preimage
figure for the same object. -/
theorem sol_published_anchor_root_is_not_decorative :
    ∀ col ∈ [29, 30, 31, 32, 33, 34, 35, 36],
      isPiBound LightClientSolanaAir.solLcVerifyDesc col = true ∧
      isRead LightClientSolanaAir.solLcVerifyDesc col = true ∧
      isRelated LightClientSolanaAir.solLcVerifyDesc col = true ∧
      col ∉ decorativeAnchors LightClientSolanaAir.solLcVerifyDesc := by
  decide

/-- ⚑ **AND SO IS THE DENOMINATOR — at the FOLD'S ACCUMULATOR COLUMNS, which is where the literal
had to move.** It read `[4, 5, 6, 7]`, the dedicated total-stake block. Those columns are now
`ROOT_IN 4..7` and are read and related for a completely different reason, so the old statement stayed
**TRUE while ceasing to be about the denominator** — the quietest way a tripwire dies. The
denominator is cols 37..40. -/
theorem sol_pinned_denominator_is_not_decorative :
    ∀ col ∈ [37, 38, 39, 40],
      isPiBound LightClientSolanaAir.solLcVerifyDesc col = true ∧
      isRead LightClientSolanaAir.solLcVerifyDesc col = true ∧
      isRelated LightClientSolanaAir.solLcVerifyDesc col = true ∧
      col ∉ decorativeAnchors LightClientSolanaAir.solLcVerifyDesc := by
  decide

/-- ⚑⚑ **THE STATEMENT THE VERIFY RUNG COULD NOT MAKE UNTIL TODAY: its published anchor and its
evidence are in ONE constraint together.** Every published root lane co-occurs, in a SINGLE
constraint, with a pubkey lane and a stake limb — the second chip absorb's tuple. This is
`solStakeFold_root_shares_a_constraint_with_the_stake_rows`, now true of the LIGHT CLIENT and not only
of the standalone fold rung, because the light client absorbed the fold's legs. -/
theorem sol_anchor_root_shares_a_constraint_with_the_stake_rows :
    ∀ j ∈ [29, 30, 31, 32, 33, 34, 35, 36],
      LightClientSolanaAir.solLcVerifyDesc.constraints.any (fun c =>
        j ∈ relatedCols c
          && LightClientSolanaAir.VOTER 8 ∈ relatedCols c
          && LightClientSolanaAir.STAKE 0 ∈ relatedCols c) = true := by
  decide

/-- ⚑⚑⚑ **MINA VERIFY — THIS LITERAL FIRED, AND IT HALVED. NINE, NOT EIGHTEEN.**

It read `[12 … 29]`: the nine `ANCHOR_STATE` lanes AND the nine `TIP_STATE` lanes, every one of them
PI-bound, width-checked and joined to nothing. **The nine `TIP_STATE` lanes are gone from this list**
— `LightClientMinaAir`'s §2c segment bind (2026-08-05) makes them the `commit` vector of a
`proofBind` guarded by `LINK_OK` and pinned to `dregg-mina-lightclient-link::v1`, so `relatedCols`'
`.proofBind` arm returns all nine of them beside the guard and nine program lanes.

⚑ **THE TRIPWIRE WORKED AS DESIGNED.** This theorem and the one below it were written *to go red the
day an anchor column enters a gate beside another column*; both fired on the same edit. Shrinking the
literal is the correct move and weakening the statement is not — so the positive fact is stated
separately (`minaVerify_tip_lanes_are_published_and_joined`) rather than left as the absence of a
red, and the residual keeps its own narrower tripwire.

⚠ What remains is the ANCHOR half, and it is not an oversight: `ProofBind`'s `commit` is the only
vector that names off-row evidence and there is one `piCommit` per engine, so a second bind against
the same program with a DIFFERENT commitment is incoherent. The anchor's nine lanes are refused at
the CONSUMER against the link sub-proof's own anchor block. That is an executor check, not an edge,
and this literal is what keeps saying so. -/
theorem minaVerify_decorative_anchors :
    decorativeAnchors LightClientMinaAir.minaLcVerifyDesc
      = [12, 13, 14, 15, 16, 17, 18, 19, 20] := by
  decide

/-- ⚑ **AND THIS IS THE CASE `constraintCols` ALONE WOULD MISS — now stated of the NINE that are
still inert.** The anchor lane columns ARE read — each by an arity-1 range lookup at 29 or 22 bits —
and joined to nothing. A width bound is a fact about a value's SHAPE; it is not a tie to the
evidence, and a census that counted "appears in a lookup tuple" as bound would have scored these nine
as connected.

⚑ This is the narrower replacement for `minaVerify_state_lanes_are_read_but_never_joined`, which
covered `[12 … 29]` and fired on the segment bind. Keeping it at the anchor block is what makes the
remaining half a MEASURED residual rather than an unmentioned one. -/
theorem minaVerify_anchor_lanes_are_read_but_never_joined :
    ∀ col ∈ [12, 13, 14, 15, 16, 17, 18, 19, 20],
      isRead LightClientMinaAir.minaLcVerifyDesc col = true ∧
      isRelated LightClientMinaAir.minaLcVerifyDesc col = false := by
  decide

/-- ⚑⚑⚑ **THE POSITIVE STATEMENT: THE HEAD'S PUBLISHED TIP IS JOINED.** Each of the nine
`TIP_STATE` lanes is PI-bound (so a consumer can compare it against a head it holds), READ, and
RELATED — none is decorative. This is the flip of the deleted
`minaVerify_state_lanes_are_read_but_never_joined`, stated in the affirmative so the gain is a term
and not the absence of a red.

⚠ The standing caveat binds here as it does everywhere in this file: **connectivity is co-occurrence,
not derivation.** What these nine co-occur with is a guard and a pinned program identity; what
upgrades that to evidence is off-row — `Satisfied2Custom.proofBound`'s existential, discharged by a
consumer that verifies a STARK over `dregg-mina-lightclient-link::v1`. ⚑ **AND THE CAVEAT THAT USED TO SIT HERE HAS MOVED ONE RUNG DOWN, 2026-08-06.** This paragraph
read *"that sub-proof's own caveat still holds: its `OWNHASH` is a free witness, so what is gated is
the segment's SHAPE, not its hashes."* The segment descriptor now carries a `proof_bind` of its own
whose commitment is `salt ‖ PARENT ‖ BODYHASH ‖ OWNHASH` against
`dregg-pasta-fp-absorb::v1` — so `OWNHASH` is the IMAGE of its row at the same recursion boundary
this seam stands at (`minaLink_the_seam_joins_the_preimage_to_the_image`, below). What remains free
is `BODYHASH`, and what attests THAT is `PICKLES_OPENING_WITNESSED` (⚑ renamed 2026-08-06 from
`PICKLES_WITNESSED`, and narrowed to the IPA opening, `cipCorrect` and `plonkChecksPassed`; the rest
became `FINALIZE_XI_B_PROVED`, which is not a bit). -/
theorem minaVerify_tip_lanes_are_published_and_joined :
    ∀ col ∈ [21, 22, 23, 24, 25, 26, 27, 28, 29],
      isPiBound LightClientMinaAir.minaLcVerifyDesc col = true ∧
      isRead LightClientMinaAir.minaLcVerifyDesc col = true ∧
      isRelated LightClientMinaAir.minaLcVerifyDesc col = true ∧
      col ∉ decorativeAnchors LightClientMinaAir.minaLcVerifyDesc := by
  decide

/-- ⚑⚑ **AND THE JOIN IS TO THE PINNED PROGRAM, IN ONE CONSTRAINT — the Mina analogue of
`sol_anchor_root_shares_a_constraint_with_the_stake_rows`.** Every published tip lane co-occurs, in a
SINGLE constraint, with the `LINK_OK` carrier and with the segment program's first and last attested
lane. So the tip columns and the identity of the sub-proof they commit to are adjacent, not merely in
one component by a long walk.

⚠ The difference from Solana's is worth stating rather than letting the parallel shape imply it:
there the co-occurring columns are the INPUTS of a deployed Poseidon2 chip absorb, so the published
root is the IMAGE of the exhibited rows. Here they are a program FINGERPRINT, so what the constraint
says is *which* sub-proof these nine lanes are the commitment of — not that they are anything's
image. -/
theorem minaVerify_tip_shares_a_constraint_with_the_pinned_segment_program :
    ∀ j ∈ [21, 22, 23, 24, 25, 26, 27, 28, 29],
      LightClientMinaAir.minaLcVerifyDesc.constraints.any (fun c =>
        j ∈ relatedCols c
          && LightClientMinaAir.LINK_OK ∈ relatedCols c
          && LightClientMinaAir.LINK_VK 0 ∈ relatedCols c
          && LightClientMinaAir.LINK_VK 8 ∈ relatedCols c) = true := by
  decide

/-! ### ⚑⚑ 2026-08-05 — THE RECURSION RUNG, MEASURED HERE RATHER THAN ASSUMED.

`dregg-mina-lightclient-verify::v1` changed shape: width 30 → 49, PIs 20 → 29, constraints 50 → 69,
because `PICKLES_OK` became `PICKLES_WITNESSED` plus `WRAP_FS_PROVED` and its nine `proof_bind`
legs. The two theorems above were TRIPWIRES for exactly that kind of change and **they did not
fire** — which is a result, not a non-event, and the reason is worth stating so nobody reads the
unchanged `18` as "nothing happened":

* the rung did not bind an EXISTING decorative anchor. The eighteen state lanes are still read only
  by arity-1 range lookups and still joined to nothing;
* it added NINE NEW published values — the sub-proof commitment lanes — and every one of them lands
  JOINED, because a `proof_bind` relates its guard, its commitment and its vk column
  (`relatedCols`'s `.proofBind` arm). **Nine public inputs added, zero decorative anchors added.**

That is the honest delta, and the theorem below is what makes it a measurement. It is a NEW tripwire
in the same direction as the others: it reds if a future edit publishes the commitment without
joining it. -/

/-- ⚑⚑ **THE NINE SUB-PROOF COMMITMENT LANES ARE PUBLISHED AND JOINED.** PI-bound (so a consumer can
compare them against a sub-proof it verifies) and related (so they are not decoration). -/
theorem minaVerify_subproof_commitment_is_published_and_joined :
    ((List.range 9).all fun i =>
        isPiBound LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.SUB_PI i)
          && isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.SUB_PI i)) = true
      ∧ LightClientMinaAir.minaLcVerifyDesc.piCount = 39
      -- ⚑ 18 → 9 on 2026-08-05 (the segment bind). The PI COUNT DID NOT MOVE THEN: the tip block was
      -- already published, and what changed is that a constraint now named it.
      -- ⚑⚑ 30 → 39 on 2026-08-06 (the FINALIZE conjunction bind). This time the count DID move — the
      -- seam commits to a DIFFERENT object, the conjunction sub-proof's 160 public inputs, so nine
      -- lanes had to be added rather than re-used. The decorative count is UNCHANGED at 9 (still the
      -- anchor's nine, still joined to nothing), which is the fact worth checking: nine published
      -- lanes were added and none of them is decoration.
      ∧ (decorativeAnchors LightClientMinaAir.minaLcVerifyDesc).length = 9 := by
  refine ⟨by decide, rfl, by decide⟩

/-- ⚑⚑ **AND THE NINE FINALIZE-CONJUNCTION COMMITMENT LANES ARE PUBLISHED AND JOINED TOO** (added
2026-08-06). Same shape as the chainlink's above, and the same reason: a `proof_bind`'s `commit`
vector is what `relatedCols` returns, so these nine are named by a constraint and not merely pinned.
`FINALIZE_XI_B_PROVED` is NOT PI-bound, for the reason `WRAP_FS_PROVED` is not: a carrier a verifier
could set from outside the proof would be no carrier. -/
theorem minaVerify_conjunction_commitment_is_published_and_joined :
    ((List.range 9).all fun i =>
        isPiBound LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.CONJ_PI i)
          && isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.CONJ_PI i)) = true
      ∧ isPiBound LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.FINALIZE_XI_B_PROVED = false
      ∧ isRelated LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.FINALIZE_XI_B_PROVED = true
      ∧ ((List.range 9).all fun i =>
          isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.CONJ_VK i)) = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- ⚑ **AND THE GUARD IS IN THE SAME COMPONENT AS EVERY LANE IT GUARDS.** Nine binds, one guard —
so the recursion carrier is not a bit sitting on its own island beside nine other bits. `WRAP_FS_PROVED`
is NOT PI-bound (a carrier a verifier could set from outside the proof would be no carrier), which is
why it never appears in the decorative census at all. -/
theorem minaVerify_recursion_guard_is_joined_and_hidden :
    isPiBound LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.WRAP_FS_PROVED = false
      ∧ isRelated LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.WRAP_FS_PROVED = true
      ∧ ((List.range 9).all fun i =>
          isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.SUB_VK i)) = true := by
  refine ⟨by decide, by decide, by decide⟩

/-- ⚑ **THE ANCHOR HEIGHT IS NOW PUBLISHED** — the flip of the former
`minaVerify_anchor_height_is_pinned_to_nothing`, on the emitted bytes (2026-08-05).

`ANCHOR_H` (col 1) is PI-bound at slot `PI_ANCHOR_H` and related, so it is neither hidden nor
decorative: a consumer holding the operator's anchor can compare the height the proof used against
the height it pinned, which is `dregg_turn::executor::mina_head_verifier`'s REFUSAL 2. Before this
leg the only published consequence of `ANCHOR_H` was the SUM `BLOCK_LEN`, and a prover picked the
summands.

⚠ **This is a PUBLICATION result, NOT a connectivity one** — see
`minaVerify_anchor_height_shares_no_constraint_with_the_hash` immediately below, which is the part
that did NOT change and is the honest residual. -/
theorem minaVerify_anchor_height_is_published :
    isPiBound LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.ANCHOR_H = true ∧
    isRelated LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.ANCHOR_H = true := by
  refine ⟨by decide, by decide⟩

/-- ⚑⚑ **AND THE HEIGHT STILL SHARES NO CONSTRAINT WITH THE HASH. THIS IS THE RESIDUAL.**

`relatedCols` returns `[]` for a `piBinding` deliberately — a pin ties a column to a PUBLIC INPUT,
not to another column — so the 2026-08-05 pin above bought publication and bought **zero** edges.
IN-CIRCUIT, "the anchor" is still two unrelated prover choices: the height (col 1) and the state
hash (cols 12..20) appear in no common constraint. Nothing in this descriptor says the height is
the height OF that hash.

That join is a Mina-state lookup this descriptor does not perform, and it is not closed by anything
here. What closes the *consumer's* exposure is that both halves are refused against cell-program
state off-row; what would close the *circuit's* is a constraint that does not exist yet. Kept as a
theorem, in the affirmative, so it reds the day someone builds it — at which point the honest move
is to delete this and state the join. -/
theorem minaVerify_anchor_height_shares_no_constraint_with_the_hash :
    (∀ col ∈ [12, 13, 14, 15, 16, 17, 18, 19, 20],
      ∀ c ∈ LightClientMinaAir.minaLcVerifyDesc.constraints,
        col ∈ relatedCols c → LightClientMinaAir.ANCHOR_H ∉ relatedCols c) := by
  decide

/-- ⚑⚑ **THE MINA LINK RUNG: NO DECORATIVE ANCHORS.** All twenty PI-bound columns are joined — the
nine anchor lanes to the nine own-hash lanes by the per-lane continuity window gates, the anchor
height to the first row's height, and the segment length to the `IS_REAL` accumulator.

⚠ **TRIPWIRE IN THE OTHER DIRECTION.** This one reds if someone DISCONNECTS a lane — the shape
`broken_link_refused` exists to catch, stated here about the emitted object rather than about one
witness pair. -/
theorem minaLink_decorative_anchors :
    decorativeAnchors LightClientMinaLinkAir.minaLinkDesc = [] := by
  decide

/-- ⚑⚑⚑ **THE POSITIVE STATEMENT, AND IT IS THE ONE THIS FILE EXISTED TO BE ABLE TO MAKE.**

The header of this module says every theorem in it is *"a TRIPWIRE meant to go red"*, and names the
change that would do it: *"the in-AIR-crypto iteration (… `LINK_OK` from the Poseidon chain) is
exactly the change that puts an anchor beside another column in a gate."* That change landed on
2026-08-06 and this is what it looks like measured rather than described: the segment descriptor's
`proof_bind` names, in ONE constraint, all thirty-six columns of the row's parent, body hash, own
hash and attested program. Nine `PARENT`, nine `OWNHASH`, nine `BODYHASH`, nine `HASH_VK`, one
component.

⚠ **AND THE FILE'S STANDING CAVEAT IS NOT REPEALED BY IT.** Connectivity is CO-OCCURRENCE, not
derivation: what this measures is that the columns share a constraint. What upgrades it to
derivation is the seam's off-row half plus the sub-program's own denotation
(`LightClientMinaLinkAir.seam_derives_the_own_hash`, which takes `StateHashEngine` as a named
hypothesis). A green here is necessary and not sufficient, and saying which is the job. -/
theorem minaLink_the_seam_joins_the_preimage_to_the_image :
    ∀ col ∈ (List.range 9).flatMap (fun j => [j, 9 + j, 22 + j, 31 + j]),
      col ∈ (((LightClientMinaLinkAir.minaLinkDesc.constraints.drop 51).take 1).flatMap
        relatedCols) := by
  decide

/-- ⚑ **THE NARROWER TRIPWIRE THAT REPLACES IT — AND ITS TRIGGER IS RE-AIMED, 2026-08-07.**
`BODYHASH` is the one nonet the seam does not DERIVE: it is an ARGUMENT of the hash. The nine
body-hash columns are read and joined, and NOT PI-bound.

⚑⚑ **REPORT: THIS DID NOT FIRE WHEN THE SUB-PROOF LANDED, AND THAT IS THE FINDING.** Its docstring
said *"it reds the day `state_body_hash` acquires its own sub-proof, which is the next rung."* That
rung landed (`Circuit.Emit.MinaStateBodyHashChain` — 25 links of the deployed
`dregg-pasta-fp-chainlink::v1` from the pinned `MinaProtoStateBody` salt over the block's packed
`Body.to_input`, proved and folded) and **every literal here is unchanged**, because the derivation
is a SIBLING CHAIN welded executor-side rather than a constraint in this descriptor. The tripwire was
watching the right column and the wrong event.

⚑ **RE-AIMED, and the new trigger is the one that matters:** `isPiBound = false` is now the SPECIFIC
gap, not an incidental observation. A `proofBind`'s `commit`/`vk` name PUBLISHED values and a
recursion fold reads `air_public_targets`, so **an unpublished `BODYHASH` cannot be `cb.connect`ed to
the body-hash chain's root at all** — the executor comparison is not a choice, it is what an
unpublished column forces. This reds the day `BODYHASH` is PI-bound, which is exactly the flag day
`LightClientMinaLinkAir`'s §"WHAT THIS BREAKS" costs (piCount 20 → 37, both Mina descriptors re-VK).

⚠ And what would STILL be owed after that: publishing the nonet buys a weld to a chain, not a weld
to a BLOCK. The chain's absorbed stream is named by its fold accumulator, and tying THAT to the
block whose `PARENT`/`HEIGHT` this row carries is a comparison the node makes from wire bytes. -/
theorem minaLink_body_hash_is_joined_but_not_published :
    ∀ col ∈ [22, 23, 24, 25, 26, 27, 28, 29, 30],
      isRead LightClientMinaLinkAir.minaLinkDesc col = true ∧
      isRelated LightClientMinaLinkAir.minaLinkDesc col = true ∧
      isPiBound LightClientMinaLinkAir.minaLinkDesc col = false := by
  decide

/-- ⚑ **THE POSITIVE HALF, STATED SO THE GAIN IS A TERM.** The nine body-hash columns are not
inert: they are named by the state-hash seam's `proof_bind` — the SAME constraint that names the
parent, the own hash and the attested program — so what is missing is PUBLICATION, not membership in
the component. Without this the theorem above reads as "BODYHASH is unconnected", which is false and
would misdirect the repair. -/
theorem minaLink_body_hash_is_named_by_the_seam :
    ∀ col ∈ [22, 23, 24, 25, 26, 27, 28, 29, 30],
      col ∈ (((LightClientMinaLinkAir.minaLinkDesc.constraints.drop 51).take 1).flatMap
        relatedCols) := by
  decide

/-- …and the count is exactly the twenty the descriptor declares, so the `[]` above is a statement
about twenty joined columns and not about an empty PI set. -/
theorem minaLink_has_twenty_pi_bound_columns :
    ((List.range LightClientMinaLinkAir.minaLinkDesc.traceWidth).filter
      fun col => isPiBound LightClientMinaLinkAir.minaLinkDesc col).length = 20 ∧
    LightClientMinaLinkAir.minaLinkDesc.piCount = 20 := by
  decide

/-- ⚑⚑⚑ **THE SOLANA STAKE-TABLE FOLD: NO DECORATIVE ANCHORS — AND, FOR THE FIRST TIME IN THIS
CENSUS, THE PUBLISHED VALUES ARE DERIVED RATHER THAN CHAINED.**

`dregg-solana-stake-table-fold::v1` publishes twelve values on its LAST row: the eight lanes of the
table's Poseidon2 commitment and the four limbs of the `u64` active-stake denominator. All twelve are
joined, and the component they sit in is the WHOLE TRACE.

⚠ Read the difference from `minaLink_decorative_anchors` carefully, because it is the whole point of
this rung. That descriptor earns its `[]` by chaining WITNESSED lane values with equality gates —
this file's own caveat says so: *"its evidence is numbers the prover chose."* Here the joining
constraints are two arity-16 chip lookups on the deployed Poseidon2 bus, whose eight output columns
are FORCED by `DescriptorIR2.chip_lookup_sound_N` against the chip table the genuine permutation
serves. The published root is not equal to a witness; it is the image of one. -/
theorem solStakeFold_decorative_anchors :
    decorativeAnchors LightClientSolStakeFoldAir.solStakeFoldDesc = [] := by
  decide

/-- …and the `[]` is a statement about TWELVE joined columns, not about an empty PI set. -/
theorem solStakeFold_has_twelve_pi_bound_columns :
    ((List.range LightClientSolStakeFoldAir.solStakeFoldDesc.traceWidth).filter
      fun col => isPiBound LightClientSolStakeFoldAir.solStakeFoldDesc col).length = 12 ∧
    LightClientSolStakeFoldAir.solStakeFoldDesc.piCount = 12 := by decide

/-- ⚑⚑ **THE STATEMENT NO OTHER DESCRIPTOR IN THIS CENSUS CAN MAKE: the published anchor and the
evidence are in ONE constraint together.**

Every published root lane co-occurs, in a SINGLE constraint, with a pubkey lane and with a stake
limb — the second chip absorb's tuple is `[16, MID₀…MID₇, VOTER₈, STAKE₀…STAKE₃, 0, 0, 0,
ROOT_OUT₀…ROOT_OUT₇]`, so the root columns and the row's own evidence columns are adjacent, not
merely in the same component by a long walk. And every published denominator limb co-occurs with the
row's stake limbs through the accumulator window gates.

⚠ Connectivity is still co-occurrence, not derivation — this file's standing caveat, and it binds
here too. What upgrades this from co-occurrence to derivation is not measured here: it is
`chip_lookup_sound_N` at the emitted tuple, and `LightClientSolStakeFoldAir.FoldScheme`'s
`tableRoot_binds_or_collides` / `same_tally_moves_the_root` over the fold the tuples compute. -/
theorem solStakeFold_root_shares_a_constraint_with_the_stake_rows :
    ∀ j ∈ [0, 1, 2, 3, 4, 5, 6, 7],
      LightClientSolStakeFoldAir.solStakeFoldDesc.constraints.any (fun c =>
        LightClientSolStakeFoldAir.ROOT_OUT j ∈ relatedCols c
          && LightClientSolStakeFoldAir.VOTER 8 ∈ relatedCols c
          && LightClientSolStakeFoldAir.STAKE 0 ∈ relatedCols c) = true := by
  decide

/-- …and the DENOMINATOR limbs are joined to the per-row stake limbs, so the number the sibling
verify rung's quorum divides by is the number these rows add up. -/
theorem solStakeFold_denominator_shares_a_constraint_with_the_row_stakes :
    ∀ i ∈ [0, 1, 2, 3],
      LightClientSolStakeFoldAir.solStakeFoldDesc.constraints.any (fun c =>
        LightClientSolStakeFoldAir.ACC i ∈ relatedCols c
          && LightClientSolStakeFoldAir.STAKE i ∈ relatedCols c) = true := by
  decide

/-! ## §3 — the census, as one number. -/

/-- ⚑ **THE ANSWER TO "HOW MANY OF OUR LIGHT CLIENTS RELATE THEIR CLAIMED BLOCK TO THE EVIDENCE THEY
CHECK?"** Fifty-three decorative anchors across the five VERIFY descriptors; zero across the LINK rung
and the FOLD rung. **Three of seven now, and two of them are VERIFY descriptors.**

⚑ **THE SEQUENCE, BECAUSE A SINGLE NUMBER IS A BAD SUMMARY AND THIS FILE HAS SAID SO THREE TIMES.**
`63 → 71 → 62 → 53`. The rise to 71 was Solana's `ANCHOR_ROOT` widening from ONE 31-bit column standing
for a 256-bit SHA-256 root to nine radix-`2^31` limbs: eight more published columns, none of them read.
The fall to 62 is those nine limbs being DELETED and replaced by the stake-table fold's eight `.last`
output lanes, which are in the same component as the rows they commit to. **Column count moved the
same direction for "we widened a root to bind it properly" and for "we published something and joined
it to nothing"; it moved the RIGHT direction only when the root became derived.** Anyone tightening
this gate should count BITS-OF-PUBLIC-STATEMENT-UNBOUND, or the decorative SHARE, not columns.

⚑ **AND THE FALL TO 53 IS THE FIRST ONE THIS METRIC MEASURES HONESTLY, WHICH IS WHY IT IS WORTH THE
SENTENCE.** Mina's nine `TIP_STATE` lanes joined a `proofBind` and **no public input was added or
removed** — the descriptor's statement is the same thirty values it was this morning, and nine of them
stopped being carried by nothing. Denominator fixed, numerator down: the one shape where the column
count and the meaning cannot disagree. Contrast the `62 → 71` step, where the count rose *because* a
root was being bound properly.

⚠ Read `minaLink_decorative_anchors`' own caveat before reading Solana's `[69 … 78]` as SOUND. Zero
decorative anchors is the floor, not the ceiling, and Solana is not at zero: its bank root and slot
are still carried by no gate, its `ED_OK` is still a witnessed carrier and its numerator is still a
witnessed projection. What changed is that the DENOMINATOR and the TABLE it is a total of are now
derived from rows the same proof commits to. -/
theorem the_five_verify_descriptors_carry_fifty_three_decorative_anchors :
    (decorativeAnchors LightClientEthAir.ethLcVerifyDesc).length
      + (decorativeAnchors LightClientTendermintAir.tmLcVerifyDesc).length
      + (decorativeAnchors LightClientMidnightAir.midLcVerifyDesc).length
      + (decorativeAnchors LightClientSolanaAir.solLcVerifyDesc).length
      + (decorativeAnchors LightClientMinaAir.minaLcVerifyDesc).length = 53 ∧
    (decorativeAnchors LightClientMinaLinkAir.minaLinkDesc).length = 0 := by
  decide

/-! ## §4 — axiom hygiene. Named theorems, `#assert_axioms`, no `#guard`. -/

#assert_axioms eth_decorative_anchors
#assert_axioms eth_anchors_are_unread
#assert_axioms tm_decorative_anchors
#assert_axioms tm_anchors_are_unread
#assert_axioms tm_chain_id_domain_is_not_the_chain_id_gate
#assert_axioms mid_decorative_anchors
#assert_axioms mid_anchors_are_unread
#assert_axioms mid_round_and_era_bits_are_not_joined_to_the_published_round_and_era
#assert_axioms sol_decorative_anchors
#assert_axioms sol_anchors_are_unread
#assert_axioms sol_pinned_denominator_is_not_decorative
#assert_axioms sol_published_anchor_root_is_not_decorative
#assert_axioms sol_anchor_root_shares_a_constraint_with_the_stake_rows
#assert_axioms minaVerify_decorative_anchors
#assert_axioms minaVerify_subproof_commitment_is_published_and_joined
#assert_axioms minaVerify_recursion_guard_is_joined_and_hidden
#assert_axioms minaVerify_anchor_lanes_are_read_but_never_joined
#assert_axioms minaVerify_tip_lanes_are_published_and_joined
#assert_axioms minaVerify_tip_shares_a_constraint_with_the_pinned_segment_program
#assert_axioms minaVerify_anchor_height_is_published
#assert_axioms minaVerify_anchor_height_shares_no_constraint_with_the_hash
#assert_axioms minaLink_decorative_anchors
#assert_axioms minaLink_the_seam_joins_the_preimage_to_the_image
#assert_axioms minaLink_body_hash_is_joined_but_not_published
#assert_axioms minaLink_body_hash_is_named_by_the_seam
#assert_axioms minaLink_has_twenty_pi_bound_columns
#assert_axioms solStakeFold_decorative_anchors
#assert_axioms solStakeFold_has_twelve_pi_bound_columns
#assert_axioms solStakeFold_root_shares_a_constraint_with_the_stake_rows
#assert_axioms solStakeFold_denominator_shares_a_constraint_with_the_row_stakes
#assert_axioms the_five_verify_descriptors_carry_fifty_three_decorative_anchors

end Dregg2.Circuit.Emit.LightClientAnchorConnectivity
