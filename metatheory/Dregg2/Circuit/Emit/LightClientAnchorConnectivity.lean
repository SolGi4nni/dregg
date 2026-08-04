/-
# `Dregg2.Circuit.Emit.LightClientAnchorConnectivity` — WHICH light clients relate their claimed block
to the evidence they check. Measured on all six served descriptors, as named theorems.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this file authors NO AIR. It reads six already-emitted
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

Six served descriptors. **One of them relates its published values to anything: the Mina LINK rung.**

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

* **`dregg-solana-lightclient-verify::v1`** — `{0}{1}{2}{3} / {4..29} / {30}…{40}`. ELEVEN of eleven
  inert and UNREAD. `LightClientSolanaAir` §6b states this in-file; it is restated here so the census
  is one object. *The prover exhibited a `(total, rooted)` pair clearing `total ≥ 1` and
  `3·rooted > 2·total`, set four bits to 1, and separately exhibited eleven public values.*

* **`dregg-mina-lightclient-verify::v1`** — `{0..7}{11} / {8} / {9} / {10} / {12}…{29}`. EIGHTEEN of
  twenty inert; the two that are not are `BLOCK_LEN` (col 11, PI 18) and `REQ_DEPTH` (col 4, PI 19),
  both inside the height/depth component. *The prover exhibited a segment length, an anchor height, a
  submission height and three range-checked slacks in an additive relation, published the derived
  block length and the required depth, set three bits to 1, and separately exhibited eighteen lane
  values each bounded to 29 or 22 bits.* ⚑ Two corrections the measurement forces:
  - the anchor HEIGHT (`ANCHOR_H`, col 1) is a FREE WITNESS — not PI-bound, not range-looked-up, and
    **pinned to no constant**; `LightClientMinaAir:274` calls it "the pinned weak-subjectivity
    anchor's blockchain length" and no constraint pins it;
  - the anchor STATE HASH (cols 12..20) and the anchor HEIGHT (col 1) share no constraint at all, so
    "the published height is the pinned anchor plus the exhibited segment" is a relation among three
    prover-chosen numbers.
  The lane bounds are real and strictly stronger than canonicality (`8·29 + 22 = 254`,
  `2^254 < p_Pasta`) — but they bound each lane of a value tied to nothing.

* **`dregg-mina-lightclient-link::v1`** — `{0}{9} / {1}{10} / … / {8}{17} / {18}{21} / {19..20}`.
  **ZERO decorative anchors: all twenty PI-bound columns are related.** *The prover exhibited a
  sequence of rows in which each row's nine-lane `OWNHASH` equals the next row's nine-lane `PARENT`,
  the heights tick by one from a first-row anchor height, a boolean `IS_REAL` is monotone and its
  running sum is published as the segment length — and the anchor and tip it publishes are the two
  ends of that chain.*
  ⚠ **AND THAT IS STILL NOT A BINDING TO MINA.** `OWNHASH` is a free witness: nothing forces it to be
  `Poseidon(stateRow)` (`LinkHashResidual`, `LightClientMinaLinkAir` §6, priced at ~5·10⁵ BabyBear
  constraints per block hash). Every lane pair is its own island — lane `j` chains to lane `j` and
  never crosses. **Connectivity is co-occurrence, not derivation.** This descriptor relates its
  publications to its evidence; its evidence is numbers the prover chose.

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

set_option autoImplicit false
set_option maxHeartbeats 1600000

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
  | .memOp m                 => nub ((exprCols m.guard) ++ (exprCols m.addr) ++ (exprCols m.value) ++
                                     (exprCols m.prevValue) ++ (exprCols m.prevSerial))
  | .umemOp m                => nub ((exprCols m.guard) ++ (exprCols m.key) ++ (exprCols m.present) ++
                                     (exprCols m.value) ++ (exprCols m.prevPresent) ++
                                     (exprCols m.prevValue) ++ (exprCols m.prevSerial))
  | .mapOp m                 => nub ((exprCols m.guard) ++ (exprCols m.key) ++ (exprCols m.value) ++
                                     ((List.ofFn m.root).flatMap exprCols) ++
                                     ((List.ofFn m.newRoot).flatMap exprCols))
  | .proofBind m             => nub ((exprCols m.guard) ++ (exprCols m.commit) ++ (exprCols m.vk))

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

/-- ⚑ **SOLANA: all eleven published anchors are decorative.** Columns 30..40 — `ANCHOR_ROOT`, the
nine `BANK_ROOT` limbs, `SLOT_COL`. This restates `LightClientSolanaAir.sol_public_anchors_are_-
arithmetically_inert` through the uniform predicate, so the six-chain census is one object and one
definition rather than six local ones. -/
theorem sol_decorative_anchors :
    decorativeAnchors LightClientSolanaAir.solLcVerifyDesc = [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40] := by
  decide

/-- …and unread. -/
theorem sol_anchors_are_unread :
    ∀ col ∈ [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40],
      isRead LightClientSolanaAir.solLcVerifyDesc col = false := by
  decide

/-- ⚑ **MINA VERIFY: eighteen of twenty published values are decorative.** Columns 12..29 — the nine
`ANCHOR_STATE` lanes and the nine `TIP_STATE` lanes. The two that are NOT are `BLOCK_LEN` (col 11) and
`REQ_DEPTH` (col 4), which sit in the height/depth component. -/
theorem minaVerify_decorative_anchors :
    decorativeAnchors LightClientMinaAir.minaLcVerifyDesc
      = [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29] := by
  decide

/-- ⚑ **AND THIS IS THE CASE `constraintCols` ALONE WOULD MISS.** The eighteen lane columns ARE read —
each by an arity-1 range lookup at 29 or 22 bits — and joined to nothing. A width bound is a fact
about a value's SHAPE; it is not a tie to the evidence, and a census that counted "appears in a
lookup tuple" as bound would have scored these eighteen as connected. -/
theorem minaVerify_state_lanes_are_read_but_never_joined :
    ∀ col ∈ [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
      isRead LightClientMinaAir.minaLcVerifyDesc col = true ∧
      isRelated LightClientMinaAir.minaLcVerifyDesc col = false := by
  decide

/-- ⚑ **THE ANCHOR HEIGHT AND THE ANCHOR HASH SHARE NO CONSTRAINT**, and the anchor height is pinned
by nothing. `ANCHOR_H` (col 1) is joined only to the height arithmetic; it is not PI-bound, carries no
range lookup, and no gate equates it to a literal. So "the published height is the PINNED anchor plus
the exhibited segment" (`LightClientMinaAir:274`, and the campaign brief) is a relation among three
numbers the prover chose. -/
theorem minaVerify_anchor_height_is_pinned_to_nothing :
    isPiBound LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.ANCHOR_H = false ∧
    isRelated LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.ANCHOR_H = true ∧
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

/-- …and the count is exactly the twenty the descriptor declares, so the `[]` above is a statement
about twenty joined columns and not about an empty PI set. -/
theorem minaLink_has_twenty_pi_bound_columns :
    ((List.range LightClientMinaLinkAir.minaLinkDesc.traceWidth).filter
      fun col => isPiBound LightClientMinaLinkAir.minaLinkDesc col).length = 20 ∧
    LightClientMinaLinkAir.minaLinkDesc.piCount = 20 := by
  decide

/-! ## §3 — the census, as one number. -/

/-- ⚑ **THE ANSWER TO "HOW MANY OF OUR LIGHT CLIENTS RELATE THEIR CLAIMED BLOCK TO THE EVIDENCE THEY
CHECK?"** Sixty-three decorative anchors across the five VERIFY descriptors; zero across the LINK
rung. One of six.

⚠ Read `minaLink_decorative_anchors`' own caveat before reading this as one-in-six SOUND: the link
rung joins its publications to a chain of witnessed lane values, and nothing forces those values to be
the Poseidon hashes of Mina blocks. Zero decorative anchors is the floor, not the ceiling. -/
theorem the_five_verify_descriptors_carry_sixty_three_decorative_anchors :
    (decorativeAnchors LightClientEthAir.ethLcVerifyDesc).length
      + (decorativeAnchors LightClientTendermintAir.tmLcVerifyDesc).length
      + (decorativeAnchors LightClientMidnightAir.midLcVerifyDesc).length
      + (decorativeAnchors LightClientSolanaAir.solLcVerifyDesc).length
      + (decorativeAnchors LightClientMinaAir.minaLcVerifyDesc).length = 63 ∧
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
#assert_axioms minaVerify_decorative_anchors
#assert_axioms minaVerify_state_lanes_are_read_but_never_joined
#assert_axioms minaVerify_anchor_height_is_pinned_to_nothing
#assert_axioms minaLink_decorative_anchors
#assert_axioms minaLink_has_twenty_pi_bound_columns
#assert_axioms the_five_verify_descriptors_carry_sixty_three_decorative_anchors

end Dregg2.Circuit.Emit.LightClientAnchorConnectivity
