/-
# `Dregg2.Circuit.Emit.LightClientMinaLinkAir` — the Mina exhibited SEGMENT, multi-row, compiled.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this is a Lean-authored AIR. `minaLinkDesc` is
`EffectLower.lowerAir` applied to the `EffectAir` source `minaLinkAir` (§3). There is **no
hand-written `VmConstraint2` in this file.** Rust only reads the emitted bytes.

## What this rung is, and — first — what it is NOT

`LightClientMinaAir` publishes three carriers. `CANON_OK` stopped being a witness on 2026-08-03.
`LINK_OK` and `PICKLES_OK` did not. This file takes the FIRST HALF of `LINK_OK` and no more, and the
split is the whole point of the file, so it is stated before the construction:

`LightClientMina.chainLinked` (`Bridge/LightClientMina.lean:202`) is three conjuncts per block:

    (i)   h.parent  =  prev                       -- the running state hash IS this block's parent
    (ii)  h.height  =  ph + 1                     -- height contiguity
    (iii) prev'     :=  blockHash L h             -- and the running value is Poseidon(stateRow h)

⚑ **(i) and (ii) are equality and addition. (iii) is Mina's Poseidon over Pasta `Fp`.** This file
derives (i) and (ii) — over nine-lane `Fp` columns, multi-row, one row per exhibited block — and
derives the SEGMENT LENGTH besides. It does **not** derive (iii), and nothing here pretends to:
`OWNHASH` is a witnessed nonet, and what binds it to a real Mina block stays `PICKLES_OK`.

So the honest name for what is derived is the segment's **SHAPE**, not `LINK_OK`. The predicate is
called `linkShapeAccepts`; the residual is called `LinkHashResidual` and is a NAMED `Prop` (§6), not
a sentence in a comment.

## ⚑ Why (iii) is a wall and not a lane — the decision, stated as the brief asks

Mina's protocol-state hash is Poseidon over Pasta `Fp` (`p ≈ 2^254.0`), and the dregg prover is over
BabyBear (`P = 2013265921 ≈ 2^30.9`). A Pasta multiplication at BabyBear is non-native: a limb
product must not wrap, so `2b + log₂ k < 30.9`, which at `k = ⌈255/b⌉` forces `b ≈ 13`, `k ≈ 20`, and
schoolbook `k² = 400` limb products plus a reduction and ~40 range-checked carry rungs — **≈10³
BabyBear constraints per Pasta multiplication** (`LightClientMinaAir` §1b, measured off this tree's
own `KimchiVerify`/`PastaPoseidon`). One Poseidon-over-Pasta permutation is 55 full rounds at width 3
with an `x^7` S-box: ~500 Pasta multiplications, so **~5·10⁵ BabyBear constraints per block hash**,
and a Samasika-depth segment (`k = 290` on mainnet) is ~1.5·10⁸ constraints for the linkage hash
alone. That is the same construction §1b already called wrong: the reachable shape is RECURSION, not
a bigger circuit.

⚑ **AND THE GADGET THAT WOULD DO IT IS NOT SOUND AS EMITTED TODAY.** `Dregg2.PastaMsmBound`'s limb
multiply is not reachable from any emitted descriptor, `pastaLimbRange` is emitted nowhere, and the
carry columns are not boolean-pinned in any emitted object. Building (iii) on it would inherit all of
that. **So this file does (i) + (ii) and NAMES (iii) as the wall.** It does not ship (iii) dressed as
(i): `minaLinkDesc` contains no multiplication of two witness columns anywhere (`minaLink_has_no_witness_product`, §3a).

## ⚑ What `dregg-turn-chain-binding-v2` actually contributed — the transfer, measured

`EffectVmEmitTurnChainBinding` is a multi-row binding descriptor with a per-row leaf and a recursion
tree, and its shape transfers ALMOST WHOLE. Site by site
(`Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean`):

    turn-chain site                          this file                              Pasta mul?
    ───────────────────────────────────────────────────────────────────────────────────────────
    rootContinuity     (:100)   new_root[i]=old_root[i+1]   OWNHASH[i]=PARENT[i+1] ×9   NO
    firstOldRootBind   (:106)   old_root[0]=pi              PARENT[0]=PI_ANCHOR    ×9   NO
    lastNewRootBind    (:110)   new_root[last]=pi           OWNHASH[last]=PI_TIP   ×9   NO
    firstIdxZero       (:137)   idx[0]=0                    HEIGHT[0]=ANCHOR_H+1        NO
    idxIncrement       (:141)   idx[i+1]=idx[i]+1           HEIGHT[i+1]=HEIGHT[i]+1     NO
    isRealBoolean      (:150)   is_real ∈ {0,1}             same                        NO
    realMonotone       (:158)   real rows are a prefix      same                        NO
    firstRealCount     (:166)   real_count[0]=is_real[0]    same                        NO
    realCountAccum     (:171)   real_count accumulates      same                        NO
    lastRealCountBind  (:180)   real_count[last]=pi         REAL_COUNT[last]=PI_SEG_LEN NO
    perRowHash         (:129)   acc=Poseidon2(acc,…)        ⚠ NOT TRANSFERRED — see below
    ───────────────────────────────────────────────────────────────────────────────────────────

⚑ **The finding, and it corrects the survey that opened this lane.** The survey said "swap 'turn' for
'Mina block' and it is an emit-and-wire job." That is RIGHT about the chaining and it buys less than
it sounds, because **`dregg-turn-chain-binding-v2` never computes the values it chains.** Its
`old_root`/`new_root` are field elements chained by EQUALITY (`rootContinuity` is `loc c1 − nxt c0`,
one subtraction); its one hash site is a *native BabyBear* Poseidon2 accumulator over the row
(`acc_out = Poseidon2([acc_in, old_root, new_root, idx])`), which digests the chain but does not
produce it. So turn-chain-binding transfers COMPLETELY for the equality/counting half and contributes
**nothing at all** to the hash half — it has no hash half to contribute. The blocker was never that
the descriptor was single-row; single-row was the blocker for (i)/(ii), and this file removes it.
(iii) was never in the donor.

`perRowHash` is deliberately not transferred: a native accumulator here would digest the chain into
one felt, which is a *convenience* for a recursion seam and not a binding, and this file has no
recursion seam to feed yet. Adding it would be a column that computes something nobody reads.

## ⚑ THE TOOTH THIS ACTUALLY CLOSES: `SEG_LEN` stops being a free felt

`LightClientMinaAir`'s §"THE TOOTH" says the published `blockchain_length` is DERIVED, not witnessed:

    G1   BLOCK_LEN = ANCHOR_H + SEG_LEN

and concludes *"a prover that exhibits `n` blocks above the pinned anchor can publish exactly
`anchorH + n`."* ⚠ **That conclusion does not hold of that descriptor, and the reason is structural:
`SEG_LEN` is column 0, a free witness, and the descriptor is SINGLE-ROW — it has no exhibited
blocks.** The only thing constraining `SEG_LEN` there is `segSlackC` (`SEG_SLACK + 1 = SEG_LEN`) with
`SEG_SLACK` ranged into `[0, 2^24)`, so `SEG_LEN` is free in `[1, 2^24]` and `BLOCK_LEN` with it.
`minaLcAir_no_forgery` is honest about this in the only place it can be — `hsl : a SEG_LEN =
u.blocks.length` is a HYPOTHESIS, discharged by the witness generator, not by a gate. The docblock's
sentence is stronger than the theorem beneath it.

Here `SEG_LEN` is `REAL_COUNT` on the last row (`lastRealCountBind`'s analog), and `REAL_COUNT`
accumulates `IS_REAL` across rows that are `0/1`-pinned and monotone. A prover claiming a
290-deep segment must commit a trace carrying 290 real rows, each with nine canonical `PARENT` lanes
and nine canonical `OWNHASH` lanes that chain into its neighbour and a height that ticks.
`link_seg_len_counts_the_real_rows` is that as a theorem. **That is the depth evidence
`LightClientMina.mina_depth_is_witnessed` claims and the single-row descriptor could not deliver.**

## ⚑ THE COUPLING: the canonicality rung is what makes this linkage EXACT

An emitted gate forces its body `≡ 0 [ZMOD P]`, not `= 0`. So `OWNHASH[i] ≡ PARENT[i+1]` alone
admits a `+P` alias per lane — nine independent aliasing lanes, one addition each. The linkage is an
EXACT equality only because every lane is range-gated below `2^29 < P` by the same `.limbs` /
narrow-lookup gadget `LightClientMinaAir` §1a landed, which this file IMPORTS rather than copies
(`laneCanon`, `stateValue`, `mina_lane_canon_forces_canonical`). `link_lane_equality_is_exact` is the
statement; `linkAccepts_forces_exact_lane_chain` is where it is used. **Two rungs, one gadget.**

## Layout — one row per exhibited block

    col 0..8    PARENT[j]    the block's `previousStateHash`, nine base-`2^29` `Faithful9` lanes
    col 9..17   OWNHASH[j]   the block's OWN protocol-state hash, nine lanes.  ⚠ WITNESSED — see §6
    col 18      HEIGHT       `blockchainLength`
    col 19      IS_REAL      1 on an exhibited block, 0 on padding; real rows are a PREFIX
    col 20      REAL_COUNT   cumulative `IS_REAL`
    col 21      ANCHOR_H     the pinned anchor's height (read on the first row only)

    PI 0..8     PI_ANCHOR[j] the operator-pinned weak-subjectivity anchor state hash
    PI 9..17    PI_TIP[j]    the verified head's state hash
    PI 18       PI_ANCHOR_H  the pinned anchor's height
    PI 19       PI_SEG_LEN   ⚑ the number of EXHIBITED blocks — now `REAL_COUNT` on the last row

Widths: lanes 0..7 at **29** bits (the last wrap-free width at BabyBear,
`RangeFieldContainment.wrap_free_iff_le_29`) and lane 8 at **22**, so `8·29 + 22 = 254` and
`2^254 < p_Pasta` exactly as in the sibling rung. Nothing here declares a width ≥ 30; the compiler
refuses one structurally (`LimbsLeg.mainRailOk`).

## Both polarities, on the emitted object

* ACCEPT — `honest_segment_accepted`: a three-block segment on the REAL devnet genesis anchor,
  chaining to a real tip, heights contiguous, `PI_SEG_LEN = 3`.
* REFUSE — `broken_link_refused`: the SAME segment with block 2's `PARENT` lane 0 bumped by one.
  Every canonicality lookup still passes (it is a canonical lane), every height still ticks, every
  carrier bit is whatever the prover likes — and the descriptor refuses it, because
  `OWNHASH[1] ≠ PARENT[2]`. ⚑ This is the forgery `LightClientMinaAir`'s witnessed `LINK_OK = 1`
  waves through, exhibited as a row pair rather than asserted.
  `broken_link_old_admits_new_rejects` states the pair.
* REFUSE — `short_segment_refused`: `PI_SEG_LEN` claimed 290 against three exhibited real rows.
  The free-depth liar.

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

**NEW descriptor** `dregg-mina-lightclient-link::v1`, width 22, 20 PIs, 53 constraints, three
declared tables (`range_w29` at wire id 98, `range_w22` at wire id 91 — SHARED with
`dregg-mina-lightclient-verify::v1`, which already declares both). **Emit**
`circuit/descriptors/by-name/dregg-mina-lightclient-link-v1.json` and **mint a VK** for it. Nothing
existing changes shape: `dregg-mina-lightclient-verify::v1` is untouched, so no VK rotates and
nothing re-genesises. ⚠ `circuit/descriptors/PROVENANCE.json` is already UNSTAMPED from the
2026-08-03 flag day and `check-descriptor-drift.sh` is already RED; this adds a row to that ledger
and the stamp remains the operator's ceremony.

## Scope — do NOT overclaim

⚠ This does **not** make the Mina light client's linkage verified. What a STARK over this descriptor
proves is: *there exists a sequence of `PI_SEG_LEN` canonical-`Fp` `(parent, ownHash)` pairs, running
from `PI_ANCHOR` to `PI_TIP`, with contiguous heights.* Whether each `ownHash` is the Poseidon of its
block's state row is `LinkHashResidual` and is NOT proved — a prover free to choose `OWNHASH` can
fabricate a chain of any length. What makes a row a real block is `PICKLES_OK`, still a witness.
⚠ And fork choice is still not here (`LightClientMinaGate`'s unchanged scope note).
-/
import Dregg2.Circuit.Emit.LightClientMinaAir

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Dregg2.Circuit.Emit.LightClientMinaLinkAir

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg PiPinLeg LimbsLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.LimbTally (limbValue LimbsInRange)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.LightClientMinaAir
  (MINA_LANE_BITS MINA_TOP_LANE_BITS minaRangeTid minaLaneTable minaTopLaneTable STATE_LIMBS
   laneCanon stateValue mina_lane_canon_forces_canonical laneCanon_value_bounds)
open Dregg2.Bridge.LightClientMina

/-! ## §1 — the column layout (ONE ROW PER EXHIBITED BLOCK) and the PI slots. -/

/-- **`PARENT j`** — lane `j` of this block's `previousStateHash`. Columns 0..8. -/
def PARENT (j : Nat) : Nat := j

/-- **`OWNHASH j`** — lane `j` of this block's OWN protocol-state hash. Columns 9..17.
⚠ WITNESSED. Nothing in this descriptor forces it to be `Poseidon(stateRow)`; that is
`LinkHashResidual` (§6) and it is the Pasta multiply. -/
def OWNHASH (j : Nat) : Nat := STATE_LIMBS + j

/-- **`HEIGHT`** — this block's `blockchainLength`. -/
def HEIGHT : Nat := 2 * STATE_LIMBS

/-- **`IS_REAL`** — 1 on an exhibited block, 0 on padding. Boolean-pinned on EVERY row and monotone
across transitions, so the real rows are a PREFIX. -/
def IS_REAL : Nat := 2 * STATE_LIMBS + 1

/-- **`REAL_COUNT`** — the cumulative count of real rows. ⚑ Its LAST-row value is `PI_SEG_LEN`, which
is what stops the segment length being a free felt. -/
def REAL_COUNT : Nat := 2 * STATE_LIMBS + 2

/-- **`ANCHOR_H`** — the pinned anchor's blockchain length. Read on the FIRST row only (the
first-row height gate and the first-row PI pin); unconstrained elsewhere, deliberately. -/
def ANCHOR_H : Nat := 2 * STATE_LIMBS + 3

/-- Main-trace width: two nine-lane hashes + height + the two real-row columns + the anchor height. -/
def MINA_LINK_WIDTH : Nat := 2 * STATE_LIMBS + 4

/-- PI slot of anchor-state lane `j` (slots 0..8). -/
def PI_ANCHOR (j : Nat) : Nat := j
/-- PI slot of tip-state lane `j` (slots 9..17). -/
def PI_TIP (j : Nat) : Nat := STATE_LIMBS + j
/-- PI slot 18: the pinned anchor's height. -/
def PI_ANCHOR_H : Nat := 2 * STATE_LIMBS
/-- ⚑ PI slot 19: the number of EXHIBITED blocks, as counted by the trace. -/
def PI_SEG_LEN : Nat := 2 * STATE_LIMBS + 1
/-- Number of public inputs. -/
def MINA_LINK_PI_COUNT : Nat := 2 * STATE_LIMBS + 2

/-- The eight LOW lane columns of the block's parent hash. -/
def parentLowLanes : List Nat :=
  [PARENT 0, PARENT 1, PARENT 2, PARENT 3, PARENT 4, PARENT 5, PARENT 6, PARENT 7]

/-- The eight LOW lane columns of the block's own state hash. -/
def ownHashLowLanes : List Nat :=
  [OWNHASH 0, OWNHASH 1, OWNHASH 2, OWNHASH 3, OWNHASH 4, OWNHASH 5, OWNHASH 6, OWNHASH 7]

/-- The `Fp` element a row's PARENT nonet denotes. -/
def parentValue (a : Assignment) : ℤ := stateValue a parentLowLanes (PARENT 8)

/-- The `Fp` element a row's OWNHASH nonet denotes. -/
def ownHashValue (a : Assignment) : ℤ := stateValue a ownHashLowLanes (OWNHASH 8)

/-! ## §2 — the SOURCE legs, in the framework's own algebra.

⚑ Every inter-row law is a `WindowLeg` at `.transition` — the ONE `RowSel` where `nxt` is the genuine
successor rather than the wrap row (`EffectAirIR.WindowLeg.mainRailOk`). The two first-row fixes are
`.first` and read only `loc`; the boolean pin is `.all`. Nothing below is a `VmConstraint2`. -/

open WindowExpr (loc nxt)

/-- **Lane continuity** — `OWNHASH[i] = PARENT[i+1]`, one leg per lane. This is
`EffectVmEmitTurnChainBinding.rootContinuity` at nine lanes instead of one felt. -/
def laneContinuity (j : Nat) : AirLeg :=
  .window ⟨RowSel.transition,
    .add (loc (OWNHASH j)) (.mul (.const (-1)) (nxt (PARENT j)))⟩

/-- **Height contiguity** — `HEIGHT[i+1] = HEIGHT[i] + 1` (`idxIncrement`). -/
def heightIncrement : AirLeg :=
  .window ⟨RowSel.transition,
    .add (nxt HEIGHT) (.add (.mul (.const (-1)) (loc HEIGHT)) (.const (-1)))⟩

/-- **The first block sits one above the pinned anchor** — `HEIGHT[0] = ANCHOR_H + 1`
(`firstIdxZero`'s analog; row-local, so `.first` is expressible). -/
def firstHeight : AirLeg :=
  .window ⟨RowSel.first,
    .add (loc HEIGHT) (.add (.mul (.const (-1)) (loc ANCHOR_H)) (.const (-1)))⟩

/-- **`IS_REAL` is boolean on EVERY row.** ⚑ `.all`, not `.transition`: a transition-scoped boolean
pin is vacuous on the last row, which is where a padding row would hide. -/
def isRealBoolean : AirLeg :=
  .window ⟨RowSel.all, .mul (loc IS_REAL) (.add (loc IS_REAL) (.const (-1)))⟩

/-- **Real rows are a PREFIX** — forbid a `0 → 1` transition (`realMonotone`). -/
def realMonotone : AirLeg :=
  .window ⟨RowSel.transition,
    .mul (nxt IS_REAL) (.add (.const 1) (.mul (.const (-1)) (loc IS_REAL)))⟩

/-- **Seed the counter** — `REAL_COUNT[0] = IS_REAL[0]` (`firstRealCount`). -/
def firstRealCount : AirLeg :=
  .window ⟨RowSel.first, .add (loc REAL_COUNT) (.mul (.const (-1)) (loc IS_REAL))⟩

/-- **Accumulate** — `REAL_COUNT[i+1] = REAL_COUNT[i] + IS_REAL[i+1]` (`realCountAccum`). -/
def realCountAccum : AirLeg :=
  .window ⟨RowSel.transition,
    .add (nxt REAL_COUNT)
      (.add (.mul (.const (-1)) (loc REAL_COUNT)) (.mul (.const (-1)) (nxt IS_REAL)))⟩

/-- The eight low lanes of a nonet, as ONE `.limbs` leg at 29 bits — the same gadget the sibling
rung uses, not a second copy. -/
def lowLanesLeg (cols : List Nat) : AirLeg :=
  .limbs { cols := cols, bits := MINA_LANE_BITS, table := minaRangeTid MINA_LANE_BITS }

/-- The top lane, on the NARROW 22-bit table — the leg that separates "well-formed 32-byte nonet"
from "canonical Pasta field element". -/
def topLaneLeg (col : Nat) : AirLeg :=
  .lookup { table := minaRangeTid MINA_TOP_LANE_BITS, tuple := [Expr.var col] }

/-- The nine FIRST-row anchor pins (`firstOldRootBind` at nine lanes). -/
def anchorPins : List AirLeg :=
  [ .pin ⟨VmRow.first, PARENT 0, PI_ANCHOR 0⟩
  , .pin ⟨VmRow.first, PARENT 1, PI_ANCHOR 1⟩
  , .pin ⟨VmRow.first, PARENT 2, PI_ANCHOR 2⟩
  , .pin ⟨VmRow.first, PARENT 3, PI_ANCHOR 3⟩
  , .pin ⟨VmRow.first, PARENT 4, PI_ANCHOR 4⟩
  , .pin ⟨VmRow.first, PARENT 5, PI_ANCHOR 5⟩
  , .pin ⟨VmRow.first, PARENT 6, PI_ANCHOR 6⟩
  , .pin ⟨VmRow.first, PARENT 7, PI_ANCHOR 7⟩
  , .pin ⟨VmRow.first, PARENT 8, PI_ANCHOR 8⟩ ]

/-- The nine LAST-row tip pins (`lastNewRootBind` at nine lanes). -/
def tipPins : List AirLeg :=
  [ .pin ⟨VmRow.last, OWNHASH 0, PI_TIP 0⟩
  , .pin ⟨VmRow.last, OWNHASH 1, PI_TIP 1⟩
  , .pin ⟨VmRow.last, OWNHASH 2, PI_TIP 2⟩
  , .pin ⟨VmRow.last, OWNHASH 3, PI_TIP 3⟩
  , .pin ⟨VmRow.last, OWNHASH 4, PI_TIP 4⟩
  , .pin ⟨VmRow.last, OWNHASH 5, PI_TIP 5⟩
  , .pin ⟨VmRow.last, OWNHASH 6, PI_TIP 6⟩
  , .pin ⟨VmRow.last, OWNHASH 7, PI_TIP 7⟩
  , .pin ⟨VmRow.last, OWNHASH 8, PI_TIP 8⟩ ]

/-! ## §3 — ⚑ THE SOURCE AIR, and the descriptor as the COMPILER'S OUTPUT. -/

/-- ⚑ **THE SOURCE.** Thirty-nine legs: fifteen windows (nine lane-continuity + six counting/height),
two `.limbs` + two narrow lookups for per-row canonicality, and twenty PI pins. -/
def minaLinkAir : EffectAir :=
  { tables := [minaLaneTable, minaTopLaneTable]
  , legs   :=
      [ laneContinuity 0, laneContinuity 1, laneContinuity 2, laneContinuity 3
      , laneContinuity 4, laneContinuity 5, laneContinuity 6, laneContinuity 7
      , laneContinuity 8
      , heightIncrement
      , firstHeight
      , isRealBoolean
      , realMonotone
      , firstRealCount
      , realCountAccum
      , lowLanesLeg parentLowLanes
      , topLaneLeg (PARENT 8)
      , lowLanesLeg ownHashLowLanes
      , topLaneLeg (OWNHASH 8) ]
      ++ anchorPins ++ tipPins
      ++ [ .pin ⟨VmRow.first, ANCHOR_H, PI_ANCHOR_H⟩
         , .pin ⟨VmRow.last, REAL_COUNT, PI_SEG_LEN⟩ ] }

/-- ⚑ **THE VOCABULARY WAS ADEQUATE, AND THE MULTI-ROW HALF IS WHERE IT MATTERED.** Every leg is
main-rail expressible — decided on the emitted predicate, not by eye — so no leg lowered to
`EffectLower.refuseConstraints`. In particular the nine `.transition` lane-continuity legs and the
two `.first` row-local fixes are exactly the `RowSel` capability `EffectAirIR` gained, which is what
made a MULTI-ROW compiled descriptor possible at all. -/
theorem minaLinkAir_mainRailOk : minaLinkAir.mainRailOk = true := by rfl

/-- Every declared PI pin indexes a slot the descriptor declares. -/
theorem minaLinkAir_pinsFit : minaLinkAir.pinsFit MINA_LINK_PI_COUNT = true := by rfl

/-- Thirty-nine legs: 9 lane windows + 6 counting/height windows + 2 `.limbs` + 2 top lookups + 20
pins. -/
theorem minaLinkAir_leg_count : minaLinkAir.legs.length = 39 := by rfl

/-- ⚑ **THE INTER-ROW LAWS ARE COUNTED BY SELECTOR.** Twelve `.transition` legs (nine lane equalities +
the height tick + the monotone pin + the counter accumulation — the laws that need a genuine
successor), two `.first` row-local fixes, and one `.all` boolean pin. A leg that silently re-scoped from `.transition` to
`.all` (which accepts STRICTLY MORE, `TableAirIR.transition_strictly_weaker`) moves this. -/
theorem minaLinkAir_window_selectors :
    minaLinkAir.windowCountSel RowSel.transition = 12
      ∧ minaLinkAir.windowCountSel RowSel.first = 2
      ∧ minaLinkAir.windowCountSel RowSel.all = 1
      ∧ minaLinkAir.windowCountSel RowSel.last = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- Two limbed quantities per row, sixteen per-lane range lookups, and the limbed capacity is the
232-bit LOW half of an `Fp` element with lane 8 gated separately and more narrowly. -/
theorem minaLinkAir_limbs_shape :
    minaLinkAir.limbsCount = 2 ∧ minaLinkAir.totalRangeLookups = 16
      ∧ minaLinkAir.maxLimbedCapacityBits = 232 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- **`minaLinkDesc` — COMPILER OUTPUT.** The exhibited Mina segment as a multi-row IR-v2 AIR. -/
def minaLinkDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-mina-lightclient-link::v1" MINA_LINK_WIDTH MINA_LINK_PI_COUNT [] minaLinkAir

/-! ### §3a — the emission pins. `rfl` against the compiler's output, so a change in the leg
lowerings, the leg ORDER or `assemble` goes red here. -/

theorem minaLinkDesc_name : minaLinkDesc.name = "dregg-mina-lightclient-link::v1" := rfl
theorem minaLinkDesc_width : minaLinkDesc.traceWidth = MINA_LINK_WIDTH := rfl
theorem minaLinkDesc_piCount : minaLinkDesc.piCount = MINA_LINK_PI_COUNT := rfl
theorem minaLinkDesc_tables : minaLinkDesc.tables = [minaLaneTable, minaTopLaneTable] := rfl
theorem minaLinkDesc_hashSites : minaLinkDesc.hashSites = [] := rfl
theorem minaLinkDesc_ranges : minaLinkDesc.ranges = [] := rfl

/-- Fifty-three constraints from thirty-nine legs: one per leg except the two `.limbs` legs, which
lower to EIGHT lookups each. A dropped lane moves this and nothing else does. -/
theorem minaLinkDesc_constraint_count : minaLinkDesc.constraints.length = 53 := rfl

/-- ⚑ **THE NINE LANE-CONTINUITY GATES, AT THEIR EMITTED POSITIONS, AS TRANSITION WINDOWS.** `rfl` on
a slice of the compiler's output. A lane that lost its gate, or a gate that drifted off
`on_transition`, moves this — and an `onTransition := false` here would be UNSATISFIABLE on the last
row rather than merely weaker, so the polarity is load-bearing in both directions. -/
theorem minaLinkDesc_lane_continuity_gates :
    minaLinkDesc.constraints.take 9 =
      (List.range 9).map (fun j =>
        VmConstraint2.windowGate
          ⟨.add (loc (OWNHASH j)) (.mul (.const (-1)) (nxt (PARENT j))), true⟩) := rfl

/-- ⚑ **THE SIXTEEN LANE LOOKUPS AND THE TWO TOP-LANE LOOKUPS.** Constraints 15..22 are the parent's
low lanes at 29 bits, 23 is the parent's TOP lane on the NARROW table, 24..31 the own-hash low lanes,
32 the own-hash top lane. A top-lane query that drifted onto the wide table moves this. -/
theorem minaLinkDesc_canon_lookups :
    (minaLinkDesc.constraints.drop 15).take 18 =
      [ .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 0)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 1)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 2)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 3)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 4)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 5)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 6)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 7)]⟩
      , .lookup ⟨minaRangeTid MINA_TOP_LANE_BITS, [.var (PARENT 8)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 0)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 1)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 2)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 3)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 4)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 5)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 6)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 7)]⟩
      , .lookup ⟨minaRangeTid MINA_TOP_LANE_BITS, [.var (OWNHASH 8)]⟩ ] := rfl

/-- ⚑ **THE TWENTY PI PINS, AND THE TWO THAT MATTER ARE `.last`.** Nine first-row anchor lanes, nine
LAST-row tip lanes, the first-row anchor height, and — the tooth — the LAST-row `REAL_COUNT` as
`PI_SEG_LEN`. A `.last` pin re-scoped to `.first` would read the first row's counter (always
`IS_REAL[0] ∈ {0,1}`) and the segment length would be free again. -/
theorem minaLinkDesc_pins :
    minaLinkDesc.constraints.drop 33 =
      [ .base (.piBinding VmRow.first (PARENT 0) (PI_ANCHOR 0))
      , .base (.piBinding VmRow.first (PARENT 1) (PI_ANCHOR 1))
      , .base (.piBinding VmRow.first (PARENT 2) (PI_ANCHOR 2))
      , .base (.piBinding VmRow.first (PARENT 3) (PI_ANCHOR 3))
      , .base (.piBinding VmRow.first (PARENT 4) (PI_ANCHOR 4))
      , .base (.piBinding VmRow.first (PARENT 5) (PI_ANCHOR 5))
      , .base (.piBinding VmRow.first (PARENT 6) (PI_ANCHOR 6))
      , .base (.piBinding VmRow.first (PARENT 7) (PI_ANCHOR 7))
      , .base (.piBinding VmRow.first (PARENT 8) (PI_ANCHOR 8))
      , .base (.piBinding VmRow.last (OWNHASH 0) (PI_TIP 0))
      , .base (.piBinding VmRow.last (OWNHASH 1) (PI_TIP 1))
      , .base (.piBinding VmRow.last (OWNHASH 2) (PI_TIP 2))
      , .base (.piBinding VmRow.last (OWNHASH 3) (PI_TIP 3))
      , .base (.piBinding VmRow.last (OWNHASH 4) (PI_TIP 4))
      , .base (.piBinding VmRow.last (OWNHASH 5) (PI_TIP 5))
      , .base (.piBinding VmRow.last (OWNHASH 6) (PI_TIP 6))
      , .base (.piBinding VmRow.last (OWNHASH 7) (PI_TIP 7))
      , .base (.piBinding VmRow.last (OWNHASH 8) (PI_TIP 8))
      , .base (.piBinding VmRow.first ANCHOR_H PI_ANCHOR_H)
      , .base (.piBinding VmRow.last REAL_COUNT PI_SEG_LEN) ] := rfl

/-- Layout sanity as theorems: the two nonets are contiguous, disjoint and inside the declared
width, and the counting columns sit above them. -/
theorem minaLink_layout_wellformed :
    PARENT 0 = 0 ∧ PARENT 8 = 8 ∧ OWNHASH 0 = 9 ∧ OWNHASH 8 = 17
      ∧ HEIGHT = 18 ∧ IS_REAL = 19 ∧ REAL_COUNT = 20 ∧ ANCHOR_H = 21
      ∧ ANCHOR_H < MINA_LINK_WIDTH ∧ PI_SEG_LEN < MINA_LINK_PI_COUNT := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide

/-! ### §3b — ⚑ THE (a)/(b) DECISION, DECIDED ON THE EMITTED BYTES.

The header claims this rung needs no non-native multiplication. That is not a promise about intent.
`prodCols` collects the columns appearing under a `.mul` whose BOTH sides read a trace cell — the
syntactic signature of a limb product — and the theorem below says the whole descriptor's set is
`{IS_REAL}`. So no gate multiplies two different columns anywhere, hence no schoolbook limb-product
accumulator is reachable from this descriptor and it inherits nothing from the Pasta cone. -/

/-- Does this body read a trace cell at all? -/
def readsCell : WindowExpr → Bool
  | .loc _ => true
  | .nxt _ => true
  | .const _ => false
  | .add a b => readsCell a || readsCell b
  | .mul a b => readsCell a || readsCell b

/-- Every column index this body reads. -/
def cellCols : WindowExpr → List Nat
  | .loc c => [c]
  | .nxt c => [c]
  | .const _ => []
  | .add a b => cellCols a ++ cellCols b
  | .mul a b => cellCols a ++ cellCols b

/-- ⚑ The columns appearing under a product of two cell-reading factors. Empty for a body that is
affine in the trace; `[c]` for a body squaring one column; two DIFFERENT indices exactly when the
body multiplies two distinct witnesses, which is the limb-product signature. -/
def prodCols : WindowExpr → List Nat
  | .loc _ => []
  | .nxt _ => []
  | .const _ => []
  | .add a b => prodCols a ++ prodCols b
  | .mul a b =>
      (if readsCell a && readsCell b then cellCols a ++ cellCols b else []) ++
        prodCols a ++ prodCols b

/-- The product columns of one emitted constraint (only window gates carry bodies here). -/
def constraintProdCols : VmConstraint2 → List Nat
  | .windowGate w => prodCols w.body
  | _ => []

/-- ⚑⚑ **NO PRODUCT OF TWO DISTINCT COLUMNS ANYWHERE IN THE EMITTED OBJECT.** The only column that
ever appears under a two-sided product is `IS_REAL` — the boolean pin `x·(x−1)` and the monotone pin
`x'·(1−x)`, both degree 2 in ONE column and neither a limb product. This is the (a)/(b) decision
decided on the compiler's output rather than asserted in prose: a non-native Pasta multiply would put
two different limb columns in this list. -/
theorem minaLink_products_are_only_the_real_bit :
    (minaLinkDesc.constraints.flatMap constraintProdCols).eraseDups = [IS_REAL] := by rfl

/-- …and the emitted bodies never multiply two DIFFERENT columns: the product-column set is a
singleton. Stated separately because it is the property that matters (a limb product needs two
indices) and it survives a re-layout that moves `IS_REAL`. -/
theorem minaLink_no_two_column_product :
    (minaLinkDesc.constraints.flatMap constraintProdCols).eraseDups.length = 1 := by rfl

/-! ## §4 — the acceptance predicate, and its tie to the EMITTED bodies.

Acceptance is stated over a `VmRowEnv` window (`loc`/`nxt`/`pub`), exactly as
`EffectVmEmitTurnChainBinding.turnChainWindowHolds` is, so it is the emitted constraint set's own
denotation rather than a private notion. -/

/-- The emitted constraint set, on one row window. -/
def linkWindowHolds (hash : List ℤ → ℤ) (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily)
    (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ minaLinkDesc.constraints, c.holdsAt hash tf env isFirst isLast

/-- ⚑ **A TRANSITION WINDOW MEANS ITS BODY VANISHES mod `P`** — the window analog of
`LightClientMinaAir.emitted_gate_means_source`, so §7's conjuncts are the emitted bodies' meaning and
not a restatement of them. -/
theorem emitted_transition_means_body (hash : List ℤ → ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (body : WindowExpr) :
    (VmConstraint2.windowGate ⟨body, true⟩).holdsAt hash tf env isFirst false
      ↔ body.eval env ≡ 0 [ZMOD 2013265921] := by
  simp [VmConstraint2.holdsAt, WindowConstraint.holdsAt]

/-- …and an `.all`-scoped window vanishes on every row, the LAST row included. That is why the
boolean pin is `.all`: at `.transition` a padding row in the final slot would be unpinned. -/
theorem emitted_all_means_body (hash : List ℤ → ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (body : WindowExpr) :
    (VmConstraint2.windowGate ⟨body, false⟩).holdsAt hash tf env isFirst isLast
      ↔ body.eval env ≡ 0 [ZMOD 2013265921] := by
  simp [VmConstraint2.holdsAt, WindowConstraint.holdsAt]

/-! ## §5 — ⚑ THE COUPLING: canonical lanes make the mod-`P` linkage an EXACT equality. -/

/-- Every lane of a canonical nonet lies in `[0, P)` — the hypothesis the exactness lemma needs, and
it is DERIVED from the emitted lookups rather than assumed (`2^29 < P` and `2^22 < P`). -/
theorem limbsInRange_below_field {a : Assignment} :
    ∀ l : List Nat, LimbsInRange MINA_LANE_BITS a l → ∀ c ∈ l, 0 ≤ a c ∧ a c < 2013265921 := by
  intro l
  induction l with
  | nil => intro _ c hc; simp at hc
  | cons d ds ih =>
    rintro ⟨⟨hd0, hdlt⟩, hrest⟩ c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨hd0, lt_of_lt_of_le hdlt (by norm_num [MINA_LANE_BITS])⟩
    · exact ih hrest c hc'

theorem laneCanon_lane_below_field {a : Assignment} {low : List Nat} {top : Nat}
    (h : laneCanon a low top) :
    (∀ c ∈ low, 0 ≤ a c ∧ a c < 2013265921) ∧ (0 ≤ a top ∧ a top < 2013265921) := by
  obtain ⟨hlow, htop0, htoplt⟩ := h
  exact ⟨limbsInRange_below_field low hlow,
         htop0, lt_of_lt_of_le htoplt (by norm_num [MINA_TOP_LANE_BITS])⟩

/-- ⚑ **THE EXACTNESS LEMMA.** A lane-continuity gate forces `OWNHASH[j] − PARENT'[j] ≡ 0 [ZMOD P]`.
With BOTH lanes range-gated below `2^29 < P` — which the canonicality legs of the SAME descriptor
force — the congruence is an EXACT equality. ⚠ Without the canonicality rung this is FALSE: each lane
could differ by `P` and every gate would still hold. The two rungs are coupled. -/
theorem link_lane_equality_is_exact {x y : ℤ}
    (hx : 0 ≤ x ∧ x < 2013265921) (hy : 0 ≤ y ∧ y < 2013265921)
    (h : x + (-1) * y ≡ 0 [ZMOD 2013265921]) : x = y := by
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  omega

/-! ## §6 — ⚑ THE RESIDUAL, NAMED. -/

/-- ⚑ **`LinkHashResidual` — WHAT THIS DESCRIPTOR DOES NOT FORCE, as a `Prop` rather than a caveat.**

Row `i`'s `OWNHASH` nonet denotes the Poseidon-over-Pasta protocol-state hash of block `i`'s state
row. **This is the Pasta multiply.** Every theorem below that reaches `ChainFrom` takes it as a
HYPOTHESIS; it is discharged by the witness generator today, i.e. it is TRUSTED.

⚠ It is load-bearing and it is not small. A prover free to choose `OWNHASH` can fabricate a chain of
any length between any two `Fp` elements; what makes a row a real Mina block is `PICKLES_OK`, which
is also still a witness. What this descriptor removes is the freedom to be INCONSISTENT and the
freedom to claim a depth without paying rows for it. -/
def LinkHashResidual (L : MinaLeaf) (enc : L.Digest → ℤ) (rows : List Assignment)
    (blocks : List (MinaHeader L)) : Prop :=
  ∀ i, (hi : i < rows.length) → (hb : i < blocks.length) →
    ownHashValue rows[i] = enc (blockHash L blocks[i])

/-- The companion tie for the PARENT nonet. ⚑ Unlike `LinkHashResidual` this is a pure ENCODING
statement — no hash is computed — discharged by writing the nine lanes of a value the generator
already holds (`turn/src/executor/mina_head_verifier.rs::check_head_binding` computes exactly this
decomposition). -/
def LinkParentEncoding (L : MinaLeaf) (enc : L.Digest → ℤ) (rows : List Assignment)
    (blocks : List (MinaHeader L)) : Prop :=
  ∀ i, (hi : i < rows.length) → (hb : i < blocks.length) →
    parentValue rows[i] = enc (blocks[i]).parent

/-! ## §7 — the segment predicate over a whole trace, and the derived facts. -/

/-- One adjacent-row window's content, as the five transition gates force it (exactly on the lane
half, via §5's coupling). -/
structure LinkStep (a b : Assignment) : Prop where
  /-- The nine lane equalities — `OWNHASH[i] = PARENT[i+1]`, `rootContinuity` at nine lanes. -/
  lanes : ∀ j, j < STATE_LIMBS → a (OWNHASH j) = b (PARENT j)
  /-- The height ticks by exactly one. -/
  height : b HEIGHT = a HEIGHT + 1
  /-- Real rows are a prefix. -/
  monotone : b IS_REAL * (1 - a IS_REAL) = 0
  /-- The counter accumulates. -/
  count : b REAL_COUNT = a REAL_COUNT + b IS_REAL

/-- The first row's boundary content (two `.first` windows and ten `.first` pins). -/
structure LinkFirst (a : Assignment) (pub : Assignment) : Prop where
  anchor : ∀ j, j < STATE_LIMBS → a (PARENT j) = pub (PI_ANCHOR j)
  anchorH : a ANCHOR_H = pub PI_ANCHOR_H
  height : a HEIGHT = a ANCHOR_H + 1
  count : a REAL_COUNT = a IS_REAL

/-- The last row's boundary content (ten `.last` pins). -/
structure LinkLast (a : Assignment) (pub : Assignment) : Prop where
  tip : ∀ j, j < STATE_LIMBS → a (OWNHASH j) = pub (PI_TIP j)
  segLen : a REAL_COUNT = pub PI_SEG_LEN

/-- Both nonets of a row are canonical `Fp` elements — the eighteen per-row lookups. -/
def RowCanon (a : Assignment) : Prop :=
  laneCanon a parentLowLanes (PARENT 8) ∧ laneCanon a ownHashLowLanes (OWNHASH 8)

/-- ⚑ **`linkShapeAccepts` — THE DERIVED PREDICATE, AND ITS NAME SAYS WHAT IT IS.** The emitted
descriptor accepts this trace: every row canonical and `IS_REAL`-boolean, every adjacent pair a
`LinkStep`, the first row anchored, the last row pinned to the tip and to the segment length.

⚠ It is the segment's SHAPE. It is NOT `LightClientMina.linkOk`, which additionally requires each
`OWNHASH` to BE the block's Poseidon state hash (`LinkHashResidual`). -/
structure linkShapeAccepts (rows : List Assignment) (pub : Assignment) : Prop where
  nonempty : rows ≠ []
  canon : ∀ a ∈ rows, RowCanon a
  isReal : ∀ a ∈ rows, a IS_REAL * (a IS_REAL - 1) = 0
  steps : List.IsChain LinkStep rows
  first : ∀ a, rows.head? = some a → LinkFirst a pub
  last : ∀ a, rows.getLast? = some a → LinkLast a pub

/-- ⚑ **DERIVED FACT 1 — THE LANE CHAIN IS AN `Fp` CHAIN.** Nine lane equalities on an adjacent pair
give equality of the two nonets' DENOTED field elements. This is `chainLinked`'s `h.parent = prev`
conjunct at the representation BabyBear actually has. -/
theorem step_chains_values {a b : Assignment} (h : LinkStep a b) :
    ownHashValue a = parentValue b := by
  simp only [ownHashValue, parentValue, stateValue,
    Dregg2.Circuit.Emit.LightClientMinaAir.nonetOf, parentLowLanes, ownHashLowLanes,
    List.cons_append, List.nil_append,
    Dregg2.Circuit.LimbTally.limbValue_cons, Dregg2.Circuit.LimbTally.limbValue_nil,
    h.lanes 0 (by decide), h.lanes 1 (by decide), h.lanes 2 (by decide),
    h.lanes 3 (by decide), h.lanes 4 (by decide), h.lanes 5 (by decide), h.lanes 6 (by decide),
    h.lanes 7 (by decide), h.lanes 8 (by decide)]

/-- The `Fp` element the PUBLIC anchor lanes denote. -/
def anchorValue (pub : Assignment) : ℤ :=
  stateValue pub [PI_ANCHOR 0, PI_ANCHOR 1, PI_ANCHOR 2, PI_ANCHOR 3, PI_ANCHOR 4, PI_ANCHOR 5,
    PI_ANCHOR 6, PI_ANCHOR 7] (PI_ANCHOR 8)

/-- The `Fp` element the PUBLIC tip lanes denote. -/
def tipValue (pub : Assignment) : ℤ :=
  stateValue pub [PI_TIP 0, PI_TIP 1, PI_TIP 2, PI_TIP 3, PI_TIP 4, PI_TIP 5, PI_TIP 6, PI_TIP 7]
    (PI_TIP 8)

/-- The first row's nine anchor pins give the `Fp`-level anchoring. -/
theorem first_pins_anchor_value {a pub : Assignment} (h : LinkFirst a pub) :
    parentValue a = anchorValue pub := by
  simp only [parentValue, anchorValue, stateValue,
    Dregg2.Circuit.Emit.LightClientMinaAir.nonetOf, parentLowLanes,
    List.cons_append, List.nil_append,
    Dregg2.Circuit.LimbTally.limbValue_cons, Dregg2.Circuit.LimbTally.limbValue_nil,
    h.anchor 0 (by decide), h.anchor 1 (by decide), h.anchor 2 (by decide),
    h.anchor 3 (by decide), h.anchor 4 (by decide), h.anchor 5 (by decide),
    h.anchor 6 (by decide), h.anchor 7 (by decide), h.anchor 8 (by decide)]

/-- The last row's nine tip pins give the `Fp`-level tip binding. -/
theorem last_pins_tip_value {a pub : Assignment} (h : LinkLast a pub) :
    ownHashValue a = tipValue pub := by
  simp only [ownHashValue, tipValue, stateValue,
    Dregg2.Circuit.Emit.LightClientMinaAir.nonetOf, ownHashLowLanes,
    List.cons_append, List.nil_append,
    Dregg2.Circuit.LimbTally.limbValue_cons, Dregg2.Circuit.LimbTally.limbValue_nil,
    h.tip 0 (by decide), h.tip 1 (by decide), h.tip 2 (by decide),
    h.tip 3 (by decide), h.tip 4 (by decide), h.tip 5 (by decide), h.tip 6 (by decide),
    h.tip 7 (by decide), h.tip 8 (by decide)]

/-- ⚑ **`SegmentFrom` — the `Fp`-level chain the descriptor forces, in `ChainFrom`'s own shape.**
Each row's parent value IS the running value, its height is one more than the running height, and
the running value becomes that row's OWN hash value. Compare `LightClientMina.ChainFrom`
(`Bridge/LightClientMina.lean:214`): the same recursion, over lane-denoted `ℤ` instead of `Digest`. -/
def SegmentFrom (prevVal prevH : ℤ) : List Assignment → Prop
  | [] => True
  | a :: rest =>
      parentValue a = prevVal ∧ a HEIGHT = prevH + 1 ∧
        SegmentFrom (ownHashValue a) (a HEIGHT) rest

/-- ⚑⚑ **DERIVED FACT 2 — ACCEPTANCE IS A CHAIN FROM THE PINNED ANCHOR.** No hypothesis: this is
what the emitted gates force, all of it. The anchor's `Fp` value, the contiguous heights, and every
adjacent link. -/
theorem segmentFrom_of_isChain :
    ∀ (rows : List Assignment) (a : Assignment) (pv ph : ℤ),
      List.IsChain LinkStep (a :: rows) → parentValue a = pv → a HEIGHT = ph + 1 →
      SegmentFrom pv ph (a :: rows) := by
  intro rows
  induction rows with
  | nil => intro a pv ph _ hp hh; exact ⟨hp, hh, trivial⟩
  | cons b rest ih =>
    intro a pv ph hch hp hh
    have hst : LinkStep a b := (List.isChain_cons_cons.mp hch).1
    have hch' : List.IsChain LinkStep (b :: rest) := (List.isChain_cons_cons.mp hch).2
    exact ⟨hp, hh, ih b (ownHashValue a) (a HEIGHT) hch'
      (step_chains_values hst).symm (by rw [hst.height])⟩

theorem linkShapeAccepts_gives_SegmentFrom {rows : List Assignment} {pub : Assignment}
    (h : linkShapeAccepts rows pub) :
    SegmentFrom (anchorValue pub) (pub PI_ANCHOR_H) rows := by
  match rows, h.nonempty with
  | a :: rest, _ =>
    have hf : LinkFirst a pub := h.first a rfl
    exact segmentFrom_of_isChain rest a (anchorValue pub) (pub PI_ANCHOR_H) h.steps
      (first_pins_anchor_value hf) (by rw [hf.height, hf.anchorH])

/-- ⚑ **DERIVED FACT 3 — the heights along an accepted segment are contiguous from the anchor.**
The corollary a reader wants stated in one line. -/
theorem link_heights_are_contiguous {rows : List Assignment} {pub : Assignment}
    (h : linkShapeAccepts rows pub) (a : Assignment) (rest : List Assignment)
    (hrows : rows = a :: rest) : a HEIGHT = pub PI_ANCHOR_H + 1 := by
  subst hrows
  exact ((linkShapeAccepts_gives_SegmentFrom h).2.1)

/-- The counter's law along a chain: the last row's `REAL_COUNT` is at most the starting value plus
the number of further rows, because every `IS_REAL` is at most `1`. -/
theorem last_count_le (rows : List Assignment) :
    ∀ (a : Assignment) (n : ℤ), List.IsChain LinkStep (a :: rows) →
      (∀ x ∈ (a :: rows), x IS_REAL * (x IS_REAL - 1) = 0) →
      a REAL_COUNT ≤ n →
      ∀ z, (a :: rows).getLast? = some z → z REAL_COUNT ≤ n + (rows.length : ℤ) := by
  induction rows with
  | nil =>
    intro a n _ _ hstart z hz
    simp only [List.getLast?_singleton, Option.some.injEq] at hz
    subst hz; simpa using hstart
  | cons b rest ih =>
    intro a n hch hbool hstart z hz
    have hst : LinkStep a b := (List.isChain_cons_cons.mp hch).1
    have hch' : List.IsChain LinkStep (b :: rest) := (List.isChain_cons_cons.mp hch).2
    have hb : b IS_REAL * (b IS_REAL - 1) = 0 := hbool b (by simp)
    have hb1 : b IS_REAL ≤ 1 := by
      rcases mul_eq_zero.mp hb with h0 | h1 <;> omega
    have hstart' : b REAL_COUNT ≤ n + 1 := by rw [hst.count]; linarith
    have hz' : (b :: rest).getLast? = some z := by simpa using hz
    have := ih b (n + 1) hch' (fun x hx => hbool x (by simp [hx])) hstart' z hz'
    simp only [List.length_cons]
    push_cast
    linarith

/-- ⚑⚑ **DERIVED FACT 4 — THE PUBLISHED SEGMENT LENGTH IS PAID FOR IN ROWS.** `PI_SEG_LEN` is the
last row's `REAL_COUNT`, which accumulates `IS_REAL` over rows that are `0/1`-pinned — so a prover
publishing `PI_SEG_LEN = n` has committed a trace with at least `n` rows.

⚑ **This is the tooth `LightClientMinaAir` could not have.** There `SEG_LEN` is a free witness column
in a SINGLE-ROW descriptor, constrained only into `[1, 2^24]`, and `minaLcAir_no_forgery` takes
`a SEG_LEN = u.blocks.length` as a HYPOTHESIS. Here it is a theorem about the committed trace. -/
theorem link_seg_len_counts_the_real_rows {rows : List Assignment} {pub : Assignment}
    (h : linkShapeAccepts rows pub) : pub PI_SEG_LEN ≤ (rows.length : ℤ) := by
  obtain ⟨hne, _, hbool, hch, hfst, hlst⟩ := h
  match rows, hne with
  | a :: rest, _ =>
    have hf : LinkFirst a pub := hfst a rfl
    have ha : a IS_REAL * (a IS_REAL - 1) = 0 := hbool a (by simp)
    have ha1 : a REAL_COUNT ≤ 1 := by
      rw [hf.count]; rcases mul_eq_zero.mp ha with h0 | h1 <;> omega
    obtain ⟨z, hz⟩ : ∃ z, (a :: rest).getLast? = some z :=
      ⟨(a :: rest).getLast (by simp), by simp [List.getLast?_eq_getLast]⟩
    have hle := last_count_le rest a 1 hch hbool ha1 z hz
    have hpin := (hlst z hz).segLen
    rw [← hpin]
    simp only [List.length_cons]
    push_cast
    linarith

/-! ## §8 — ⚑ THE REFINEMENT: acceptance + the NAMED residual ⟹ `LightClientMina.ChainFrom`. -/

/-- ⚑ **THE PAYOFF, WITH ITS RESIDUAL IN THE STATEMENT.** Given a segment the emitted descriptor
accepts, an INJECTIVE nine-lane encoding of digests, the parent-encoding tie and — the wall —
`LinkHashResidual`, the exhibited segment IS `LightClientMina.ChainFrom` from the pinned anchor.

⚑ Read the hypotheses, not the conclusion. `hres` is the Poseidon-over-Pasta leg and it is TRUSTED.
What the DESCRIPTOR contributes is the `SegmentFrom` argument — the chaining and the heights — and
those are the only conjuncts a gate discharges. `hinj` is the `Faithful9` lane encoding's
injectivity, which the tree proves (`fieldToLanes9_injective`) rather than assumes. -/
theorem segmentFrom_refines_chainFrom (L : MinaLeaf) (enc : L.Digest → ℤ)
    (hinj : Function.Injective enc) :
    ∀ (blocks : List (MinaHeader L)) (rows : List Assignment) (prev : L.Digest) (ph : Nat),
      rows.length = blocks.length →
      (∀ i, (hi : i < rows.length) → (hb : i < blocks.length) →
        rows[i] HEIGHT = ((blocks[i]).height : ℤ)) →
      LinkParentEncoding L enc rows blocks →
      LinkHashResidual L enc rows blocks →
      SegmentFrom (enc prev) (ph : ℤ) rows →
      ChainFrom L prev ph blocks := by
  intro blocks
  induction blocks with
  | nil => intro _ _ _ _ _ _ _ _; trivial
  | cons b rest ih =>
    intro rows prev ph hlen hht hpar hres hseg
    match rows with
    | [] => simp at hlen
    | a :: rows' =>
      obtain ⟨hpv, hhv, hrec⟩ := hseg
      -- the head block's parent IS the running digest
      have hparHead : parentValue a = enc b.parent := hpar 0 (by simp) (by simp)
      have hpb : b.parent = prev := hinj (by rw [← hparHead, hpv])
      -- and its height is one above the running height
      have hhtHead : ((b.height : ℤ)) = (ph : ℤ) + 1 := by
        have h0 := hht 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero] at h0
        rw [← h0, hhv]
      have hhtN : b.height = ph + 1 := by exact_mod_cast hhtHead
      refine ⟨hpb, hhtN, ?_⟩
      -- the running value becomes this block's OWN hash — the residual's one use
      have hown : ownHashValue a = enc (blockHash L b) := hres 0 (by simp) (by simp)
      have hheq : a HEIGHT = ((b.height : ℤ)) := by
        have h0 := hht 0 (by simp) (by simp); simpa using h0
      refine ih rows' (blockHash L b) b.height (by simpa using hlen)
        (fun i hi hb' => by simpa using hht (i + 1) (by simpa using hi) (by simpa using hb'))
        (fun i hi hb' => by simpa using hpar (i + 1) (by simpa using hi) (by simpa using hb'))
        (fun i hi hb' => by simpa using hres (i + 1) (by simpa using hi) (by simpa using hb'))
        ?_
      rw [← hown, ← hheq]
      exact hrec

/-- ⚑ **THE DESCRIPTOR-LEVEL FORM.** An accepted trace, at the pinned anchor, entails the Mina
light client's own `ChainFrom` — modulo `LinkHashResidual`, stated in the hypotheses where a reader
cannot miss it. -/
theorem link_refines_chainFrom (L : MinaLeaf) (ts : MinaTrustedState L)
    (rows : List Assignment) (pub : Assignment) (blocks : List (MinaHeader L))
    (enc : L.Digest → ℤ) (hinj : Function.Injective enc)
    (hlen : rows.length = blocks.length)
    (hanchorEnc : anchorValue pub = enc ts.anchorState)
    (hanchorH : pub PI_ANCHOR_H = (ts.anchorHeight : ℤ))
    (hht : ∀ i, (hi : i < rows.length) → (hb : i < blocks.length) →
      rows[i] HEIGHT = ((blocks[i]).height : ℤ))
    (hpar : LinkParentEncoding L enc rows blocks)
    (hres : LinkHashResidual L enc rows blocks)
    (hacc : linkShapeAccepts rows pub) :
    ChainFrom L ts.anchorState ts.anchorHeight blocks := by
  apply segmentFrom_refines_chainFrom L enc hinj blocks rows ts.anchorState ts.anchorHeight
    hlen hht hpar hres
  have := linkShapeAccepts_gives_SegmentFrom hacc
  rwa [hanchorEnc, hanchorH] at this


/-! ## §9 — ⚑ BOTH POLARITIES, EXHIBITED ON CONCRETE ROWS.

A refusal nothing witnesses is decoration. These are three-row segments on the REAL devnet genesis
anchor and the REAL block-539508 tip (the same two values `LightClientMinaAir` §7 pins against their
Base58Check decimals), accepted; and the same segment with ONE lane bent, refused. -/

/-- A row from its column values, index-ordered from `PARENT 0`. -/
def rowOf (vs : List ℤ) : Assignment := fun w => vs.getD w 0

/-- The two interior state hashes of the exhibited segment. Any canonical nonet does: what the
descriptor forces is that they CHAIN, not what they are — and that is exactly the residual. -/
def MID1_LANES : List ℤ := [11, 22, 33, 44, 55, 66, 77, 88, 99]
def MID2_LANES : List ℤ := [111, 222, 333, 444, 555, 666, 777, 888, 999]

/-- Row 0 — parent is the REAL devnet genesis anchor, height 1001, real. -/
def hrow0 : Assignment :=
  rowOf (Dregg2.Circuit.Emit.LightClientMinaAir.GENESIS_ANCHOR_LANES ++ MID1_LANES
    ++ [1001, 1, 1, 1000])

/-- Row 1 — parent is row 0's own hash. -/
def hrow1 : Assignment := rowOf (MID1_LANES ++ MID2_LANES ++ [1002, 1, 2, 1000])

/-- Row 2 — parent is row 1's own hash, own hash is the REAL devnet block-539508 tip. -/
def hrow2 : Assignment :=
  rowOf (MID2_LANES ++ Dregg2.Circuit.Emit.LightClientMinaAir.DEVNET_TIP_LANES
    ++ [1003, 1, 3, 1000])

/-- The public inputs: the pinned anchor, the verified tip, the anchor height, and the segment
length THE TRACE PAYS FOR. -/
def honestPub : Assignment :=
  rowOf (Dregg2.Circuit.Emit.LightClientMinaAir.GENESIS_ANCHOR_LANES
    ++ Dregg2.Circuit.Emit.LightClientMinaAir.DEVNET_TIP_LANES ++ [1000, 3])

/-- The honest three-block exhibited segment. -/
def honestSegment : List Assignment := [hrow0, hrow1, hrow2]

theorem honest_step_01 : LinkStep hrow0 hrow1 :=
  { lanes := by decide, height := by decide, monotone := by decide, count := by decide }

theorem honest_step_12 : LinkStep hrow1 hrow2 :=
  { lanes := by decide, height := by decide, monotone := by decide, count := by decide }

theorem honest_first : LinkFirst hrow0 honestPub :=
  { anchor := by decide, anchorH := by decide, height := by decide, count := by decide }

theorem honest_last : LinkLast hrow2 honestPub :=
  { tip := by decide, segLen := by decide }

/-- ⚑ **ACCEPTED — a three-block anchored segment on REAL devnet lanes.** Every row canonical, every
`IS_REAL` boolean, both links exact, the anchor pinned, the tip pinned, and `PI_SEG_LEN = 3` paid for
by three rows. Without this the rung would be satisfied by a descriptor that refuses everything. -/
theorem honest_segment_accepted : linkShapeAccepts honestSegment honestPub where
  nonempty := by simp [honestSegment]
  canon := by
    intro a ha
    simp only [honestSegment, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  isReal := by
    intro a ha
    simp only [honestSegment, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  steps := by
    refine List.isChain_cons_cons.mpr ⟨honest_step_01, ?_⟩
    exact List.isChain_cons_cons.mpr ⟨honest_step_12, List.isChain_singleton _⟩
  first := by
    intro a ha
    simp only [honestSegment, List.head?_cons, Option.some.injEq] at ha
    subst ha; exact honest_first
  last := by
    intro a ha
    simp only [honestSegment] at ha
    have h2 : a = hrow2 := by simpa using ha.symm
    subst h2; exact honest_last

/-- ⚑ **DERIVED FACT 4, ON THE WITNESS.** The accepted segment's published length is paid for in
rows — three claimed, three committed. -/
theorem honest_segment_pays_for_its_length : honestPub PI_SEG_LEN ≤ (honestSegment.length : ℤ) :=
  link_seg_len_counts_the_real_rows honest_segment_accepted

/-- ⚑ **THE BENT LANE.** Row 1's parent lane 0 is `12` where row 0's own-hash lane 0 is `11`. It is a
perfectly canonical lane (`12 < 2^29`), so every canonicality lookup still passes, every height still
ticks, and `IS_REAL`/`REAL_COUNT` are untouched. Only the linkage is broken. -/
def brokenRow1 : Assignment :=
  rowOf ((12 :: MID1_LANES.tail) ++ MID2_LANES ++ [1002, 1, 2, 1000])

/-- The bent row is still a well-formed canonical row — so the refusal below is the LINKAGE gate's
and not the canonicality gate's. -/
theorem broken_row_is_still_canonical : RowCanon brokenRow1 := ⟨by decide, by decide⟩

/-- …and its height and counter are still exactly the honest row's, so nothing but the link differs. -/
theorem broken_row_differs_only_in_the_link :
    brokenRow1 HEIGHT = hrow1 HEIGHT ∧ brokenRow1 IS_REAL = hrow1 IS_REAL
      ∧ brokenRow1 REAL_COUNT = hrow1 REAL_COUNT
      ∧ brokenRow1 (PARENT 0) ≠ hrow0 (OWNHASH 0) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

def brokenSegment : List Assignment := [hrow0, brokenRow1, hrow2]

/-- ⚑⚑ **REFUSED — THE MISMATCHED PARENT.** This is the forgery `LightClientMinaAir`'s witnessed
`LINK_OK = 1` waves through: a segment whose second block's `previousStateHash` is NOT the first
block's state hash. The bent lane is canonical, so the canonicality rung does not refuse it; the
lane-continuity window gate does. -/
theorem broken_link_refused : ¬ linkShapeAccepts brokenSegment honestPub := by
  intro h
  have hst : LinkStep hrow0 brokenRow1 := (List.isChain_cons_cons.mp h.steps).1
  have := hst.lanes 0 (by decide)
  revert this
  decide

/-- ⚑⚑ **OLD ADMITS, NEW REJECTS — the rung as one theorem.** The bent segment satisfies everything
the PRE-RUNG descriptor could see about linkage: its rows are canonical, its heights are contiguous,
its counter is right, and `LINK_OK` is a bit a prover sets to `1`. `linkShapeAccepts` refuses it.
Nothing about the trace changed; the carrier stopped being a bit somebody wrote down. -/
theorem broken_link_old_admits_new_rejects :
    (RowCanon hrow0 ∧ RowCanon brokenRow1 ∧ RowCanon hrow2)
      ∧ brokenRow1 HEIGHT = hrow0 HEIGHT + 1
      ∧ ¬ linkShapeAccepts brokenSegment honestPub :=
  ⟨⟨⟨by decide, by decide⟩, broken_row_is_still_canonical, ⟨by decide, by decide⟩⟩,
   by decide, broken_link_refused⟩

/-- ⚑ **REFUSED — THE FREE DEPTH.** The same three exhibited rows, but the published `PI_SEG_LEN`
claims 290 (mainnet Samasika `k`). `link_seg_len_counts_the_real_rows` refuses it: 290 rows were not
committed. ⚠ This is the shape `LightClientMinaAir` CANNOT refuse — there `SEG_LEN` is a free witness
column in a single-row descriptor and 290 is as cheap to write as 3. -/
def liarPub : Assignment :=
  rowOf (Dregg2.Circuit.Emit.LightClientMinaAir.GENESIS_ANCHOR_LANES
    ++ Dregg2.Circuit.Emit.LightClientMinaAir.DEVNET_TIP_LANES ++ [1000, 290])

theorem short_segment_refused : ¬ linkShapeAccepts honestSegment liarPub := by
  intro h
  have hle := link_seg_len_counts_the_real_rows h
  have : liarPub PI_SEG_LEN = 290 := by decide
  rw [this] at hle
  simp only [honestSegment, List.length_cons, List.length_nil] at hle
  norm_num at hle

/-- ⚑ **THE POLARITY PAIR, AS ONE STATEMENT.** The emitted logic DISCRIMINATES: it accepts an honest
anchored segment on real devnet lanes and refuses both the mismatched parent and the free depth. -/
theorem mina_link_discriminates :
    linkShapeAccepts honestSegment honestPub
      ∧ ¬ linkShapeAccepts brokenSegment honestPub
      ∧ ¬ linkShapeAccepts honestSegment liarPub :=
  ⟨honest_segment_accepted, broken_link_refused, short_segment_refused⟩

/-! ## §10 — axiom hygiene. Every asserted fact above is a NAMED THEOREM; this file contains no
`#guard` (`metatheory/docs/GUARD-DISCIPLINE.md`). -/

#assert_axioms minaLinkAir_mainRailOk
#assert_axioms minaLinkAir_pinsFit
#assert_axioms minaLinkAir_leg_count
#assert_axioms minaLinkAir_window_selectors
#assert_axioms minaLinkAir_limbs_shape
#assert_axioms minaLinkDesc_constraint_count
#assert_axioms minaLinkDesc_lane_continuity_gates
#assert_axioms minaLinkDesc_canon_lookups
#assert_axioms minaLinkDesc_pins
#assert_axioms minaLink_layout_wellformed
#assert_axioms minaLink_products_are_only_the_real_bit
#assert_axioms minaLink_no_two_column_product
#assert_axioms emitted_transition_means_body
#assert_axioms emitted_all_means_body
#assert_axioms limbsInRange_below_field
#assert_axioms laneCanon_lane_below_field
#assert_axioms link_lane_equality_is_exact
#assert_axioms step_chains_values
#assert_axioms first_pins_anchor_value
#assert_axioms last_pins_tip_value
#assert_axioms segmentFrom_of_isChain
#assert_axioms linkShapeAccepts_gives_SegmentFrom
#assert_axioms link_heights_are_contiguous
#assert_axioms last_count_le
#assert_axioms link_seg_len_counts_the_real_rows
#assert_axioms segmentFrom_refines_chainFrom
#assert_axioms link_refines_chainFrom
#assert_axioms honest_segment_accepted
#assert_axioms honest_segment_pays_for_its_length
#assert_axioms broken_row_is_still_canonical
#assert_axioms broken_link_refused
#assert_axioms broken_link_old_admits_new_rejects
#assert_axioms short_segment_refused
#assert_axioms mina_link_discriminates

end Dregg2.Circuit.Emit.LightClientMinaLinkAir
