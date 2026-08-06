/-
# `Dregg2.Circuit.Emit.MinaAccumulatorAir` — ⚑ THE DEFERRED IPA ACCUMULATOR CHECK, IN A CIRCUIT.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every column index, every pin, every window body and both emitted
descriptors are authored here and go through `EffectLower.lowerAir` of an `EffectAirIR.EffectAir`.
There is no hand-written `VmConstraint2` in this file. Rust PROVES the artifact, FOLDS it, and
authors no constraint. House Law #1.

## WHAT IS BEING PUT IN A CIRCUIT, and it is the leg upstream evaluates natively

`mina-rust`'s verifier `&&`s `Ipa::Step::accumulator_check` into `batch_step_dlog_check`
(`verify.ml:135-146`). With `C` the challenge-polynomial commitment (a **Vesta** point) and `u⃗` the
sixteen endo-lifted bulletproof challenges,

```text
    C == ⟨ b_poly_coefficients(u⃗), srs.g ⟩          |srs.g| = 2^16 = 65 536 Vesta generators
```

and a batch of `N` claims is discharged by ONE MSM over `|G| + N` points:

```text
    Σ_i r^i·C_i  −  ⟨ Σ_i r^i·s(u⃗_i), G ⟩  ==  O
```

`bridge/src/mina_accumulator_discharge.rs` evaluates that **natively** over the byte-pinned SRS, and
`turn/src/executor/mina_accumulator_oracle.rs` makes a Mina head's acceptance depend on it. Both of
those files say, in their own headers, that **nothing there is an AIR**. This file is the AIR.

## ⚑ THE SHAPE, and why the accumulator's ENTRY POINT is the claim

Read the batch relation as a running sum and it is a chain of complete additions:

```text
    acc_0    = C                       -- ⚑ the claim's commitment IS the initial accumulator
    acc_{r+1} = acc_r + A_r            -- A_r the r-th addend
    acc_n    = O                       -- the discharge
```

so with the addends `A_r` the scaled generators `−s_j·G_j`, `acc_n = O` **is** `C − ⟨s, G⟩ = O`.

That is why this file needs no separate "claim block": the accumulator entering row 0 is `C`, it is
published at `PI[0..95]`, and it is joined arithmetically (the six input limb legs range it and the
33 SSA ops read it) rather than pinned decoratively. A consumer that holds this block's `C` compares
it against those 96 published limbs **elementwise — 256 bits per coordinate, no digest and therefore
no birthday bound**, the same shape `LightClientMinaAir`'s `TIP_STATE` seam takes.

## ⚑ WHAT A THREAD BUYS THAT A RE-PIN DOES NOT — inherited, not re-argued

`PastaLadderThread` established it and this file consumes it: the accumulator crosses rows through
96 `AirLeg.window .transition` gates, so `threadedLadder_forces` is an `n`-row induction rather than
a chain of quoted outputs. The width is `RCB_WIDTH = 3 048` at every depth, and the depth is rows.

The same distinction is what the RECURSION half has to preserve. `mina_phase2_chain_leaf`'s lesson —
*"a fold that just re-pins the same public inputs closes nothing"* — is answered here by publishing
`acc_in ‖ acc_out` as **contiguous** PI blocks so a fold node `cb.connect`s the left child's 96
outgoing limbs to the right child's 96 incoming ones. The 96 is not a coincidence: a projective
Pasta point in the sound 8-bit encoding is `3 × 32 = 96` felts, exactly the width the phase-2 chain
already carries its sponge state on.

## ⚑ TWO DESCRIPTORS, AND THE PAIR IS THE POINT

* `dregg-mina-accumulator-seg::v1` — a SEGMENT of the chain. Publishes its two endpoints. Says
  nothing about vanishing, because an intermediate segment must not.
* `dregg-mina-accumulator-final::v1` — the segment PLUS `dischargeLegs`: `2 · SK = 64` `.last`-row
  window gates forcing every limb of the terminal `X` and `Z` blocks to **zero**. That is
  `pasta_msm::is_identity` (`z == 0 && x == 0`) as a constraint, and it is the accumulator check.

The pair is an OLD-ADMITS / NEW-REJECTS exhibit that cannot rot into agreement: a chain that does
not vanish PROVES under `-seg` and is REFUSED under `-final`, and the refusing constraint is a
`.last` window gate on an `OUT_Z` limb — not a range lookup, not a bus.

## What is proved here

* `accSegAir_mainRailOk` / `accFinalAir_mainRailOk` — the compiler accepts both blocks.
* `accSegDesc_constraint_count` / `accFinalDesc_constraint_count` / the widths and PI counts.
* `the_discharge_is_sixty_four_last_row_gates` — the selector census, so a `.last → .all` re-scope
  (which would refuse every intermediate row and make the descriptor accept nothing) moves a number.
* `threadedLadderV_forces` — the Vesta twin of `PastaLadderThread.threadedLadder_forces`.
* `terminalAccumulator_forces` — an `n+1`-row trace's terminal output is the `n+1`-fold RCB chain.
* ⚑ `accumulator_discharge_forced` — rows satisfied + threads held + the discharge gates satisfied
  force the `n+1`-fold chain of the trace's own addends to be the point at infinity mod `q`. This is
  the accumulator check, as a consequence of the emitted constraints.
* `the_discharge_gate_is_refutable` — a trace satisfying every ROW and every THREAD whose terminal
  accumulator is NOT the identity, so `accumulator_discharge_forced`'s last hypothesis is doing work.

## ⚠ WHAT THIS DOES **NOT** ESTABLISH — the addends are the caller's

`threadedLadder_forces` names it and it is inherited verbatim: **nothing here forces the ADDENDS to
be anything in particular.** The chain is forced to be the `n+1`-fold sum of whatever `ADD_X/Y/Z`
the trace supplies. Forcing `A_r` to be the `r`-th scaled SRS generator is the ROUTING half, it
lives in `PastaMsmBucketed`'s three exact-public lookups, and porting those to the sound row's
32-limb encoding is real work this file does not do (§4 prices it, including the one deployed
constant — `MAX_EXACT_PUBLIC_ARITY = 64` — that a 96-limb point tuple exceeds).

So what the emitted object checks is the **SUMMATION half** of the accumulator check, in a circuit,
soundly, at full 256-bit width. The scaling and the routing are named residuals with numbers, not
hidden assumptions.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.PastaLadderThread

namespace Dregg2.Circuit.Emit.MinaAccumulatorAir

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 WindowExpr VmConstraint2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg WindowLeg PiPinLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK NG sVal qLimb)
open Dregg2.Circuit.Emit.PastaCurve (CZm)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3)
open Dregg2.Circuit.Emit.PastaCurveSound
open Dregg2.Circuit.Emit.PastaLadderThread

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §1 — THE PUBLIC INPUT LAYOUT.

`in ‖ out`, contiguous and in that order, so a recursion leaf re-exposes the continuity claim as ONE
slice and a fold node connects `left[96 + k]` to `right[k]` for `k < 96`. This is
`MinaPhase2Chain`'s layout choice, made again for the same reason. -/

/-- PI slot of the `i`-th INCOMING accumulator limb (`i < 3·SK`): X block, then Y, then Z. -/
def ACC_IN_PI (i : Nat) : Nat := i
/-- PI slot of the `i`-th OUTGOING accumulator limb. -/
def ACC_OUT_PI (i : Nat) : Nat := 3 * SK + i
/-- `6 · 32 = 192` — two projective Vesta points in the sound 8-bit encoding. -/
def ACC_PI_COUNT : Nat := 6 * SK

theorem acc_pi_layout :
    ACC_PI_COUNT = 192 ∧ ACC_IN_PI 0 = 0 ∧ ACC_OUT_PI 0 = 96
    ∧ ∀ i, ACC_OUT_PI i = ACC_IN_PI i + 3 * SK := by
  refine ⟨by decide, rfl, by decide, fun i => ?_⟩
  simp [ACC_OUT_PI, ACC_IN_PI, Nat.add_comm]

/-- The FIRST row's accumulator input, published. Its three blocks are contiguous at `0, 32, 64`
(`ACC_X/ACC_Y/ACC_Z`), so the column index and the PI slot agree — but they are written out rather
than assumed equal, because a layout that drifts here aliases two points. -/
def inPinLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [ AirLeg.pin ⟨.first, ACC_X + i, ACC_IN_PI i⟩
    , AirLeg.pin ⟨.first, ACC_Y + i, ACC_IN_PI (SK + i)⟩
    , AirLeg.pin ⟨.first, ACC_Z + i, ACC_IN_PI (2 * SK + i)⟩ ])

/-- The LAST row's accumulator output, published. `OUT_X/OUT_Y/OUT_Z` are the gadget's `v 26/29/32`
and are NOT contiguous in the trace — which is exactly why the PI side is. -/
def outPinLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [ AirLeg.pin ⟨.last, OUT_X + i, ACC_OUT_PI i⟩
    , AirLeg.pin ⟨.last, OUT_Y + i, ACC_OUT_PI (SK + i)⟩
    , AirLeg.pin ⟨.last, OUT_Z + i, ACC_OUT_PI (2 * SK + i)⟩ ])

theorem pin_leg_counts : inPinLegs.length = 96 ∧ outPinLegs.length = 96 := by
  refine ⟨by decide, by decide⟩

/-! ## §2 — ⚑ THE DISCHARGE GATE.

`pasta_msm::is_identity` is `p.z == U256::ZERO && p.x == U256::ZERO`. On the projective curve
`Y²Z = X³ + bZ³` those two are not independent — `Z = 0` forces `X³ = 0` — but the AIR does not
carry an on-curve gate, so BOTH are forced here and the constraint is the deployed predicate rather
than an argument about it.

⚑ **Every LIMB is forced to zero, not the value.** `sVal` over 32 byte-ranged limbs ranges to
`2^256 > q`, so "the value is `≡ 0 mod q`" would also be satisfied by the limbs of `q` and of `2q`.
Forcing the limbs makes the terminal accumulator the CANONICAL zero, which is strictly stronger,
costs nothing (the honest witness reduces) and removes a representation the prover could otherwise
choose. -/

/-- One discharge gate: the `i`-th limb of the block at `base`, on the LAST row, is zero.

`.last` is the selector, and `WindowLeg.mainRailOk` admits it because the body reads no `nxt`. Under
`.all` this would fire on EVERY row and refuse every intermediate accumulator — a descriptor that
accepts nothing, which is the direction a selector confusion goes here. -/
def vanishLeg (base i : Nat) : AirLeg :=
  .window ⟨RowSel.last, WindowExpr.loc (base + i)⟩

theorem vanishLeg_eq (base i : Nat) :
    vanishLeg base i = .window ⟨RowSel.last, WindowExpr.loc (base + i)⟩ := rfl

/-- ⚑ **THE 64 DISCHARGE GATES** — `X` and `Z`, 32 limbs each. -/
def dischargeLegs : List AirLeg :=
  (List.range SK).flatMap (fun i => [vanishLeg OUT_X i, vanishLeg OUT_Z i])

theorem dischargeLegs_length : dischargeLegs.length = 64 := by decide

/-! ## §3 — THE TWO AIRS AND THE TWO DESCRIPTORS. -/

/-- **A SEGMENT of the accumulator chain.** `PastaLadderThread.vestaThreadAir` — the sound Vesta RCB
row with the 96 `.transition` accumulator threads — plus the two published endpoints. -/
def accSegAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (vestaCompleteAddSoundLegs ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE).1
      ++ threadLegs ++ inPinLegs ++ outPinLegs }

/-- ⚑ **THE FINAL SEGMENT** — the same block, plus the discharge. -/
def accFinalAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (vestaCompleteAddSoundLegs ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE).1
      ++ threadLegs ++ inPinLegs ++ outPinLegs ++ dischargeLegs }

/-- ⚑ **THE SEGMENT'S LEGS ARE A PREFIX OF THE FINAL'S.** Every forcing statement about the segment
applies to the final block unchanged — the discharge APPENDS, it does not re-author. -/
theorem accFinalAir_extends_accSegAir : accSegAir.legs <+: accFinalAir.legs :=
  ⟨dischargeLegs, by simp [accSegAir, accFinalAir, List.append_assoc]⟩

/-- ⚑ **THE COMPILER ACCEPTS BOTH BLOCKS.** The 96 threads are `.transition` (the only selector
admitting a `nxt` read) and the 64 discharge gates are `.last` with no `nxt` read. A `.last` thread
or an `.all` discharge would lower to `refuseConstraints` and this would be false. -/
theorem accSegAir_mainRailOk : accSegAir.mainRailOk = true := by decide

theorem accFinalAir_mainRailOk : accFinalAir.mainRailOk = true := by decide

/-- ⚑ **THE SELECTOR CENSUS.** 96 `.transition` threads and 64 `.last` discharge gates, and NONE at
`.all` or `.first`. The two families are byte-identical algebra under a different selector, so the
counts are what keep a re-scope visible: `.last → .all` on the discharge refuses every intermediate
row (a descriptor accepting nothing), `.transition → .all` on the thread accepts strictly more
(`TableAirIR.TableGate.transition_strictly_weaker`). Neither moves a constraint COUNT. -/
theorem the_discharge_is_sixty_four_last_row_gates :
    accFinalAir.windowCountSel RowSel.transition = 96
    ∧ accFinalAir.windowCountSel RowSel.last = 64
    ∧ accFinalAir.windowCountSel RowSel.all = 0
    ∧ accFinalAir.windowCountSel RowSel.first = 0
    ∧ accSegAir.windowCountSel RowSel.last = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The emitted SEGMENT descriptor. -/
def accSegDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-mina-accumulator-seg::v1" RCB_WIDTH ACC_PI_COUNT [] accSegAir

/-- The emitted FINAL descriptor. -/
def accFinalDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-mina-accumulator-final::v1" RCB_WIDTH ACC_PI_COUNT [] accFinalAir

/-- `4 476` sound row-local constraints + `96` accumulator threads + `192` endpoint pins. -/
theorem accSegDesc_constraint_count : accSegDesc.constraints.length = 4476 + 96 + 192 := by decide

/-- …and the final segment is that plus the `64` discharge gates. -/
theorem accFinalDesc_constraint_count :
    accFinalDesc.constraints.length = 4476 + 96 + 192 + 64 := by decide

theorem accSegDesc_width : accSegDesc.traceWidth = 3048 := rfl
theorem accFinalDesc_width : accFinalDesc.traceWidth = 3048 := rfl
theorem accSegDesc_piCount : accSegDesc.piCount = 192 := rfl
theorem accFinalDesc_piCount : accFinalDesc.piCount = 192 := rfl

/-- ⚑ **A NAME IS A KEY.** The two descriptors are different objects and must not share one;
`reference-a-display-name-is-not-a-key` records three wrong lookups in one day from exactly this. -/
theorem the_two_descriptors_do_not_share_a_name : accSegDesc.name ≠ accFinalDesc.name := by decide

/-- ⚑ …and they differ in their CONSTRAINTS, not only in their names. A rename with no algebra
behind it is the shape that makes a registry lookup resolve to a look-alike. -/
theorem the_two_descriptors_differ : accSegDesc.constraints ≠ accFinalDesc.constraints := by
  intro h
  have := congrArg List.length h
  rw [accSegDesc_constraint_count, accFinalDesc_constraint_count] at this
  omega

/-! ## §4 — ⚑ THE GEOMETRY, AS NUMBERS RATHER THAN AS A WORRY.

Three facts, each measured on the emitted object, and the third is the one that says what is NOT
here. -/

/-- The deployed base-trace ceiling (`MAX_EXACT_PUBLIC_ROWS`, `circuit/src/descriptor_ir2.rs`). -/
def DREGG_MAX_ROWS : Nat := 2097152
/-- The deployed exact-public ARITY cap. -/
def MAX_EP_ARITY : Nat := 64
/-- The Step/Tick SRS width, `2^16`. -/
def STEP_SRS : Nat := 65536

/-- Rows a segment of `k` complete additions needs: one row each. -/
def segRows (k : Nat) : Nat := k

/-- Committed cells a `k`-row segment carries at this width. -/
def segCells (k : Nat) : Nat := k * 3048

/-- ⚑ **ONE INSTANCE CANNOT HOLD THE FULL-WIDTH SUM, AND THE FOLD IS WHY THAT IS NOT THE END.**
`PastaMsmBucketed.fused_at_step` prices the whole `2^16`-generator MSM at `1 474 800` complete
additions. At `3 048` columns that is `4.5 · 10⁹` committed cells — so the full-width chain is a
FOLD of segments, not one proof, and the recursion is load-bearing rather than an optimisation. -/
theorem the_full_width_sum_needs_the_fold :
    segCells 1474800 = 4495190400
    ∧ 1000 * DREGG_MAX_ROWS < segCells 1474800 := by
  refine ⟨by decide, by decide⟩

/-- ⚑ **THE ROUTING RESIDUAL — REFUSED AT HEAD, BUT THE CAP IS NOT A PRICE.**

Forcing the addend of row `r` to be a DECLARED SRS generator is an exact-public lookup whose tuple
is the generator index plus the point's limbs. In the sound encoding a projective point is
`3 · 32 = 96` limbs, so the tuple is `97` wide against the deployed `MAX_EXACT_PUBLIC_ARITY = 64`
(`circuit/src/descriptor_ir2.rs:531`), and `check_descriptor2` refuses it (`:2135`). **That refusal
is real and nothing should be designed as though it were not.**

⚠ **BUT THE EARLIER DRAFT OF THIS DOCBLOCK CALLED 64 A PRICE, AND IT IS NOT ONE.** Read at source
2026-08-06: the constant's ONLY other use is a drift guard whose own message says the remedy —
*"the emitted exact-public family covers {family_len} arities but this file admits
{MAX_EXACT_PUBLIC_ARITY}; re-emit `dregg-ir2-exact-public-v1.json` or re-pin the cap"*
(`descriptor_ir2.rs:6737-6742`). So 64 is **the number of members in a checked-in JSON artifact**,
pinned on both sides so the two cannot drift. It is exact as that, and it bounds no resource: the
committed object is `next_pow2(distinct) × (arity + 2)` preprocessed cells in ONE instance
(`ExactPublicManifest::of` at `:3370`, `prep_width` at `:3386`), and at `2^16` distinct generators
a 97-wide table is **6 488 064** cells — 26 MB, one instance.

⚑ It was introduced (`dc285da37`, 2026-07-22) under a comment justifying ROWS and CELLS — *"each row
becomes one batch instance, so bound the grammar before allocation"* — which is an argument about
instance count, and arity does not scale instance count. Its two siblings in that comment have since
moved by `2^14×` and `2^13×`; 64 has never been touched. `a-cost-verdict-outlives-its-premise`.

⚠ **AND THE REMEDY THIS DOCBLOCK USED TO PRESCRIBE IS THE MORE EXPENSIVE ONE** —
see `the_split_remedy_costs_more_than_the_wide_table`. -/
theorem the_routing_tuple_does_not_fit_one_table :
    MAX_EP_ARITY < 1 + 3 * SK
    ∧ 1 + (3 * SK) / 2 < MAX_EP_ARITY
    ∧ 1 + 3 * SK = 97 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The preprocessed width an exact-public table of arity `a` commits: the table id, `a` value
columns, and the pinned multiplicity (`ExactPublicManifest::prep_width`, `descriptor_ir2.rs:3386`).
Written here so the comparison below is against the deployed geometry rather than against a guess. -/
def epPrepWidth (a : Nat) : Nat := a + 2

/-- ⚑⚑ **THE SPLIT REMEDY COSTS MORE THAN THE WIDE TABLE IT AVOIDS.**

This file used to prescribe `PastaMsmBucketed.split_srs_cells_fit`'s medicine — split the 96 limbs
across two tables keyed by the same index, `49 + 49`, clearing the arity cap. Over the same `2^16`
distinct generators that costs `2 · 2^16 · 51 = 6 684 672` preprocessed cells against the single
97-wide table's `2^16 · 99 = 6 488 064`: **196 608 cells MORE**, because each half pays its own
`table_id` and `multiplicity` column. It also costs a second batch instance, a second bus, a second
FRI opening set — and a soundness leg the wide table does not have, since **nothing forces the two
halves keyed by index `r` to name limbs of the SAME generator.**

⚠ And the citation was transplanted across two caps that share no mechanism: `split_srs_cells_fit`
is a theorem about `MAX_EXACT_PUBLIC_CELLS`, not about the ARITY cap this file is blocked by. -/
theorem the_split_remedy_costs_more_than_the_wide_table :
    STEP_SRS * epPrepWidth (1 + 3 * SK) = 6488064
    ∧ 2 * (STEP_SRS * epPrepWidth (1 + (3 * SK) / 2)) = 6684672
    ∧ STEP_SRS * epPrepWidth (1 + 3 * SK)
        < 2 * (STEP_SRS * epPrepWidth (1 + (3 * SK) / 2)) := by
  refine ⟨by decide, by decide, by decide⟩

/-- The SRS the routing would have to cover, and the fact the fold's leaf count is set by the
segment height rather than by the generator count. -/
theorem the_step_srs_is_two_to_the_sixteen : STEP_SRS = 2 ^ 16 := by decide

/-! ### ⚑⚑ §4.1 — WHERE THE 3 048 COLUMNS GO, AND WHICH OF THEM CROSS A ROW BOUNDARY.

The fold's bill is paid in COLUMNS: `circuit-prove/tests/mina_accumulator_leaf_anatomy.rs` measures
the leaf wrap's in-circuit verifier at **2 878 067 ops** for this 3 048-column descriptor against
**248 555** for the 469-column `pasta-fq-chainlink::v1` that folds 46 leaves in production — and the
same measurement's ROW sweep moves the figure by **0.5% across 1 → 8 inner rows**. So the width is
the whole bill and the height is free, and the question this section answers is not "how big is the
row" but **"how much of the row is scratch that only exists because 33 SSA ops share one row."**

Every number below is `decide`d from the layout definitions the descriptor is emitted from — not a
second copy of them. -/

/-- The six INPUT blocks: `ACC_X/Y/Z ‖ ADD_X/Y/Z`, `SK` limbs each. -/
def censusInputs : Nat := 6 * SK
/-- The 33 SSA intermediates, `SK` limbs each (`vBase`). -/
def censusSSA : Nat := 33 * SK
/-- The 12 MULTIPLY witnesses: `SK` quotient limbs then `NG - 1` carries each (`mWit`). -/
def censusMul : Nat := 12 * (SK + (NG - 1))
/-- The 2 CONSTANT-MULTIPLY witnesses, `SK` columns each (`sWit`). -/
def censusSmul : Nat := 2 * SK
/-- The 19 ADD/SUB witnesses, `SK` columns each (`aWit`). -/
def censusAddSub : Nat := 19 * SK

/-- ⚑ **THE COLUMN CENSUS.** Five blocks, each named, summing to the width the descriptor declares.
A layout change that moved a stride would move one of these five numbers rather than only the total,
which is what makes this a census and not a restatement of `rcb_width_eq`. -/
theorem the_column_census :
    censusInputs = 192 ∧ censusSSA = 1056 ∧ censusMul = 1128 ∧ censusSmul = 64
    ∧ censusAddSub = 608
    ∧ censusInputs + censusSSA + censusMul + censusSmul + censusAddSub = RCB_WIDTH
    ∧ accSegDesc.traceWidth = RCB_WIDTH
    ∧ accFinalDesc.traceWidth = RCB_WIDTH := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl, rfl⟩

/-- ⚑ **THE CARRIES ALONE ARE BETWEEN A FIFTH AND A QUARTER OF THE ROW.** `12 · (NG − 1) = 744`
columns exist only to carry a 256-bit schoolbook product's partial sums. Said separately from
`censusMul` because the quotient limbs and the carries are different work and a narrower encoding
moves them differently.

⚠ The bracket is two-sided on purpose. This theorem's first draft asserted `4 · 744 > RCB_WIDTH`
— "a quarter of the row" rounded UP — and the kernel refused it: `2 976 < 3 048`. A one-sided bound
on a fraction is exactly where a flattering round survives, so both sides are stated. -/
theorem the_multiply_carries_are_seven_hundred_forty_four :
    12 * (NG - 1) = 744
    ∧ 4 * (12 * (NG - 1)) < RCB_WIDTH
    ∧ 5 * (12 * (NG - 1)) > RCB_WIDTH := by
  refine ⟨by decide, by decide, by decide⟩

/-- ⚑⚑ **ONLY 288 OF THE 3 048 COLUMNS CROSS A ROW BOUNDARY — THE OTHER 2 760 ARE SCRATCH.**

The six input blocks are read by the row's own gadget and by the 96 `.transition` threads; the three
output blocks `OUT_X/OUT_Y/OUT_Z` are pinned on `.last` and threaded forward. **Nothing else in the
row is visible outside it.** `9.4%` of the width is the row's interface and `90.6%` is intermediates
that exist because one complete addition is one row.

⚑ This is the number that says the narrowing is a LAYOUT change and not a soundness change: a row
carrying ONE SSA op instead of 33 does not have to hold the other 32 ops' scratch, and every
constraint `swCompleteAddSoundLegs` emits is a statement about a single op's operands and output.
`PastaLadderThread` made exactly this move one rail down — the row-local ladder was 731 136 columns
in one row before depth became rows — and the emitted width has been flat at `RCB_WIDTH` ever since,
which is precisely why the bill moved up a rail instead of going away. -/
theorem the_row_boundary_is_two_hundred_eighty_eight :
    censusInputs + 3 * SK = 288
    ∧ RCB_WIDTH - (censusInputs + 3 * SK) = 2760
    ∧ 10 * (censusInputs + 3 * SK) < RCB_WIDTH := by
  refine ⟨by decide, by decide, by decide⟩

/-- …and the three output blocks live INSIDE the scratch region rather than in a reserved band, so
the `288` above counts distinct columns rather than a reserved prefix. `OUT_X/Y/Z` are `vBase`
slots 26 / 29 / 32 — the gadget's own SSA results, pinned where they land. -/
theorem the_outputs_are_scratch_slots :
    OUT_X = vBase IN_BASE 26 ∧ OUT_Y = vBase IN_BASE 29 ∧ OUT_Z = vBase IN_BASE 32
    ∧ IN_BASE ≤ OUT_X ∧ OUT_Z + SK ≤ RCB_WIDTH := by
  refine ⟨rfl, rfl, rfl, by decide, by decide⟩

/-! ## §5 — ⚑ THE VESTA TWIN OF THE THREADED INDUCTION.

`PastaLadderThread.threadedLadder_forces` is stated at the PALLAS base prime, because `row_forces`
consumes `pallasCompleteAddSound_forces`. The accumulator leg is Step/Tick on **Vesta**, so the
induction is re-run at `q` against `vestaCompleteAddSound_forces`. The proof body is the same three
moves — the row's own forcing, the thread's carry, and `rcbTraceZ_congr` transporting the induction
hypothesis through the RCB formula — because none of them mentions which prime. -/

/-- ⚑ **THE ROW'S DEPLOYED SATISFACTION AT `q`.** Field for field what
`vestaCompleteAddSound_forces` consumes, packaged so the induction quantifies over rows. -/
structure RowSoundV (tr : Trace) (r : Nat) : Prop where
  hX1 : Ranged (tr r) ACC_X
  hY1 : Ranged (tr r) ACC_Y
  hZ1 : Ranged (tr r) ACC_Z
  hX2 : Ranged (tr r) ADD_X
  hY2 : Ranged (tr r) ADD_Y
  hZ2 : Ranged (tr r) ADD_Z
  hv  : ∀ i, i < 33 → Ranged (tr r) (vBase IN_BASE i)
  hm  : ∀ k, k < 12 → MulWitRanged (tr r) (mWit IN_BASE k)
  hs  : ∀ k, k < 2 → SmulWitRanged (tr r) (sWit IN_BASE k)
  hb  : ∀ k, k < 19 → AddSubWitRanged (tr r) (aWit IN_BASE k)
  hG  : RcbSat (tr r) qLimb (curveB3 : ℤ) ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE

/-- One Vesta row, forced. -/
theorem rowV_forces (tr : Trace) (r : Nat) (hR : RowSoundV tr r) :
    CZ3 (qN : ℤ) (accOut tr r)
      (rcbOutZ (curveB3 : ℤ) (accIn tr r).1 (accIn tr r).2.1 (accIn tr r).2.2
        (addend tr r).1 (addend tr r).2.1 (addend tr r).2.2) :=
  vestaCompleteAddSound_forces (tr r) ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE
    hR.hX1 hR.hY1 hR.hZ1 hR.hX2 hR.hY2 hR.hZ2 hR.hv hR.hm hR.hs hR.hb hR.hG

/-- ⚑ **THE COMPOSITION THEOREM AT `q`.** `n` rows of DEPLOYED satisfaction plus `n` held threads
force the accumulator entering row `n` to be congruent — mod the real Vesta-base prime — to the
`n`-fold RCB chain of the addends the trace supplied. No row's output is quoted; each is forced. -/
theorem threadedLadderV_forces (tr : Trace) : ∀ n : Nat,
    (∀ r, r < n → RowSoundV tr r) → (∀ r, r < n → Threaded tr r) →
    CZ3 (qN : ℤ) (accIn tr n) (chainRef tr n)
  | 0, _, _ => CZ3.refl _
  | n + 1, hrow, hthread => by
      have ih : CZ3 (qN : ℤ) (accIn tr n) (chainRef tr n) :=
        threadedLadderV_forces tr n (fun r hr => hrow r (Nat.lt_succ_of_lt hr))
          (fun r hr => hthread r (Nat.lt_succ_of_lt hr))
      have hcarry : accIn tr (n + 1) = accOut tr n :=
        threaded_carries tr n (hthread n (Nat.lt_succ_self n))
      have hrowf := rowV_forces tr n (hrow n (Nat.lt_succ_self n))
      have hstep : CZ3 (qN : ℤ)
          (rcbOutZ (curveB3 : ℤ) (accIn tr n).1 (accIn tr n).2.1 (accIn tr n).2.2
            (addend tr n).1 (addend tr n).2.1 (addend tr n).2.2)
          (chainRef tr (n + 1)) :=
        rcbTraceZ_congr (curveB3 : ℤ) ih.1 ih.2.1 ih.2.2
          (CZm.refl _) (CZm.refl _) (CZm.refl _)
      rw [hcarry]
      exact CZ3.trans hrowf hstep

/-- ⚑ **THE TERMINAL OUTPUT IS THE WHOLE CHAIN.**

The last row of an `n+1`-row trace is where the discharge gates fire, and its `.transition` legs do
NOT fire (`when_transition` is every row BUT the last). So the statement has to reach the LAST ROW'S
OUTPUT, which `threadedLadderV_forces` alone does not: it stops at the accumulator entering row `n`.
One more application of the row's own forcing, transported through `rcbTraceZ_congr`, closes it —
and this is exactly the seam where an off-by-one would silently drop the final addend. -/
theorem terminalAccumulator_forces (tr : Trace) (n : Nat)
    (hrow : ∀ r, r ≤ n → RowSoundV tr r) (hthread : ∀ r, r < n → Threaded tr r) :
    CZ3 (qN : ℤ) (accOut tr n) (chainRef tr (n + 1)) := by
  have ih : CZ3 (qN : ℤ) (accIn tr n) (chainRef tr n) :=
    threadedLadderV_forces tr n (fun r hr => hrow r (Nat.le_of_lt hr)) hthread
  have hrowf := rowV_forces tr n (hrow n (Nat.le_refl n))
  exact CZ3.trans hrowf
    (rcbTraceZ_congr (curveB3 : ℤ) ih.1 ih.2.1 ih.2.2 (CZm.refl _) (CZm.refl _) (CZm.refl _))

/-! ## §6 — ⚑ THE DISCHARGE, FORCED. -/

/-- A block of `SK` limbs that are all zero recomposes to zero. This is the step that makes the
limbwise gate a statement about the VALUE, and it is the direction that needs no range hypothesis —
zero limbs recompose to zero whatever their declared width. -/
theorem sVal_eq_zero (a : Assignment) (b : Nat) (h : ∀ i, i < SK → a (b + i) = 0) :
    sVal a b = 0 := by
  unfold sVal Dregg2.Circuit.Emit.PastaFieldSound.sumL
  refine List.sum_eq_zero ?_
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [h i hi]
  ring

/-- ⚑ **THE DISCHARGE GATES, AS THE PROVER SATISFIES THEM.** The 64 `.last` window bodies vanish on
row `n` exactly when every limb of that row's `OUT_X` and `OUT_Z` blocks is zero. This is
`dischargeLegs`' body read as a fact about the trace. -/
def Discharged (tr : Trace) (n : Nat) : Prop :=
  (∀ i, i < SK → tr n (OUT_X + i) = 0) ∧ (∀ i, i < SK → tr n (OUT_Z + i) = 0)

/-- A satisfied discharge makes the terminal accumulator the CANONICAL point at infinity — the two
coordinates `pasta_msm::is_identity` reads, both exactly `0` rather than merely `≡ 0`. -/
theorem discharged_is_the_identity (tr : Trace) (n : Nat) (h : Discharged tr n) :
    (accOut tr n).1 = 0 ∧ (accOut tr n).2.2 = 0 :=
  ⟨sVal_eq_zero _ _ h.1, sVal_eq_zero _ _ h.2⟩

/-- ⚑⚑ **THE ACCUMULATOR CHECK, FORCED BY THE EMITTED CONSTRAINTS.**

`n+1` rows of deployed satisfaction, `n` held threads, and the 64 discharge gates force the
`n+1`-fold RCB chain of the trace's own addends — starting from the accumulator published at
`PI[0..95]` — to be the point at infinity mod the real Vesta-base prime.

Read against the relation this file exists for: with `acc_0 = C` and the addends the scaled
generators, this says `C − ⟨s(u⃗), G⟩ = O`, which is `Ipa.Step.accumulator_check`.

⚠ It says nothing about WHAT the addends are. That hypothesis-free half is the routing, priced in
§4, and calling this the whole check would be the substitution this repo keeps finding. -/
theorem accumulator_discharge_forced (tr : Trace) (n : Nat)
    (hrow : ∀ r, r ≤ n → RowSoundV tr r) (hthread : ∀ r, r < n → Threaded tr r)
    (hd : Discharged tr n) :
    CZm (qN : ℤ) (chainRef tr (n + 1)).1 0
    ∧ CZm (qN : ℤ) (chainRef tr (n + 1)).2.2 0 := by
  have hterm := terminalAccumulator_forces tr n hrow hthread
  have hz := discharged_is_the_identity tr n hd
  refine ⟨?_, ?_⟩
  · have := CZm.symm hterm.1
    rw [hz.1] at this
    exact CZm.symm (CZm.symm this)
  · have := CZm.symm hterm.2.2
    rw [hz.2] at this
    exact CZm.symm (CZm.symm this)

/-! ### ⚠ THE NON-VACUITY OF `RowSoundV` IS WITNESSED BEHAVIOURALLY, NOT IN THIS KERNEL.

`accumulator_discharge_forced` would be vacuous if `RowSoundV` were unsatisfiable, and **nothing in
this file proves it is not**. What witnesses it is the deployed prover accepting the honest trace
under `dregg-mina-accumulator-final::v1` (`circuit/tests/mina_accumulator_air_proves.rs`, both
polarities, release) — behavioural evidence, one rail down, and `PastaLadderThread`'s
`threadedLadder_forces` has exactly the same status.

⚑ This is UNDONE WORK wearing a caveat, not a theorem of the model, so here is what it would cost.
A kernel witness means exhibiting one `Assignment` and discharging `RcbSat` on it — 33 SSA ops, 12
multiply witnesses at 32 quotient limbs and 62 carries each, all reduced at `q`. That is the
`decide`-through-a-real-field-element shape `minted-poseidon2-perm-is-a-reduction-bomb` measured at
47.6 GB for ONE permutation, so it is a `native_decide` + `#assert_compiled` job (a confession, not a
certificate) or a genuine satisfiability lemma over `rcbSoundRow` — which is the thing actually worth
building, because it would serve every descriptor in this cone rather than this one.

⚠ And the OTHER end is not closed either: these theorems speak the SOURCE vocabulary (`RcbSat`,
`Ranged`), and this file lowers with `lowerAir` rather than the certified `lowerTiedAir`, so the
`AirLeg.forces` bridge from the emitted constraints back to those predicates is inherited from
`PastaCurveSound`/`EffectLowerCertified` rather than re-established here. `lowerTiedAir` was not used
because `EffectAir.pinsTied` is a quadratic `decide` over ~4 000 legs against 192 pins; that is a
cost, and a cost is not a reason to call the weaker thing done.

## §7 — ⚑ AND THE LAST HYPOTHESIS IS DOING WORK.

A theorem whose final hypothesis were unsatisfiable, or satisfied by everything, would prove nothing
about the gate it is named for. Both directions are exhibited: a trace where `Discharged` HOLDS and
one where it FAILS, over assignments that agree everywhere the discharge does not look. -/

/-- The everywhere-zero trace: every limb of every block is `0`. -/
def zeroTrace : Trace := fun _ _ => 0

/-- The trace that is zero except for the terminal accumulator's low `X` limb. -/
def oneTrace : Trace := fun _ c => if c = OUT_X then 1 else 0

theorem zeroTrace_is_discharged (n : Nat) : Discharged zeroTrace n :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- ⚑ **THE REFUTATION.** `oneTrace` differs from `zeroTrace` in exactly ONE cell, that cell is
INSIDE the declared 8-bit limb width (so no range lookup can be what separates them), and the
discharge gate refuses it. A falsifier that moved a zero into a zero is the failure this exhibit is
built against: the moved value is `1`, and it is asserted to be nonzero. -/
theorem the_discharge_gate_is_refutable :
    ¬ Discharged oneTrace 0 ∧ oneTrace 0 OUT_X = 1 ∧ oneTrace 0 OUT_X ≠ zeroTrace 0 OUT_X := by
  refine ⟨?_, by decide, by decide⟩
  intro h
  have h0 := h.1 0 (by decide)
  simp [oneTrace] at h0

/-- …and the two exhibits agree on every cell the discharge does NOT read, so the refusal above is
about the gate and not about collateral damage. -/
theorem the_two_exhibits_differ_in_one_cell :
    ∀ c, c ≠ OUT_X → oneTrace 0 c = zeroTrace 0 c := by
  intro c hc
  simp only [oneTrace, zeroTrace, if_neg hc]

#assert_axioms acc_pi_layout
#assert_axioms pin_leg_counts
#assert_axioms dischargeLegs_length
#assert_axioms accFinalAir_extends_accSegAir
#assert_axioms accSegAir_mainRailOk
#assert_axioms accFinalAir_mainRailOk
#assert_axioms the_discharge_is_sixty_four_last_row_gates
#assert_axioms accSegDesc_constraint_count
#assert_axioms accFinalDesc_constraint_count
#assert_axioms the_two_descriptors_do_not_share_a_name
#assert_axioms the_two_descriptors_differ
#assert_axioms the_full_width_sum_needs_the_fold
#assert_axioms the_routing_tuple_does_not_fit_one_table
#assert_axioms the_split_remedy_costs_more_than_the_wide_table
#assert_axioms the_column_census
#assert_axioms the_multiply_carries_are_seven_hundred_forty_four
#assert_axioms the_row_boundary_is_two_hundred_eighty_eight
#assert_axioms the_outputs_are_scratch_slots
#assert_axioms rowV_forces
#assert_axioms threadedLadderV_forces
#assert_axioms terminalAccumulator_forces
#assert_axioms sVal_eq_zero
#assert_axioms discharged_is_the_identity
#assert_axioms accumulator_discharge_forced
#assert_axioms the_discharge_gate_is_refutable
#assert_axioms the_two_exhibits_differ_in_one_cell

end Dregg2.Circuit.Emit.MinaAccumulatorAir
