/-
# Dregg2.Circuit.Emit.KimchiWrapMainFixture — the pinned INSTANCES the §11–§24 pins measure.

⚑ **ONE MODULE OF THE `KimchiWrapMain` SPLIT.** The namespace is unchanged
(`Dregg2.Circuit.Emit.KimchiWrapMain`), so nothing here is renamed and no consumer moves; the file
boundary exists only so a pin re-elaborates without the emitter's 5,000 lines of `def` behind it.
The in-file rule that keeps it stable is the step side's: **a `def` goes in `…Core`/`…Fixture`, a
pin goes in its section's `…PinsNN`.**

⚠ The `set_option` block below is VERBATIM `KimchiWrapMain`'s and must stay that way. `set_option`
does not cross an import, and `KimchiWrapFinalizeSpongeGate` shipped four proofs as `sorryAx` --
each still landing in the environment with the right statement -- because a split dropped it.

Every `def` that lived among the pins: the smoke instance (`tW`, `rowsW`, `gatesW`, `placedW`,
`gridW`), the real accepted proof's tape and its bent control, and the per-section subjects. They are
here rather than in their sections because more than one `…PinsNN` reads them, and a nullary `def`
evaluated once is the whole reason the pins are affordable at all.

-/
import Dregg2.Circuit.Emit.KimchiWrapMainCore

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

set_option autoImplicit false
set_option maxRecDepth 100000
-- ⚠ §12/§14b reduce whole sponge trajectories IN THE KERNEL (`rfl`/`decide`), which is strictly
-- stronger than the `#guard`s they replace and correspondingly slower to elaborate.
set_option maxHeartbeats 4000000

def tW : WrapData := mkWrap shapeSmoke
def rowsW : List WRow := rungRows tW .bind true
def rowsUW : List WRow := rungRows tW .bind false
def nRowsW : Nat := rowsW.length
def gatesW : List PGate := wrapGates rowsW
def placedW : List PlacedGate := placedOf shapeSmoke .bind (rungPub shapeSmoke .bind) gatesW
/-- ⚑ At `.bind`, not at the closing rung: `rowsW` IS the `w4_bind` row list, and asking for the
`w6_xhat` environment here would make every §12 guard reduce §15's ladders for cells no `w4_bind`
row has. That is the measurement that cost this module its build. -/
def gridW : List (List Int) := wrapWitnessAt tW .bind (rungPub shapeSmoke .bind) rowsW

/-- The real proof's absorb/squeeze schedule (`verifier.rs:159-283`): the tape, β, γ, `z_comm`, α′,
`t_comm`, ζ′, digest. -/
def realTapeSchedule : List Ev :=
  (Dregg2.Circuit.Emit.PastaPoseidonFq.fqTape).map (fun w => Ev.abs T_WCOMM w)
  ++ [ Ev.sq .chal, Ev.sq .chal ]
  ++ (Dregg2.Circuit.Emit.PastaPoseidonFq.ZCOMM_XY).map (fun w => Ev.abs T_ZCOMM w)
  ++ [ Ev.sq .chal ]
  ++ (Dregg2.Circuit.Emit.PastaPoseidonFq.TCOMM_XY).map (fun w => Ev.abs T_TCOMM w)
  ++ [ Ev.sq .chal, Ev.sq .full ]

def realRun : SpAcc := runSpongeQ 0 realTapeSchedule 99999 0
/-- β, γ, α′, ζ′ — the four `chal` squeezes, low 128 bits. -/
def realChals : List Nat := (chalSqueezes realRun).map (fun e => e.2 % 2 ^ 128)
/-- the phase-1 digest — the FULL squeeze. -/
def realDigest : Nat :=
  ((realRun.evs.filter (fun e => !e.isAbs && e.kind == SqKind.full)).map (fun e => e.val)).headD 0

/-- ⚑ RED CONTROL. Bending ONE absorbed word of that tape moves ALL FOUR challenges and the digest
— which is what makes the pins above a measurement of the derivation rather than of five
constants. -/
def realBent : SpAcc :=
  runSpongeQ 0 realTapeSchedule 3 (qAdd (Dregg2.Circuit.Emit.PastaPoseidonFq.fqTape.getD 3 0) 1)
def realBentChals : List Nat := (chalSqueezes realBent).map (fun e => e.2 % 2 ^ 128)
/-- The same chain at a bent seed `n₀ = 1` decodes a DIFFERENT scalar. -/
def seedBentN : Nat :=
  let cr := crumbsOfQ shapeSmoke 12345
  cr.foldl (fun acc x => (4 * acc + x) % qN) 1
def seedHonestN : Nat := ((emsAccsQ shapeSmoke 12345).getD shapeSmoke.emsRows (0, 2, 2)).1
/-- …and the emitted rows DO pin all three: `n₀ = 0` and `a₀ = 2` on one row, `b₀ = 2` on the next. -/
def seedRow0 : List Int :=
  ((tfcRowsQ shapeSmoke 0 (chainVars shapeSmoke 100 0) (.external 1) true 12345 true).getD 0
     default).coeffs
def seedRow1 : List Int :=
  ((tfcRowsQ shapeSmoke 0 (chainVars shapeSmoke 100 0) (.external 1) true 12345 true).getD 1
     default).coeffs
/-- A real squeeze off the smoke transcript, and the honest split. -/
def sqSample : Nat := ((chalSqueezes tW.sp).getD 0 (.external 0, 0)).2
def hiHonest : Nat := sqSample / 2 ^ CHAL_BITS shapeSmoke
def loHonest : Nat := sqSample % 2 ^ CHAL_BITS shapeSmoke
/-- A FORGED low part. `util.ml:100` stays satisfiable because `hi' = (x − lo')·2^{−128}` always
exists in `Fq` — `2^128` is a unit — so the decomposition row alone constrains NOTHING about which
128-bit value `lo` is. -/
def loForged : Nat := (loHonest + 12345) % 2 ^ CHAL_BITS shapeSmoke
/-- ⚑ …and the transcript's dependence on them is REAL: bending one absorbed word moves every later
challenge. That is the property an absorbed-but-unconsumed word still has, and it is the only one. -/
def tBent : WrapData := mkWrapWith shapeSmoke 5 (qAdd (itemVal T_WCOMM 0) 7)
def sqEvts : List SpEvt := tW.sp.evs.filter (fun e => !e.isAbs)
def forkEvt : SpEvt := (tW.sp.evs.filter (fun e => !e.isAbs && e.kind == SqKind.fork)).getD 0 default
def censusW : List (KGateType × Nat) :=
  [KGateType.zero, .generic, .poseidon, .completeAdd, .varBaseMul, .endoMul, .endoMulScalar].map
    (fun k => (k, (rowsW.filter (fun r => r.kind == k)).length))
/-- The smoke instance, materialised once so the interpreter and the kernel share one term. -/
def tKey : WrapData := mkWrap shapeSmoke

/-- The smoke instance's W-XHAT rows, materialised once so the pins share one term. -/
def xhRows : List WRow := xhatRows tKey true

/-- Does the emitted row list contain the `Generic` constant pin `vx = p.1`, `vy = p.2`?

⚑ Deliberately compares `kind` / `perm` / `coeffs` and NOT the whole row. `WRow` carries the
`advice` cells, and a structural equality on a `CompleteAdd` row forces `caWitnessQ` — three `qInv`
apiece — for every row against every candidate. Written as `List.contains` this one theorem took the
file from 150 s and ~1 GB to 9.7 GB and unfinished. The pin is about the CONSTRAINT, and the
constraint is the gate kind, the wires and the coefficients. -/
def xhHasConstRow (vx vy : PVar) (p : Nat × Nat) : Bool :=
  let r := ptConstRow vx vy p
  xhRows.any (fun w => w.kind == r.kind && w.perm == r.perm && w.coeffs == r.coeffs)

/-- The smoke instance's W-SPLIT rows, materialised once so the pins share one term. -/
def spRows : List WRow := splitRows tKey true



/-- W-PREV's own row-set at the smoke shape. ⚑ Same `WrapData` as §14b/§15f/§16b's — the rungs share
one shape and one sponge trajectory; a second `mkWrap` here would re-run the whole transcript. -/
def tPrev : WrapData := tKey
def prRows : List WRow := prevRows tPrev true

/-- ⚑ Does `rows` carry the `Generic` HALF `(vs, c)` — in EITHER slot of the double gate?
`packHalves` fills cols 0,1,2 with the first half and 3,4,5 with the second, so a pin written
against `perm.take 3` alone would silently miss every half that landed in the second slot. It is the
HALF that is the constraint, and both slots are the same constraint. -/
def hasHalf (rows : List WRow) (vs : List (Option PVar)) (c : List Int) : Bool :=
  rows.any (fun w => w.kind == KGateType.generic
    && ((w.perm.take 3 == vs && w.coeffs.take 5 == c)
        || ((w.perm.drop 3).take 3 == vs && (w.coeffs.drop 5).take 5 == c)))

/-- Recompose an MSB-first bit list, exactly as the `EC_scale` gate's `n_acc` chain does
(`plonk_curve_ops.ml:174-177`: `n' = 2n + b`, five bits per row). -/
def ftcRecompose (bs : List Nat) : Nat := bs.foldl (fun a b => 2 * a + b) 0

def tWh : WrapData := tPrev

/-- ⚑ **`w12_close`'s WHOLE ROW LIST AND ITS GATES, MATERIALISED ONCE** — the same discipline
`xhRows`/`spRows` follow, and it stopped being optional when `.bullet` came under `.close`
(2026-08-05). §22a's pin names the length, the placement, the inert-word check and the region escape;
each of those spelled `rungRows tWh .close true` inline is a SEPARATE evaluation of a rung that now
runs `bullData` — 34 + 33 endo ladders and a 51-chunk `scale_fast` — and `combData`'s 46 more. Four
evaluations of that, plus a second `wrapGates` walk each time, is §7's "computed and discarded" in a
new place. -/
def clRows : List WRow := rungRows tWh .close true
def clGates : List PGate := wrapGates clRows

/-- ⚑ **THE SAME 32 VALUES WITH THE COMMITMENT ABSORBED FIRST** — the order the STEP side uses and
this one does not. It exists only as the red control below; nothing emits it. -/
def whDigestCommitmentFirst (chals : List Nat) (g : Nat × Nat) : Nat :=
  (Dregg2.Circuit.Emit.PastaPoseidonFq.squeeze1 Dregg2.Circuit.Emit.PastaPoseidonFq.fqParams
      (Dregg2.Circuit.Emit.PastaPoseidonFq.absorbMany Dregg2.Circuit.Emit.PastaPoseidonFq.fqParams
        Dregg2.Circuit.Emit.PastaPoseidonFq.newSponge ([g.1, g.2] ++ chals))).2

/-- One `Generic` half's residue at a witness: `c₀w₀ + c₁w₁ + c₂w₂ + c₃w₀w₁ + c₄`
(`generic.rs:283-314`). Two lines, here, so §22's refusal is an ARITHMETIC statement about the
emitted coefficients rather than a restatement of `cConst`'s definition. -/
def genericHalfAt (c : List Int) (w0 w1 w2 : Int) : Int :=
  c.getD 0 0 * w0 + c.getD 1 0 * w1 + c.getD 2 0 * w2 + c.getD 3 0 * w0 * w1 + c.getD 4 0

/-- Every cell rung `k`'s OWN rows mention. `WRow.perm` is the row's variable list, so this is
exactly "what this rung's rows touch" — not what its docstring says they touch. -/
def rungCells (t : WrapData) (k : Rung) : List PVar :=
  (rungOwn t true k).flatMap (fun r => r.perm.filterMap id)

/-- The transcript's `t_comm` absorb cells — the sponge variable each quotient chunk is read into. -/
def tCommCells (t : WrapData) : List PVar :=
  ((t.sp.evs.filter (fun e => e.isAbs && e.tag == T_TCOMM)).map (fun e => e.wordV))

/-- How many of rung `k`'s own cells are `t_comm` transcript cells. -/
def tCommReadsIn (t : WrapData) (k : Rung) : Nat :=
  ((rungCells t k).filter (fun v => (tCommCells t).contains v)).length

/-! ### §20's SUBJECTS — W-FINSPONGE's per-instance data and its own emitted rows.

⚠ Everything below is downstream of `finZW0`, which runs §19's 1047-op probe program to solve the
finalizing block's `z(ζω)`. So a `def` here is affordable to EVALUATE and not to REDUCE, and
`KimchiWrapMainPins12` says which of its pins that costs. -/

/-- Every instance's sponge half at the smoke shape, built ONCE — `finSpRows`, `finSpEnv` and
`finSpDerivedWords` each build this internally, so a pin that wants two of them pays for it twice
unless it comes through here. -/
def finSpDataW : List FinSpData := finSpAll tW (finAll tW)

/-- Instance `p`'s five `Boolean.all` slots as the emission actually witnesses them:
`(xi_correct, b_correct, combined_inner_product_correct, finalized, (1 − finalized)·should_finalize)`. -/
def finSpLegsAt (p : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let d := finSpDataW.getD p default
  ( d.vals.getD d.fp.slots.xc 0
  , d.vals.getD d.fp.slots.bc 0
  , d.vals.getD d.fp.slots.cc 0
  , d.vals.getD d.fp.slots.finalized 0
  , d.vals.getD d.fp.slots.out 0 )

/-- …and the THREE `Field.equal` differences the legs are read off, which is where both branches of
the gadget live: zero on the block that carries the derived words, nonzero on the one that does not. -/
def finSpDiffsAt (p : Nat) : Nat × Nat × Nat :=
  let d := finSpDataW.getD p default
  ( d.vals.getD d.fp.slots.dXi 0
  , d.vals.getD d.fp.slots.dB 0
  , d.vals.getD d.fp.slots.dCip 0 )

/-- W-FINSPONGE's OWN emitted rows at the smoke shape — the rung's row-set, not the ladder's. -/
def finSpRowsW : List WRow := rungOwn tW true .finsponge

end Dregg2.Circuit.Emit.KimchiWrapMain
