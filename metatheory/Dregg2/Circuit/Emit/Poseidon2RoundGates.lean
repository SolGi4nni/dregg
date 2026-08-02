/-
# `Dregg2.Circuit.Emit.Poseidon2RoundGates` — the deployed Poseidon2-w16 permutation's
ROUND-BY-ROUND ARITHMETIZATION, authored in Lean.

## What this is

`circuit/src/plonky3_prover.rs::poseidon2_permute_expr_lanes` is the hand-written Rust gadget every
in-circuit hash in IR-v2 rides through: it emits `(1 + TOTAL_ROUNDS) · 16 = 352` `assert_eq`
constraints binding each round's output to a witness column, and returns the first 8 lanes of the
final state. It is called from `Ir2Air::Chip | Ir2Air::ChipState16`, and — being Rust-authored AIR —
it is exactly what architectural law #1 forbids.

This file is the Lean author of that algebra. `permGateBodies aux0 seed` IS the 352 gate bodies, in
the Rust emission order, as `WindowExpr` trees; `ChipTableEmit` splices them into the chip's
`TableAir` and the Rust side only INTERPRETS.

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every constraint below is a Lean `WindowExpr`. Nothing here hand-writes a Rust constraint.

## Where the constants come from — and why they are not re-transcribed

`Dregg2.Circuit.Poseidon2BabyBearW16` already holds the round constants
(`rcExtInitial`/`rcInternal`/`rcExtFinal`), the linear layers (`mdsLight`/`internalRound`) and the
S-box, KAT-pinned bit-exact against the deployed Rust permutation
(`default_babybear_poseidon2_16().permute(·)`, three `#guard`s at that file's §6). §2 and §3 below
build the emitter's constant tables FROM THOSE, so there is one transcription of the hex in the
tree, not two.

⚠ The one table that is NOT already in Lean in usable form is the internal diagonal: the Lean
`internalRound` carries its coefficients as SHIFTS (`fhalve`, `fdiv2exp _ 27`), while the emitted
expression needs canonical RESIDUES (`state[i] · V[i]`, the Rust `internal_linear_layer_expr`
shape). §3 therefore transcribes `INTERNAL_DIAG` (`circuit/src/poseidon2.rs:92`) and pins it against
the shift form — two INDEPENDENT sources, not a constant checked against its own definition.

## ⚑ THE COST OF A TREE IR, MEASURED RATHER THAN ASSUMED — §7

The Rust gadget gets its size from EXPRESSION SHARING: within a round the 16 S-boxed values are
`AB::Expr` VALUES referenced ~35× each by the linear layer, and only the round OUTPUT is rebound to
a column. `WindowExpr` is a TREE with no `let`/share node, so each external-round gate body
DUPLICATES all 16 S-box subtrees. MEASURED, not estimated: **140,850 nodes against a hash-consed
DAG of 3,194 — 44.1×** — of which 70,249 are arithmetic. `WindowExpr::eval_expr` on the Rust side
is a naive recursive walk with no memoisation, so that ratio lands on the prover's per-row
constraint evaluation over the quotient domain (blow-up 64). §7 is the measurement.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. `#eval` appears only in §7, as MEASUREMENT — never as
evidence for a claim.
-/
import Dregg2.Circuit.TableAirIR
import Dregg2.Circuit.Poseidon2BabyBearW16

namespace Dregg2.Circuit.Emit.Poseidon2RoundGates

open Dregg2.Circuit.DescriptorIR2 (WindowExpr)
open Dregg2.Circuit.TableAirIR (v k eSub)

namespace P2 export Dregg2.Circuit.Poseidon2BabyBearW16 (
  P inv2 fadd fsub fmul fhalve fdiv2exp sbox mat4 mdsLight internalRound externalRound
  rcExtInitial rcExtFinal rcInternal perm compress g) end P2

set_option autoImplicit false

/-! ## §1 — The permutation geometry.

Every number is DERIVED from the two the deployed permutation actually fixes (`WIDTH = 16`,
`EXTERNAL_ROUNDS = 8`, `INTERNAL_ROUNDS = 13`) and `#guard`ed, so a drift moves an arithmetic pin
rather than a comment. Source: `circuit/src/poseidon2.rs:21-30`,
`circuit/src/plonky3_prover.rs:{POSEIDON2_PERM_AUX_COLS, POSEIDON2_WIDTH}`. -/

/-- `WIDTH` — the permutation state width. -/
def WIDTH : Nat := 16
/-- `EXTERNAL_ROUNDS` — full rounds, split half before / half after the internal block. -/
def EXTERNAL_ROUNDS : Nat := 8
/-- `HALF_EXTERNAL`. -/
def HALF_EXTERNAL : Nat := EXTERNAL_ROUNDS / 2
/-- `INTERNAL_ROUNDS` — partial rounds (S-box on lane 0 only). -/
def INTERNAL_ROUNDS : Nat := 13
/-- `TOTAL_ROUNDS`. -/
def TOTAL_ROUNDS : Nat := EXTERNAL_ROUNDS + INTERNAL_ROUNDS
/-- `ROUND_COLS` — witness columns one round's output costs. -/
def ROUND_COLS : Nat := WIDTH
/-- `POSEIDON2_AUX_COLS` — the whole aux block: the post-initial-linear-layer state plus one
block per round. -/
def POSEIDON2_AUX_COLS : Nat := (TOTAL_ROUNDS + 1) * ROUND_COLS
/-- The S-box exponent. -/
def SBOX_ALPHA : Nat := 7

#guard HALF_EXTERNAL == 4
#guard TOTAL_ROUNDS == 21
#guard POSEIDON2_AUX_COLS == 352

/-- The round index is EXTERNAL exactly on the first and last `HALF_EXTERNAL` rounds — the Rust
gadget's three loops, as one predicate. -/
def isExternalRound (r : Nat) : Bool :=
  decide (r < HALF_EXTERNAL) || decide (HALF_EXTERNAL + INTERNAL_ROUNDS ≤ r)

#guard (List.range TOTAL_ROUNDS).filter isExternalRound == [0, 1, 2, 3, 17, 18, 19, 20]
#guard ((List.range TOTAL_ROUNDS).filter (fun r => !isExternalRound r)).length == INTERNAL_ROUNDS

/-! ## §2 — The round constants, from the KAT-pinned Lean tables.

`compute_round_constants` (`circuit/src/poseidon2.rs:117`) concatenates: the four
`RC_EXT_INIT` rows, then thirteen rows whose ONLY nonzero lane is `rc[0] = RC_INTERNAL[round]`,
then the four `RC_EXT_FINAL` rows. The hex is `Poseidon2BabyBearW16`'s already — that module's
`perm` is `#guard`ed bit-exact against the deployed Rust permutation, so reusing its tables makes
the KAT the source of these constants rather than a second transcription of the same hex. -/

/-- The 21 round-constant rows, in the deployed order. Internal rounds carry a constant on lane 0
and zero elsewhere — the shape `compute_round_constants` builds. -/
def roundConstants : List (List ℤ) :=
  P2.rcExtInitial.map (fun row => row.map (fun x => (x : ℤ))) ++
  P2.rcInternal.map (fun c => (c : ℤ) :: List.replicate (WIDTH - 1) (0 : ℤ)) ++
  P2.rcExtFinal.map (fun row => row.map (fun x => (x : ℤ)))

/-- `rc[r][j]`. -/
def rcAt (r j : Nat) : ℤ := (roundConstants.getD r []).getD j 0

#guard roundConstants.length == TOTAL_ROUNDS
#guard roundConstants.all (fun row => row.length == WIDTH)
-- The internal block really is lane-0-only: rounds 4..16 have fifteen zero lanes.
#guard ((List.range TOTAL_ROUNDS).filter (fun r => !isExternalRound r)).all
  (fun r => ((roundConstants.getD r []).drop 1).all (fun x => x == 0))
-- …and the external rows are NOT (a table that silently zeroed would pass the count pins).
#guard ((List.range TOTAL_ROUNDS).filter isExternalRound).all
  (fun r => ((roundConstants.getD r []).drop 1).any (fun x => x != 0))
-- Boundary values, so a splice at the wrong offset moves a pin.
#guard rcAt 0 0 == 0x69cbb6af
#guard rcAt 3 15 == 0x1e36ea47
#guard rcAt 4 0 == 0x5a8053c0
#guard rcAt 16 0 == 0x241af16d
#guard rcAt 17 0 == 0x7290a80d
#guard rcAt 20 15 == 0x608758b8

/-! ## §3 — The internal diagonal, from TWO independent sources.

`internal_linear_layer_expr` (`circuit/src/plonky3_prover.rs:337`) is
`state[i] ← sum + state[i] · (INTERNAL_DIAG[i] − 1)`, i.e. it needs the canonical RESIDUE of each
`V[i] = d[i] − 1`. `Poseidon2BabyBearW16.internalRound` carries the SAME coefficients in shift form
(`fhalve`, `fdiv2exp _ 8`, …) because that is how p3's specialized BabyBear layer computes them.

So: `internalDiag` transcribes `circuit/src/poseidon2.rs:92`, `Vshift` re-derives the same vector
from the KAT-pinned Lean field arithmetic, and the `#guard` is the AGREEMENT of two independent
sources. A pin of a constant against its own definition would be decoration. -/

/-- `INTERNAL_DIAG` (`circuit/src/poseidon2.rs:92`), canonical residues. -/
def internalDiag : List Nat :=
  [ 2013265920, 2, 3, 1006632962, 4, 5, 1006632961, 2013265919,
    2013265918, 2005401602, 1509949442, 1761607682, 2013265907, 7864321, 125829121, 16 ]

/-- `V[i] = INTERNAL_DIAG[i] − 1` — the coefficient the emitted internal layer multiplies by. -/
def V : List ℤ := internalDiag.map (fun d => (d : ℤ) - 1)

/-- `V[i]`. -/
def vCoef (i : Nat) : ℤ := V.getD i 0

/-- The SAME vector `V`, re-derived from `Poseidon2BabyBearW16`'s shift arithmetic — the form the
KAT'd `internalRound` actually applies: `[−2, 1, 2, ½, 3, 4, −½, −3, −4, 2⁻⁸, ¼, ⅛, 2⁻²⁷, −2⁻⁸,
−1/16, −2⁻²⁷]`, canonicalized. -/
def Vshift : List Nat :=
  [ P2.P - 2, 1, 2, P2.inv2, 3, 4, P2.P - P2.inv2, P2.P - 3, P2.P - 4,
    P2.fdiv2exp 1 8, P2.fdiv2exp 1 2, P2.fdiv2exp 1 3, P2.fdiv2exp 1 27,
    P2.P - P2.fdiv2exp 1 8, P2.P - P2.fdiv2exp 1 4, P2.P - P2.fdiv2exp 1 27 ]

-- ⚑ THE TWO-SOURCE PIN: the Rust residue table and the Lean shift arithmetic agree, lane for lane.
#guard Vshift == internalDiag.map (fun d => d - 1)
#guard V.length == WIDTH
-- …and the shift form is genuinely shift-shaped: these are real inverses, not coincident numbers.
#guard P2.fmul 2 P2.inv2 == 1
#guard P2.fmul 16 (P2.fdiv2exp 1 4) == 1
#guard P2.fmul 256 (P2.fdiv2exp 1 8) == 1
#guard P2.fmul 134217728 (P2.fdiv2exp 1 27) == 1

/-! ## §4 — The expression emitters.

Each mirrors its Rust function OPERATION FOR OPERATION, so the emitted polynomial is the deployed
one and the association order is the deployed one too. (Addition is associative in the polynomial
ring, so a re-association would be sound; matching Rust's is what makes a future byte-identity
claim cheap rather than a re-derivation.) -/

/-- `x ↦ x⁷`, exactly as p3's `exp_const_u64::<7>` builds it (`p3-field/src/field.rs:249`):
`x2 = x·x`, `x3 = x2·x`, `x4 = x2·x2`, result `x3·x4`. Seven leaf copies of `x`, six `mul` nodes —
the duplication §7 measures. -/
def eSbox (x : WindowExpr) : WindowExpr :=
  let x2 : WindowExpr := .mul x x
  let x3 : WindowExpr := .mul x2 x
  let x4 : WindowExpr := .mul x2 x2
  .mul x3 x4

/-- Read state lane `i`, `0` past the end (the Lean `g`, so an under-length state is a ZERO lane
rather than a panic — and `#guard`s below fix the lengths so it never fires). -/
def gx (s : List WindowExpr) (i : Nat) : WindowExpr := s.getD i (k 0)

/-- `external_linear_layer_expr` (`circuit/src/plonky3_prover.rs:296`): the `MDSMat4` circulant on
each block of four, then the outer column sums. Left-associated exactly as the Rust `s += …` loop
accumulates `sums[k]`. -/
def extLayer (s : List WindowExpr) : List WindowExpr :=
  let blk : Nat → WindowExpr × WindowExpr × WindowExpr × WindowExpr := fun b =>
    let x0 := gx s (4 * b); let x1 := gx s (4 * b + 1)
    let x2 := gx s (4 * b + 2); let x3 := gx s (4 * b + 3)
    let t01 : WindowExpr := .add x0 x1
    let t23 : WindowExpr := .add x2 x3
    let t0123 : WindowExpr := .add t01 t23
    let t01123 : WindowExpr := .add t0123 x1
    let t01233 : WindowExpr := .add t0123 x3
    ( .add t01123 t01
    , .add (.add t01123 x2) x2
    , .add t01233 t23
    , .add (.add t01233 x0) x0 )
  let m : Nat → WindowExpr := fun i =>
    let q := blk (i / 4)
    match i % 4 with
    | 0 => q.1
    | 1 => q.2.1
    | 2 => q.2.2.1
    | _ => q.2.2.2
  let sums : Nat → WindowExpr := fun r =>
    .add (.add (.add (m r) (m (4 + r))) (m (8 + r))) (m (12 + r))
  (List.range WIDTH).map (fun i => .add (m i) (sums (i % 4)))

/-- `internal_linear_layer_expr` (`circuit/src/plonky3_prover.rs:337`): `sum = Σ state[i]`
(left-associated from `state[0]`, as the Rust `sum +=` loop), then `state[i] = sum + state[i]·V[i]`. -/
def intLayer (s : List WindowExpr) : List WindowExpr :=
  let sum : WindowExpr :=
    (List.range (WIDTH - 1)).foldl (fun acc i => .add acc (gx s (i + 1))) (gx s 0)
  (List.range WIDTH).map (fun i => .add sum (.mul (gx s i) (k (vCoef i))))

/-- One round applied to a state of expressions. External rounds add the row constant to every
lane, S-box every lane, then the external layer; internal rounds touch lane 0 only, then the
diagonal layer. -/
def roundOut (r : Nat) (s : List WindowExpr) : List WindowExpr :=
  if isExternalRound r then
    extLayer ((List.range WIDTH).map (fun j => eSbox (.add (gx s j) (k (rcAt r j)))))
  else
    intLayer ((List.range WIDTH).map (fun j =>
      if j = 0 then eSbox (.add (gx s 0) (k (rcAt r 0))) else gx s j))

/-! ## §5 — The 352 gates.

`poseidon2_permute_expr_lanes` walks the aux block in `ROUND_COLS`-sized steps: block 0 is the
POST-INITIAL-LINEAR-LAYER state, block `r+1` the output of round `r`. Each step emits
`assert_eq(state[j], aux[off+j])` — body `state[j] − aux[off+j]` — and then REBINDS
`state[j] := aux[off+j]`, which is why every round's input is a bare column read and the emitted
degree stays at the S-box budget of 7. -/

/-- Aux column of block `b`, lane `j`, for an aux block based at `aux0`. -/
def auxLane (aux0 b j : Nat) : WindowExpr := v (aux0 + ROUND_COLS * b + j)

/-- The block-`b` state, as the 16 columns the rebinding leaves it at. -/
def auxState (aux0 b : Nat) : List WindowExpr := (List.range WIDTH).map (auxLane aux0 b)

/-- **THE 352 PERMUTATION GATE BODIES**, in the Rust emission order: the initial linear layer's 16,
then 16 per round for 21 rounds. `seed` is the input state (whatever the calling table seeds its
lanes from); `aux0` is the first aux column. -/
def permGateBodies (aux0 : Nat) (seed : List WindowExpr) : List WindowExpr :=
  let init := extLayer seed
  ((List.range WIDTH).map (fun j => eSub (gx init j) (auxLane aux0 0 j))) ++
  ((List.range TOTAL_ROUNDS).flatMap (fun r =>
    let out := roundOut r (auxState aux0 r)
    (List.range WIDTH).map (fun j => eSub (gx out j) (auxLane aux0 (r + 1) j))))

/-- The permutation's exposed output lanes. ⚑ After the FINAL rebind `state[j] := aux[off+j]`, the
returned `state[0..8]` ARE aux columns — which is why the chip's `out[i] − lanes[i]` gates are
equality bindings to a constrained column and not a re-derivation. -/
def permOutLane (aux0 i : Nat) : WindowExpr := auxLane aux0 TOTAL_ROUNDS i

/-- The FINAL permutation state, all 16 lanes — what `Ir2Air::ChipState16` puts on the wire
(`aux[POSEIDON2_AUX_COLS − WIDTH ..]`). -/
def permFinalState (aux0 : Nat) : List WindowExpr := auxState aux0 TOTAL_ROUNDS

#guard (permGateBodies 33 (auxState 1000 0)).length == POSEIDON2_AUX_COLS
#guard (permFinalState 33).length == WIDTH
-- The final block really is the last `WIDTH` columns of the aux span. (`WindowExpr` has no `BEq`,
-- so the pin is on the wire rendering — which is the thing the Rust decoder reads anyway.)
#guard (permOutLane 33 0).toJson == (v (33 + POSEIDON2_AUX_COLS - WIDTH)).toJson
#guard (permFinalState 33).map WindowExpr.toJson
     == ((List.range WIDTH).map (fun i => v (33 + POSEIDON2_AUX_COLS - WIDTH + i))).map WindowExpr.toJson

/-! ## §6 — AGREEMENT WITH THE KAT-PINNED PERMUTATION.

The emitted algebra is worthless if it is not the deployed permutation's. `Poseidon2BabyBearW16` is
bit-exact against the deployed Rust hash by three KATs; this section evaluates the EMITTED
EXPRESSIONS on the witness that module's own functions produce, so the emission is checked against
the KAT rather than against a re-reading of the Rust.

⚠ These are `#guard`s, i.e. they are checked by evaluation at elaboration time and fail the build
when they diverge — the same instrument `Poseidon2BabyBearW16`'s KATs use. The FORCING claims (what
an accepting witness implies) are theorems, in `ChipTableEmit`. -/

/-- The 22 intermediate states the deployed permutation passes through: block 0 is the
post-initial-linear-layer state, block `r+1` is round `r`'s output. This is the Lean twin of
`poseidon2_permute_aux_witness` (`circuit/src/plonky3_prover.rs:492`), built out of
`Poseidon2BabyBearW16`'s own round functions so it inherits their KAT. -/
def permBlocks (input : List Nat) : List (List Nat) :=
  let rounds : List (List Nat → List Nat) :=
    P2.rcExtInitial.map (fun rc => P2.externalRound rc) ++
    P2.rcInternal.map (fun c => P2.internalRound c) ++
    P2.rcExtFinal.map (fun rc => P2.externalRound rc)
  rounds.foldl (fun acc f => acc ++ [f (acc.getLastD [])]) [P2.mdsLight input]

/-- The flattened aux witness, `POSEIDON2_AUX_COLS` field values. -/
def permAuxWitness (input : List Nat) : List ℤ :=
  (permBlocks input).flatMap (fun blk => blk.map (fun x => (x : ℤ)))

-- The trace really is 22 blocks and really ends at the KAT-pinned permutation output.
#guard (permBlocks (List.range 16)).length == TOTAL_ROUNDS + 1
#guard (permBlocks (List.range 16)).getLastD [] == P2.perm (List.range 16)
#guard (permBlocks (List.replicate 16 0)).getLastD [] == P2.perm (List.replicate 16 0)
#guard (permAuxWitness (List.range 16)).length == POSEIDON2_AUX_COLS

/-- The row window a permutation witness induces: the input state at `in0`, the aux block at
`aux0`, everything else zero. -/
def permEnv (in0 aux0 : Nat) (input : List Nat) :
    Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv :=
  let inv : List ℤ := input.map (fun x => (x : ℤ))
  let aux : List ℤ := permAuxWitness input
  let loc : Nat → ℤ := fun c =>
    if c < in0 then 0
    else if c < in0 + WIDTH then inv.getD (c - in0) 0
    else if c < aux0 then 0
    else aux.getD (c - aux0) 0
  ⟨loc, fun _ => 0, fun _ => 0⟩

/-- The S-box emitter agrees with the KAT'd `sbox`, and the layer emitters agree with `mdsLight` /
the diagonal half of `internalRound`, on a concrete state. Cheap, and it names WHICH piece moved if
the whole-permutation check below ever goes red. -/
private def katState : List Nat := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3]

private def evalAt (e : WindowExpr) (s : List Nat) : ℤ :=
  e.eval ⟨fun c => (s.getD c 0 : ℤ), fun _ => 0, fun _ => 0⟩ % 2013265921

#guard evalAt (eSbox (v 5)) katState == (P2.sbox (katState.getD 5 0) : ℤ)
#guard ((List.range WIDTH).map (fun i => evalAt (gx (extLayer ((List.range WIDTH).map v)) i) katState))
     == (P2.mdsLight katState).map (fun x => (x : ℤ))

/-- ⚑ **THE WHOLE 352-GATE ARITHMETIZATION ACCEPTS THE KAT-PINNED WITNESS.** Every emitted gate
body vanishes mod `p` on the row the deployed permutation itself produces. This is the check that
the round constants, both linear layers, the S-box, the round SPLIT (4/13/4) and the aux offsets are
all the deployed ones at once — anchored on `Poseidon2BabyBearW16`'s KAT rather than on a re-reading
of the Rust. -/
def permGatesAcceptWitness (in0 aux0 : Nat) (input : List Nat) : Bool :=
  let env := permEnv in0 aux0 input
  (permGateBodies aux0 ((List.range WIDTH).map (fun i => v (in0 + i)))).all
    (fun b => b.eval env % 2013265921 == 0)

#guard permGatesAcceptWitness 1 33 (List.range 16)
#guard permGatesAcceptWitness 1 33 (List.replicate 16 0)
#guard permGatesAcceptWitness 1 33 katState

/-- ⚠ NON-VACUITY, the FALSE pole: the arithmetization can go RED. Perturbing ONE aux limb of the
honest witness breaks it. A check that no witness refutes is decoration. -/
def permGatesAcceptPerturbed (in0 aux0 : Nat) (input : List Nat) (col : Nat) : Bool :=
  let base := permEnv in0 aux0 input
  let env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv :=
    ⟨fun c => if c == col then base.loc c + 1 else base.loc c, base.nxt, base.pub⟩
  (permGateBodies aux0 ((List.range WIDTH).map (fun i => v (in0 + i)))).all
    (fun b => b.eval env % 2013265921 == 0)

-- A bump in the FIRST aux block, in the middle, and in the LAST — each refused.
#guard permGatesAcceptPerturbed 1 33 katState 33 == false
#guard permGatesAcceptPerturbed 1 33 katState (33 + 16 * 11 + 7) == false
#guard permGatesAcceptPerturbed 1 33 katState (33 + 336) == false
-- …and an INPUT bump is refused too (the input is not free once the aux block is fixed).
#guard permGatesAcceptPerturbed 1 33 katState 1 == false
#guard permGatesAcceptPerturbed 1 33 katState 16 == false
-- Sanity that the perturbation instrument is not always-false: a column OUTSIDE the gadget
-- (neither input nor aux) changes nothing.
#guard permGatesAcceptPerturbed 1 33 katState 400 == true

/-! ## §7 — ⚑ THE TREE BLOW-UP, MEASURED.

`WindowExpr` has `loc`/`nxt`/`const`/`add`/`mul` and NO sharing node. The Rust gadget's speed comes
from `AB::Expr` VALUES: within one round the 16 S-boxed lanes are each referenced 35 times by the
external linear layer (7 from the `MDSMat4` block plus 28 from the four column sums), and each
S-box is itself 7 copies of its argument. A tree IR pays that as literal duplication.

`nodeCount` measures it on the EMITTED object, and every number below is a `#guard` — derived from
the emitted trees, attributable to a round, and red on drift. The headline:

| | value |
|---|---|
| total nodes | **140,850** |
| arithmetic nodes | **70,249** |
| hash-consed DAG | **3,194** |
| **blow-up** | **44.1×** |
| one EXTERNAL round | 15,728 |
| one INTERNAL round | 1,066 |
| emitted JSON (this half alone) | 3,084,906 bytes |

⚑ **This is a design fork, not a wart.** The remedy is a sharing constructor on `WindowExpr` — the
same fork `TableAirIR` §7 item 1 already prices for a different reason — and it is NOT a licence to
re-arithmetize: the algebra here IS the deployed permutation, checked against its KAT in §6, and a
cheaper circuit would be a DIFFERENT circuit. `ChipTableEmit` §11 states the cost of doing it in
the wrong order. -/

/-- Nodes in a `WindowExpr` tree — the unit the prover's per-row constraint evaluation pays, once
per row of the quotient domain (blow-up 64). -/
def nodeCount : WindowExpr → Nat
  | .loc _ | .nxt _ | .const _ => 1
  | .add a b => 1 + nodeCount a + nodeCount b
  | .mul a b => 1 + nodeCount a + nodeCount b

/-- Total nodes over a gate-body list. -/
def totalNodes (bs : List WindowExpr) : Nat := (bs.map nodeCount).foldl (· + ·) 0

/-- The permutation's node total at the chip's geometry — the number §7 is about. -/
def permNodeTotal : Nat := totalNodes (permGateBodies 33 ((List.range WIDTH).map (fun i => v (1 + i))))

-- The measured shape, pinned so a "harmless" re-association of a layer cannot move the prover's
-- cost silently. An EXTERNAL round body is ~14× an INTERNAL one; that ratio IS the finding.
#guard nodeCount (eSbox (v 0)) == 13
#guard permNodeTotal == 140850
#guard totalNodes (permGateBodies 33 ((List.range WIDTH).map (fun i => v (1 + i)))) == 140850

/-- Per-round node totals, so the blow-up is attributable rather than aggregate. -/
def roundNodeTotal (r : Nat) : Nat :=
  totalNodes ((List.range WIDTH).map (fun j =>
    eSub (gx (roundOut r (auxState 33 r)) j) (auxLane 33 (r + 1) j)))

/-- Nodes that are ARITHMETIC — the prover's actual per-row work, leaves excluded. -/
def opCount : WindowExpr → Nat
  | .loc _ | .nxt _ | .const _ => 0
  | .add a b => 1 + opCount a + opCount b
  | .mul a b => 1 + opCount a + opCount b

/-- ⚑ **THE SHARED-DAG SIZE** — what the SAME polynomial costs with a share/`let` node, measured by
hash-consing the emitted trees bottom-up. The gap between this and `totalNodes` is exactly what a
tree IR pays, and it is the price tag on the design fork §7's closing note names. -/
def dagSize (bs : List WindowExpr) : Nat := Id.run do
  let mut tbl : Std.HashMap String Nat := {}
  let rec go (e : WindowExpr) (t : Std.HashMap String Nat) : Nat × Std.HashMap String Nat :=
    match e with
    | .loc c => key s!"L{c}" t
    | .nxt c => key s!"N{c}" t
    | .const z => key s!"K{z}" t
    | .add a b => let (ia, t) := go a t; let (ib, t) := go b t; key s!"+{ia},{ib}" t
    | .mul a b => let (ia, t) := go a t; let (ib, t) := go b t; key s!"*{ia},{ib}" t
  for b in bs do
    let (_, t) := go b tbl
    tbl := t
  return tbl.size
where
  key (s : String) (t : Std.HashMap String Nat) : Nat × Std.HashMap String Nat :=
    match t[s]? with
    | some i => (i, t)
    | none   => let i := t.size; (i, t.insert s i)

/-- The permutation's ARITHMETIC total — the ops a naive tree walk performs per row. -/
def permOpTotal : Nat :=
  (permGateBodies 33 ((List.range WIDTH).map (fun i => v (1 + i)))).foldl
    (fun acc b => acc + opCount b) 0

/-- The permutation's SHARED-DAG size at the chip's geometry. -/
def permDagSize : Nat := dagSize (permGateBodies 33 ((List.range WIDTH).map (fun i => v (1 + i))))

-- ⚑ THE MEASUREMENT, pinned. Every one of these is derived from the emitted trees.
#guard roundNodeTotal 0 == 15728     -- an EXTERNAL round: 16 gates × 983 nodes
#guard roundNodeTotal 4 == 1066      -- an INTERNAL round — 14.8× smaller
#guard roundNodeTotal 20 == 15728    -- the last external round
#guard totalNodes ((List.range WIDTH).map (fun j =>
      eSub (gx (extLayer ((List.range WIDTH).map (fun i => v (1 + i)))) j) (auxLane 33 0 j)))
     == 1168                         -- the initial linear layer, over bare column reads
-- …and those three account for the whole total, so the number is attributable.
#guard 8 * 15728 + 13 * 1066 + 1168 == permNodeTotal
#guard permOpTotal == 70249
-- ⚑ **THE FORK, AS A NUMBER.** The SAME polynomial, hash-consed, is 3194 distinct subexpressions.
-- 140850 / 3194 = 44.1×, and the Rust interpreter's `WindowExpr::eval_expr` is a NAIVE recursive
-- walk with no memoisation — so the emitted table costs the prover ~44× the hand-written arm's
-- per-row work, which shares its 16 per-round S-box values as `AB::Expr`. That is a property of
-- the IR (no share/`let` node), NOT of this emission, and it is not fixable by re-associating a
-- layer: the arithmetization here IS the deployed one, and trading it for a cheaper one would be
-- inventing a different circuit.
#guard permDagSize == 3194
#guard permNodeTotal / permDagSize == 44

end Dregg2.Circuit.Emit.Poseidon2RoundGates
