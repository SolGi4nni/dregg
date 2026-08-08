/-
# `Dregg2.Circuit.Emit.MinaFinalizeScalars` — ⚑⚑ **`dregg-mina-finalize-scalars::v1`: Pickles'
finalize conjuncts 3 and 4, rendered as a Lean-authored scheduled AIR at the Pallas-scalar prime.**

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every op, every selector leg, every carry mask, every pin below is
authored here and lowered by `EffectLower.lowerAir`. Rust parses the emitted descriptor, fills
cells from the Lean-rendered witness, and runs the deployed prover. It authors no constraint.
House Law #1.

## THE OBJECT — a lowering, not new mathematics

`PicklesFinalize.finalizeOtherProof` is a four-way AND (`step.rs:876-884`):
`xi_correct && b_correct && combined_inner_product_correct && plonk_checks_passed`.
`MinaWrapConjunctionAir` renders conjuncts 1 and 2 and **names 3 and 4 as absent by construction**:

> `cipCorrect` compares the claimed `combined_inner_product` against `cipActualOf`, whose
> `ft_eval0` slot is K5's gate linearization. A gate comparing `cip` against a ξ-fold with a FREE
> `ft_eval0` column would force nothing at all.

This file is those two conjuncts. The bodies already exist at `[CommRing R]` in `KimchiVerify`
(`ftEval0R`, `cipR`, `zkPolyR`) and `PicklesFinalize` (`permScalarR`); what is new here is their
RENDERING as one straight-line program of 301 sound field ops, one op per row, on the scheduled
substrate `PastaCurveScheduled`/`AirCrossRow`/`AirSelectorForcing` built for the RCB row — with
`ft_eval0` COMPUTED (witnessed inverse and all) and fed into the ξ-fold's slot 3, so the fold's
one free input is closed in-AIR.

⚠ **THE SIDE, SAID ONCE MORE.** This is the **Wrap-side** finalize: `ZMod qN`, domain `2^14`,
Tock shifts, the 47-entry `es` order `[bp0, bp1, public, ft, z, sel(6), w(15), coeff(15), σ(6)]`
(`MinaRealBlockGate.EVZ`'s own order, `verifier.rs:492-540`). It is NOT `KimchiStepMainCore`'s
`ftProgOf` (`FT_LOG2N = 16`, Tick, hardcoded `pN`) — porting that object here would be a theorem
about the wrong side.

## ⚑ WHAT THIS LEAF FORCES, AND WHERE EACH FORCING LIVES

Stated per conjunct, at this tree's resolution:

1. **Conjunct 3, `cipCorrect` — IN-AIR** (this descriptor): `CIP_CLAIM ≡ cipR ξ r esZ esW`
   where `esZ`/`esW` are assembled from this trace's own input blocks and the `ft` slot is the
   in-AIR `ftEval0R` value — ζ-power ladder, `zkPolyR`, the witnessed inverse (`den·DINV = 1`
   forced by gate), the two C5 folds, all on this trace's rows. The ONE ported input is `LCT`
   (below).
2. **Conjunct 4, `plonkChecksPassed` — IN-AIR** (this descriptor): `PERM_CLAIM ≡ permScalarR`,
   over the same β, γ, α²¹, ζ-derived `zkPolyR`, the six σ evals and `z(ζω)`. The comparison list
   upstream is `[perm]` (`plonk_checks.rs:363-366`), and that is what is forced.
3. **The eval inputs — AT THE FOLD, not here**: every `EZ_k`/`EW_k`/`FT1`/`PUBZ`/`PUBW` block is
   a PI-pinned PORT of this leaf; the recursion fold `cb.connect`s them elementwise to the
   phase-2 chain links' absorbed pairs (`MinaPhase2Chain.chainPins` publishes each pair at
   `[6·SK, 8·SK)`). Until those connects run, this leaf's statement is "the ξ-fold of the blocks
   this claim names", not "of the block's transcript".
4. **The challenges — AT THE FOLD**: β/γ weld to `MinaPhase1Chain`'s squeezes (low-128 reads:
   in-leaf zero-pins on limbs 16..31 make the weld 16 limbs + 16 zeros, the `v′` pattern); α, ζ,
   ξ, r weld to `dregg-mina-xi-endo-lift::v1` instances (the descriptor is challenge-independent;
   each instance is a witness/PI regen).
5. **The b-halves `BP0Z/BP1Z/BP0W/BP1W` — PORTS, never recomputed.** A second `bEval` here would
   be a twin of `MinaWrapConjunctionAir`'s threaded fold. They weld to conjunction instances'
   published registers at the fold.
6. **`CIP_CLAIM`/`PERM_CLAIM`'s consumers — AT THE FOLD/HOST**: `CIP_CLAIM` connects to the
   conjunction's `CIP` block (the `ub` coefficient `c·cip − z1·b0` of the opening), `PERM_CLAIM`
   to the `f_comm` MSM's scalar lane (`MinaWrapGroupGate.F_TERMS`).

## ⚑⚑ THE ONE PORT THAT IS UNDONE WORK IN PORT'S CLOTHES — `LCT`

`ft_eval0`'s last subtraction is `− linConstTerm`, and `linConstTerm` here is the PI-pinned block
`LCT`, welded to nothing yet. `cipActualOf` is affine in `ft_eval0` and therefore affine in `LCT`,
so **a prover free to choose `LCT` can reach any `CIP_CLAIM`** — the same shape as the vacuity
this leaf closes for `ft_eval0`, one level down. It is a PORT (published, refutable, elementwise)
whose closure is the gate-linearization leaf: `KimchiVerify.gateLinConst`'s six transcribed bodies
over the same 86 eval blocks, ~320 further ops on this same substrate. That leaf is NAMED, not
built here, and **no claim of "conjunct 3 closed" may omit this sentence.** The standing is
exactly `MinaWrapConjunctionAir.xiCorrect`'s ("a consumer's constraint, real in the fold") —
except the consumer does not exist yet, which is worse, and is said here rather than discovered.

## THE SCHEDULE, THE REGISTER, AND WHAT IS REUSED

One op per row, 301 ops, 512-row trace (power of two, idle tail). A 302-wide one-hot phase
register (301 op phases + IDLE), `AirSelectorForcing`'s own register discipline at this size.
Values live in 32-limb slots allocated by `AirColumnAlloc.allocate` over the program's own live
ranges; slots are carried across rows by **complement-masked** transition legs — the mask is
`1 − Σ handover-phases` rather than `Σ live-phases`, which keeps every carry leg's expression
O(handovers) instead of O(live-length) at 301 rows. The sound cores are
`PastaCurveSound.mulCore/addSubCore` at `qLimb`, verbatim; the witness pools and the
one-column-one-range-class law are `PastaCurveScheduled`'s.

## WHAT IS PROVED HERE vs WHAT IS PENDING — read before citing

* PROVED (kernel): the layout facts — op count, table coverage, read coverage, same-slot
  disjointness, width, committed width, constraint census. PROVED (compiled, confessed at the
  statements): `mainRailOk`, `pinsTied`.
* PROVED in `MinaFinalizeScalarsWeld` (kernel): the real-block differential — the program's
  denotation on Mina devnet block 539508's own wire reproduces `proof.oracles(…)`'s
  `combined_inner_product` and o1-labs' own `perm_scalars` value, and the reference composition
  (§5) meets the same numbers at the same point. ⚠ The GENERIC `progEval = reference` theorem is
  pending and named in §5 — the weld is a differential, not a proof about all inputs.
* ⚠ PENDING, NAMED: the trace-level forcing composition (this trace's rows + carries + phase
  register ⇒ the slot values ARE the denotation) is `AirCrossRow`'s walk at 301 ops, NOT built
  here. Its two selector premises are reachable by the argument `AirSelectorForcing` already
  makes (`phaseIndicator_of_phaseFacts` + `bits_onehot` are general; this register is the same
  shape at literal 301/302, and the complement carry masks need `mask ≡ 1 on live transitions`,
  which is PhaseIndicator + `same_slot_ranges_are_disjoint`); the per-op walk is the
  `rcbSat_of_rows` composition generalized over `finalizeProg` with `the_ranges_cover_the_reads`
  as its placement side condition. Until it lands, this descriptor's polarity evidence is the
  deployed prover's refusal (real, measured in `circuit/tests/mina_finalize_scalars_proves.rs`),
  which is behavioural, not a proof — say it that way.

## Axiom hygiene

`#assert_axioms` on every named theorem; no `sorry`/`admit`; zero `#guard`s. ⚠ TWO theorems are
compiler-trusted and say so at their statements (`finalizeAir_mainRailOk`, `finalizeAir_pinsTied`
— `native_decide` + `#assert_compiled`, the `SeamSpec` §4 wall); everything else is kernel.
-/
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PicklesFinalize
import Dregg2.Circuit.Emit.PastaCurveScheduled
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Bridge.MinaWrapFtEval0

namespace Dregg2.Circuit.Emit.MinaFinalizeScalars

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TableId mainTableDef WindowExpr)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg WindowLeg PiPinLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB CB NG limbCols carryCols rangeTidW qLimb limbAt)
open Dregg2.Circuit.Emit.PastaAddSubSound (NA ACB CBITS acarryCols)
open Dregg2.Circuit.Emit.PastaCurveSound (SoundCore mulCore addSubCore)
open Dregg2.Circuit.Emit.PastaCurveScheduled (sumLoc)
open Dregg2.Circuit.Emit.AirColumnAlloc (SsaOp LiveRange liveRanges allocate allocWidth defTime lastUse)
open Dregg2.Circuit.Emit.KimchiVerify (PERMUTS ftEval0R cipR zkPolyR)
open Dregg2.Circuit.Emit.PicklesFinalize (permScalarR)

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! ## §1 — THE VALUE SPACE.

Values are `Nat` indices. `0 … NPI−1` are the PI-pinned input blocks, `NPI … NIN−1` the
constant blocks, and op `i` defines value `NIN + i` — every op defines exactly one fresh value,
so the program is SSA by construction and `dst` is never written down (a hand-numbered `dst`
table at 301 ops is 301 chances to alias two values). -/

-- The 43 evaluation columns at ζ, wire order `[z] ++ sel(6) ++ w(15) ++ coeff(15) ++ s(6)`.
def vEZ (k : Nat) : Nat := k
-- …and at ζω.
def vEW (k : Nat) : Nat := 43 + k
/-- `ft_eval1` — tape element 2. -/
def vFT1 : Nat := 86
/-- `public_evals[0]` (ζ) — tape element 3. -/
def vPUBZ : Nat := 87
/-- `public_evals[1]` (ζω) — tape element 4. -/
def vPUBW : Nat := 88
/-- β, RAW (low-128; limbs 16..31 zero-pinned in-leaf). -/
def vBETA : Nat := 89
/-- γ, RAW. -/
def vGAMMA : Nat := 90
/-- α, endo-MAPPED (the lift instance's output). -/
def vALPHA : Nat := 91
/-- ζ, endo-MAPPED. -/
def vZETA : Nat := 92
/-- ξ (polyscale), endo-MAPPED. -/
def vXI : Nat := 93
/-- r (evalscale), endo-MAPPED. -/
def vRSQ : Nat := 94
/-- The four b-poly prefix PORTS — `es[0..1]` at both points. Never recomputed here. -/
def vBP0Z : Nat := 95
def vBP1Z : Nat := 96
def vBP0W : Nat := 97
def vBP1W : Nat := 98
/-- The claimed `combined_inner_product`, DECODED. -/
def vCIPCL : Nat := 99
/-- The claimed `perm`, DECODED. -/
def vPERMCL : Nat := 100
/-- The witnessed inverse of `(ζ − ω^{n−3})(ζ − 1)`. -/
def vDINV : Nat := 101
/-- ⚑ THE PORT: the linearization constant term. See the header section about it. -/
def vLCT : Nat := 102

/-- The number of PI-pinned input blocks. -/
def NPI_BLOCKS : Nat := 103

-- The constant blocks, forced by `.first` window pins and carried like any value.
def vONE : Nat := 103
def vZERO : Nat := 104
/-- `ω^{n−3}`, `ω^{n−2}`, `ω^{n−1}` — `zkPolyR`'s three roots, as constants of the fixed
Wrap domain (`log2n = 14`). -/
def vOM3 : Nat := 105
def vOM2 : Nat := 106
def vOM1 : Nat := 107
/-- The seven Tock coset shifts. -/
def vSH (i : Nat) : Nat := 108 + i

/-- Values that pre-exist the program: 103 PI blocks + 12 constants. -/
def NIN_VALS : Nat := 115

/-! ## §2 — THE PROGRAM.

Four op kinds. `eq` defines a fresh (dead) value so that "op `i` defines value `NIN_VALS + i`"
stays uniform; its gates read its two sources and write nothing. -/

inductive FKind where
  | mul | add | sub | eq
  deriving Repr, DecidableEq

/-- One op: the kind and the two source VALUES. The destination is implicit (`NIN_VALS + i`). -/
structure FOp where
  k : FKind
  x : Nat
  y : Nat
  deriving Repr, DecidableEq

/-- The builder state: ops emitted so far. `emit` returns the value the op defines. -/
abbrev BB := List FOp

@[inline] def emitOp (b : BB) (k : FKind) (x y : Nat) : BB × Nat :=
  (b ++ [⟨k, x, y⟩], NIN_VALS + b.length)

def bMul (b : BB) (x y : Nat) : BB × Nat := emitOp b .mul x y
def bAdd (b : BB) (x y : Nat) : BB × Nat := emitOp b .add x y
def bSub (b : BB) (x y : Nat) : BB × Nat := emitOp b .sub x y
def bEq (b : BB) (x y : Nat) : BB × Nat := emitOp b .eq x y

/-- Wire-column helpers, `MinaWrapFtEval0`'s own offsets: `w` columns start at 7, σ at 37. -/
def wCol (i : Nat) : Nat := vEZ (7 + i)
def sCol (i : Nat) : Nat := vEZ (37 + i)

/-- The Wrap domain: `log2n = 14`. -/
def LOG2N : Nat := 14
def DOMN : Nat := 2 ^ LOG2N

/-! ### Stage 0 — `ζ^n` by 14 squarings. Returns (ops, ζ^{2^14}). -/

def sqChain (b : BB) (x : Nat) : Nat → BB × Nat
  | 0 => (b, x)
  | n + 1 =>
      let (b1, x2) := bMul b x x
      sqChain b1 x2 n

def stZN (b : BB) : BB × Nat := sqChain b vZETA LOG2N

/-! ### Stage 1 — `zkPolyR`, the C5 denominator, the witnessed inverse, `ζⁿ − 1`. -/

structure St1 where
  zkp : Nat
  d3 : Nat        -- ζ − ω^{n−3}
  zm1 : Nat       -- ζ − 1
  den : Nat       -- d3 · zm1
  zeta1m1 : Nat   -- ζⁿ − 1

def stZk (b : BB) (zn : Nat) : BB × St1 :=
  let (b, d3) := bSub b vZETA vOM3
  let (b, d2) := bSub b vZETA vOM2
  let (b, d1) := bSub b vZETA vOM1
  let (b, zk0) := bMul b d3 d2
  let (b, zkp) := bMul b zk0 d1
  let (b, zm1) := bSub b vZETA vONE
  let (b, den) := bMul b d3 zm1
  let (b, dchk) := bMul b den vDINV
  let (b, _) := bEq b dchk vONE
  let (b, zeta1m1) := bSub b zn vONE
  (b, ⟨zkp, d3, zm1, den, zeta1m1⟩)

/-! ### Stage 2 — the α ladder to α²¹, α²², α²³. -/

structure StA where
  a21 : Nat
  a22 : Nat
  a23 : Nat

def stAlpha (b : BB) : BB × StA :=
  let (b, a2) := bMul b vALPHA vALPHA
  let (b, a4) := bMul b a2 a2
  let (b, a5) := bMul b a4 vALPHA
  let (b, a10) := bMul b a5 a5
  let (b, a20) := bMul b a10 a10
  let (b, a21) := bMul b a20 vALPHA
  let (b, a22) := bMul b a21 vALPHA
  let (b, a23) := bMul b a22 vALPHA
  (b, ⟨a21, a22, a23⟩)

/-! ### Stage 3 — the C5 NUMERATOR fold, and its six per-σ factors (shared with `perm`).

`init = (w₆ + γ)·z(ζω)·α²¹·zkp`, then six rounds of `acc · (β·sᵢ + wᵢ + γ)`. The six factors are
returned so stage 9 REUSES them — `permScalarR`'s fold factor is the same value, and computing it
twice would be 18 wasted rows. -/

def numerRound (bf : BB × Nat × List Nat) (i : Nat) : BB × Nat × List Nat :=
  let (b, acc, fs) := bf
  let (b, bs) := bMul b vBETA (sCol i)
  let (b, bsw) := bAdd b bs (wCol i)
  let (b, f) := bAdd b bsw vGAMMA
  let (b, acc') := bMul b acc f
  (b, acc', fs ++ [f])

def stNumer (b : BB) (a : StA) (s1 : St1) : BB × Nat × List Nat :=
  let (b, t0) := bAdd b (wCol 6) vGAMMA
  let (b, i1) := bMul b t0 (vEW 0)
  let (b, i2) := bMul b i1 a.a21
  let (b, i3) := bMul b i2 s1.zkp
  (List.range (PERMUTS - 1)).foldl numerRound (b, i3, [])

/-! ### Stage 4/5 — the public subtraction and the C5 DENOMINATOR fold. -/

def denomRound (bp : BB × Nat × Nat) (i : Nat) : BB × Nat × Nat :=
  let (b, bz, acc) := bp
  let (b, u1) := bMul b bz (vSH i)
  let (b, u2) := bAdd b u1 vGAMMA
  let (b, u3) := bAdd b u2 (wCol i)
  let (b, acc') := bMul b acc u3
  (b, bz, acc')

def stDenom (b : BB) (a : StA) (s1 : St1) : BB × Nat :=
  let (b, bz) := bMul b vBETA vZETA
  let (b, e1) := bMul b a.a21 s1.zkp
  let (b, e2) := bMul b e1 (vEZ 0)
  let (b, _, acc) := (List.range PERMUTS).foldl denomRound (b, bz, e2)
  (b, acc)

/-! ### Stage 7 — the zk-row numerator and `ft_eval0` itself. -/

def stFt (b : BB) (a : StA) (s1 : St1) (numer pubZ denom : Nat) : BB × Nat :=
  let (b, afterPub) := bSub b numer pubZ
  let (b, afterDenom) := bSub b afterPub denom
  let (b, n1) := bMul b s1.zeta1m1 a.a22
  let (b, n1b) := bMul b n1 s1.d3
  let (b, n2) := bMul b s1.zeta1m1 a.a23
  let (b, n2b) := bMul b n2 s1.zm1
  let (b, ns) := bAdd b n1b n2b
  let (b, omz) := bSub b vONE (vEZ 0)
  let (b, nsz) := bMul b ns omz
  let (b, nd) := bMul b nsz vDINV
  let (b, azk) := bAdd b afterDenom nd
  let (b, ft0) := bSub b azk vLCT
  (b, ft0)

/-! ### Stage 9 — `permScalarR`, reusing stage 3's six factors, and its forcing. -/

def stPerm (b : BB) (a : StA) (s1 : St1) (factors : List Nat) : BB :=
  let (b, p1) := bMul b (vEW 0) vBETA
  let (b, p2) := bMul b p1 a.a21
  let (b, p3) := bMul b p2 s1.zkp
  let (b, p) := factors.foldl (fun (bp : BB × Nat) f =>
    let (b, acc) := bp
    bMul b acc f) (b, p3)
  let (b, pneg) := bSub b vZERO p
  (bEq b vPERMCL pneg).1

/-! ### Stage 10 — the 47-entry ξ-fold (C8), Horner from the top, and its forcing.

`es` index `k`'s ζ-column and ζω-column values, with the in-AIR `ft0` in slot 3. -/

def esZ (ft0 : Nat) (k : Nat) : Nat :=
  if k = 0 then vBP0Z else if k = 1 then vBP1Z else if k = 2 then vPUBZ
  else if k = 3 then ft0 else vEZ (k - 4)

def esW (k : Nat) : Nat :=
  if k = 0 then vBP0W else if k = 1 then vBP1W else if k = 2 then vPUBW
  else if k = 3 then vFT1 else vEW (k - 4)

/-- The number of `es` entries on the Wrap side: 2 prefix + public + ft + 43 columns. -/
def NES : Nat := 47

/-- One Horner entry: `t_k = ez_k + r·ew_k`. -/
def esTerm (b : BB) (ft0 k : Nat) : BB × Nat :=
  let (b, m) := bMul b vRSQ (esW k)
  bAdd b (esZ ft0 k) m

/-- The Horner walk from entry `NES−1` down to 0: `acc ← acc·ξ + t_k`. -/
def cipHorner (b : BB) (ft0 : Nat) (acc : Nat) : Nat → BB × Nat
  | 0 => (b, acc)
  | j + 1 =>
      let (b, am) := bMul b acc vXI
      let (b, t) := esTerm b ft0 j
      let (b, acc') := bAdd b am t
      cipHorner b ft0 acc' j

def stCip (b : BB) (ft0 : Nat) : BB :=
  let (b, t46) := esTerm b ft0 (NES - 1)
  let (b, cip) := cipHorner b ft0 t46 (NES - 1)
  (bEq b vCIPCL cip).1

/-! ### THE WHOLE PROGRAM. -/

def finalizeProg : List FOp :=
  let b : BB := []
  let (b, zn) := stZN b
  let (b, s1) := stZk b zn
  let (b, a) := stAlpha b
  let (b, numer, factors) := stNumer b a s1
  let (b, denom) := stDenom b a s1
  let (b, ft0) := stFt b a s1 numer vPUBZ denom
  let b := stPerm b a s1 factors
  stCip b ft0

/-- The op count, pinned. 301 ops: 14 + 10 + 8 + 28 + 31 + 12 + 11 + 187. -/
theorem finalizeProg_length : finalizeProg.length = 301 := by decide

/-- The trace height: the next power of two with an idle tail. -/
def NROWS : Nat := 512

theorem the_rows_hold_the_program : finalizeProg.length + 1 ≤ NROWS ∧ NROWS = 2 ^ 9 := by decide

/-! ## §3 — THE DENOTATION, generic over `[CommRing R]`.

`progEval` extends an environment one op at a time; op `i` writes index `NIN_VALS + i`. The `eq`
op writes its FIRST source's value (a dead value; nothing reads it) — writing SOMETHING keeps the
recursion uniform. -/

def stepEval {R : Type} [CommRing R] (env : Nat → R) (o : FOp) (dst : Nat) : Nat → R :=
  fun v =>
    if v = dst then
      match o.k with
      | .mul => env o.x * env o.y
      | .add => env o.x + env o.y
      | .sub => env o.x - env o.y
      | .eq => env o.x
    else env v

def progEvalFrom {R : Type} [CommRing R] (env : Nat → R) (base : Nat) : List FOp → (Nat → R)
  | [] => env
  | o :: rest => progEvalFrom (stepEval env o base) (base + 1) rest

/-- The whole program's environment, from the 115 input/constant values. -/
def progEval {R : Type} [CommRing R] (env0 : Nat → R) : Nat → R :=
  progEvalFrom env0 NIN_VALS finalizeProg

/-! ## §4 — THE SCHEDULE AS DATA, and the allocation.

⚑ **The allocation is MATERIALIZED as three literal tables**, not called at every use site. The
reason is kernel arithmetic, not taste: `slotOfF` appears inside every one of ~23K legs, and a
`by decide` on `mainRailOk` that re-ran `AirColumnAlloc.allocate` (a ~10⁷-step fold at 416
values × 301 ops) per reference would never terminate. The tables are the allocator's own answer
(rendered by `AirColumnAlloc` at emit time); what the kernel then checks — directly, cheaply, and
about the object the legs actually use — are the three facts the layout needs:

  * `the_ranges_cover_the_reads` — every op reads its sources inside their live windows and
    defines its value at its own row;
  * `same_slot_ranges_are_disjoint` — two values sharing a slot never overlap;
  * `the_slots_fit` — every slot index is below `NSLOTS`.

Those three are what the forcing walk consumes; the allocator itself is tooling. -/

/-- Op `i` as an `SsaOp` — dst `NIN_VALS + i`, reads its two sources. Emit-time tooling and the
weld's tie-point; the legs below never call it. -/
def finalizeSsa : List SsaOp :=
  (List.range finalizeProg.length).map (fun i =>
    match finalizeProg[i]? with
    | some o => ⟨NIN_VALS + i, [o.x, o.y]⟩
    | none => ⟨NIN_VALS + i, []⟩)

/-- The number of values: 115 inputs/constants + one per op. -/
def NVALS : Nat := NIN_VALS + finalizeProg.length

theorem nvals_eq : NVALS = 416 := by decide

/-- The physical slot of each value, value-indexed. -/
def slotTable : List Nat := [36, 119, 117, 115, 113, 111, 109, 25, 27, 29, 31, 33, 35, 20, 100, 98, 96, 94, 92, 90, 88, 86, 84, 82, 80, 78, 76, 74, 72, 70, 68, 66, 64, 62, 60, 58, 56, 24, 26, 28, 30, 32, 34, 22, 118, 116, 114, 112, 110, 108, 107, 106, 105, 104, 103, 102, 101, 99, 97, 95, 93, 91, 89, 87, 85, 83, 81, 79, 77, 75, 73, 71, 69, 67, 65, 63, 61, 59, 57, 55, 54, 53, 52, 51, 50, 48, 120, 43, 121, 23, 21, 7, 15, 49, 47, 125, 123, 124, 122, 126, 46, 19, 44, 18, 45, 2, 3, 4, 17, 37, 38, 39, 40, 41, 42, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 3, 4, 2, 3, 4, 5, 4, 4, 1, 5, 1, 5, 1, 5, 1, 6, 7, 8, 7, 8, 7, 9, 7, 9, 8, 10, 8, 10, 9, 11, 9, 11, 10, 12, 10, 12, 11, 13, 11, 13, 12, 14, 12, 14, 13, 15, 16, 15, 17, 15, 17, 15, 16, 15, 16, 15, 17, 15, 17, 15, 16, 15, 16, 15, 17, 15, 17, 15, 16, 15, 16, 15, 13, 15, 13, 15, 14, 13, 1, 0, 4, 0, 1, 3, 0, 1, 0, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1]

/-- Each value's first live row (its definition row; 0 for inputs/constants). -/
def loTable : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300]

/-- Each value's last live row (its last read; its definition row if never read). -/
def hiTable : List Nat := [282, 278, 274, 270, 266, 262, 258, 254, 250, 246, 242, 238, 234, 230, 226, 222, 218, 214, 210, 206, 202, 198, 194, 190, 186, 182, 178, 174, 170, 166, 162, 158, 154, 150, 146, 142, 138, 134, 130, 126, 122, 118, 115, 281, 277, 273, 269, 265, 261, 257, 253, 249, 245, 241, 237, 233, 229, 225, 221, 217, 213, 209, 205, 201, 197, 193, 189, 185, 181, 177, 173, 169, 165, 161, 157, 153, 149, 145, 141, 137, 133, 129, 125, 121, 117, 114, 285, 290, 289, 103, 88, 31, 60, 296, 297, 298, 294, 297, 293, 300, 113, 100, 102, 98, 112, 14, 15, 16, 63, 67, 71, 75, 79, 83, 87, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 23, 94, 17, 18, 18, 105, 96, 21, 22, 22, 95, 25, 26, 27, 28, 29, 104, 93, 95, 33, 34, 35, 39, 37, 38, 106, 43, 41, 42, 107, 47, 45, 46, 108, 51, 49, 50, 109, 55, 53, 54, 110, 59, 57, 58, 111, 91, 87, 62, 66, 64, 65, 66, 70, 68, 69, 70, 74, 72, 73, 74, 78, 76, 77, 78, 82, 80, 81, 82, 86, 84, 85, 86, 90, 88, 89, 90, 92, 92, 101, 94, 97, 96, 97, 99, 99, 100, 101, 102, 286, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 113, 115, 116, 119, 118, 119, 120, 123, 122, 123, 124, 127, 126, 127, 128, 131, 130, 131, 132, 135, 134, 135, 136, 139, 138, 139, 140, 143, 142, 143, 144, 147, 146, 147, 148, 151, 150, 151, 152, 155, 154, 155, 156, 159, 158, 159, 160, 163, 162, 163, 164, 167, 166, 167, 168, 171, 170, 171, 172, 175, 174, 175, 176, 179, 178, 179, 180, 183, 182, 183, 184, 187, 186, 187, 188, 191, 190, 191, 192, 195, 194, 195, 196, 199, 198, 199, 200, 203, 202, 203, 204, 207, 206, 207, 208, 211, 210, 211, 212, 215, 214, 215, 216, 219, 218, 219, 220, 223, 222, 223, 224, 227, 226, 227, 228, 231, 230, 231, 232, 235, 234, 235, 236, 239, 238, 239, 240, 243, 242, 243, 244, 247, 246, 247, 248, 251, 250, 251, 252, 255, 254, 255, 256, 259, 258, 259, 260, 263, 262, 263, 264, 267, 266, 267, 268, 271, 270, 271, 272, 275, 274, 275, 276, 279, 278, 279, 280, 283, 282, 283, 284, 287, 286, 287, 288, 291, 290, 291, 292, 295, 294, 295, 296, 299, 298, 299, 300, 300]

def slotOfF (v : Nat) : Nat := slotTable.getD v 0
def loOfF (v : Nat) : Nat := loTable.getD v 0
def hiOfF (v : Nat) : Nat := hiTable.getD v 0

/-- The physical slot count. -/
def NSLOTS : Nat := 127

set_option maxHeartbeats 40000000 in
/-- The three tables cover the value space and the slots fit. -/
theorem the_tables_cover_the_values :
    slotTable.length = NVALS ∧ loTable.length = NVALS ∧ hiTable.length = NVALS
    ∧ slotTable.all (· < NSLOTS) = true := by decide

set_option maxHeartbeats 400000000 in
/-- ⚑ **EVERY READ IS INSIDE ITS SOURCE'S LIVE WINDOW, AND EVERY DEFINITION IS AT ITS OWN ROW.**
This is the fact the cross-row gather consumes: op `i`'s gate reads its sources' slots AT row `i`,
and the carries hold each slot constant from the value's definition row to `i`. -/
theorem the_ranges_cover_the_reads :
    (List.range finalizeProg.length).all (fun i =>
      match finalizeProg[i]? with
      | some o =>
          loOfF o.x ≤ i && i ≤ hiOfF o.x && o.x < NVALS
          && (loOfF o.y ≤ i && i ≤ hiOfF o.y && o.y < NVALS)
          && loOfF (NIN_VALS + i) == i && i ≤ hiOfF (NIN_VALS + i)
      | none => false) = true := by decide

set_option maxHeartbeats 400000000 in
/-- ⚑ **TWO VALUES SHARING A SLOT NEVER OVERLAP.** Stated over same-slot pairs only — the fact
the carry discipline needs, checked directly on the tables. -/
theorem same_slot_ranges_are_disjoint :
    (List.range NVALS).all (fun v =>
      (List.range v).all (fun u =>
        slotOfF u != slotOfF v || hiOfF u < loOfF v || hiOfF v < loOfF u)) = true := by decide

set_option maxHeartbeats 40000000 in
/-- Inputs and constants are live from row 0 — which is what makes a `.first` pin a pin on the
value every consuming gate reads. -/
theorem inputs_are_live_from_the_top :
    (List.range NIN_VALS).all (fun v => loOfF v == 0) = true := by decide

/-! ## §5 — THE REFERENCE the program claims to compute, and the standing of the tie.

`cipRef`/`ftRef`/`permRef` below are thin compositions of the SHIPPED bodies (`KimchiVerify.cipR`
/ `ftEval0R`, `PicklesFinalize.permScalarR`) — no arithmetic is re-authored, so there is no twin
to drift. What ties `progEval` to them:

  * TODAY (in `MinaFinalizeScalarsWeld`, kernel decide): at the real block's environment, both
    sides land on upstream's own `combined_inner_product` and `perm_scalars` numbers, and each
    input that should move them moves them. A differential at one real point, both sides
    upstream-derived — not a proof about all inputs.
  * ⚠ PENDING, NAMED: the generic `progEval = reference` theorem at every `[CommRing R]` and
    every environment. Its shape is staged — `progEvalFrom_append` + a frame lemma for reads
    below the extension base, per-stage lemmas (each ≤ 31 ops), and `bFoldFrom`-style inductions
    for the two folds (`numerRound`/`denomRound`/`cipHorner`). Undone work with a shape, not a
    theorem of the model; until it lands, do not cite this file as proving the program computes
    the reference — cite the weld's differential, at its resolution. -/

/-- The reference: what the program CLAIMS to compute, as one thin composition of the shipped
bodies. `esZref`/`esWref` are the 47-entry lists `cipR` folds, with `ftEval0R`'s value in slot 3.
No arithmetic is re-authored: every body is `KimchiVerify`'s / `PicklesFinalize`'s. -/
def esZref {R : Type} [CommRing R] (env0 : Nat → R) (ft : R) : List R :=
  (List.range NES).map (fun k =>
    if k = 0 then env0 vBP0Z else if k = 1 then env0 vBP1Z else if k = 2 then env0 vPUBZ
    else if k = 3 then ft else env0 (vEZ (k - 4)))

def esWref {R : Type} [CommRing R] (env0 : Nat → R) : List R :=
  (List.range NES).map (fun k =>
    if k = 0 then env0 vBP0W else if k = 1 then env0 vBP1W else if k = 2 then env0 vPUBW
    else if k = 3 then env0 vFT1 else env0 (vEW (k - 4)))

/-- The `w` and σ eval lists as `ftEval0R`/`permScalarR` want them. -/
def wListRef {R : Type} [CommRing R] (env0 : Nat → R) : List R :=
  (List.range 15).map (fun i => env0 (wCol i))
def sListRef {R : Type} [CommRing R] (env0 : Nat → R) : List R :=
  (List.range 6).map (fun i => env0 (sCol i))
def shListRef {R : Type} [CommRing R] (env0 : Nat → R) : List R :=
  (List.range PERMUTS).map (fun i => env0 (vSH i))

/-- The reference `ft_eval0`: `KimchiVerify.ftEval0R` at the environment's own values, with the
domain generator entering ONLY through the three constant blocks (`zkPolyR`'s roots) — which is
why the statement takes them as hypotheses rather than recomputing `ω`. -/
def ftRef {R : Type} [CommRing R] (env0 : Nat → R) (omega : R) : R :=
  ftEval0R DOMN omega (env0 vZETA) (env0 vBETA) (env0 vGAMMA)
    (env0 vALPHA ^ 21) (env0 vALPHA ^ 22) (env0 vALPHA ^ 23)
    (wListRef env0) (sListRef env0) (shListRef env0)
    (env0 (vEZ 0)) (env0 (vEW 0)) (env0 vPUBZ) (env0 vLCT) (env0 vDINV)

def cipRef {R : Type} [CommRing R] (env0 : Nat → R) (omega : R) : R :=
  cipR (env0 vXI) (env0 vRSQ) (esZref env0 (ftRef env0 omega)) (esWref env0)

def permRef {R : Type} [CommRing R] (env0 : Nat → R) (omega : R) : R :=
  permScalarR DOMN omega (env0 vZETA) (env0 vBETA) (env0 vGAMMA) (env0 vALPHA ^ 21)
    (wListRef env0) (sListRef env0) (env0 (vEW 0))

/-! ## §6 — THE COLUMN LAYOUT. -/

/-- Selector columns: phases `0 … 300` then IDLE at 301. `SEL` is the identity, as in
`PastaCurveScheduled` — a property of this layout, stated so it can be cited. -/
def NPHASE : Nat := finalizeProg.length
def SEL (i : Nat) : Nat := i
def SEL_IDLE : Nat := NPHASE

/-- The value slots begin after the selectors. -/
def VAL_BASE : Nat := NPHASE + 1
def valueColF (v : Nat) : Nat := VAL_BASE + SK * slotOfF v

/-- The witness pools, `PastaCurveScheduled`'s order: w1, then w8 (32), then w16 (62), adjacent
so each core's `wB`/`wB+1`/`wB+SK` strides land inside the right range class. -/
def W1_COL : Nat := VAL_BASE + SK * NSLOTS
def W8_BASE : Nat := W1_COL + 1
def W16_BASE : Nat := W8_BASE + SK
def FS_WIDTH : Nat := W16_BASE + (NG - 1)

def MUL_WIT : Nat := W8_BASE
def ADDSUB_WIT : Nat := W1_COL

/-! ## §7 — THE LEGS. -/

/-- Booleanity of every phase column, on every row (`.window .all`, not `.gate`, so the last row
is bound too — `PastaCurveScheduled`'s own reasoning). -/
def selBooleanLegs : List AirLeg :=
  (List.range (NPHASE + 1)).map (fun i =>
    AirLeg.window ⟨.all, .mul (.loc (SEL i)) (.add (.loc (SEL i)) (.const (-1)))⟩)

/-- Exactly one phase live per row. -/
def selOneHotLeg : AirLeg :=
  AirLeg.window ⟨.all, .add (sumLoc (List.range (NPHASE + 1))) (.const (-1))⟩

/-- The shift register: row 0 is phase 0; the indicator walks right; the idle column absorbs the
last phase and itself; phase 0 never returns. -/
def selShiftLegs : List AirLeg :=
  AirLeg.window ⟨.first, .add (.loc (SEL 0)) (.const (-1))⟩
  :: AirLeg.window ⟨.transition, .nxt (SEL 0)⟩
  :: AirLeg.window ⟨.transition,
       .add (.nxt SEL_IDLE)
         (.mul (.const (-1)) (.add (.loc (SEL (NPHASE - 1))) (.loc SEL_IDLE)))⟩
  :: (List.range (NPHASE - 1)).map (fun i =>
       AirLeg.window ⟨.transition,
         .add (.nxt (SEL (i + 1))) (.mul (.const (-1)) (.loc (SEL i)))⟩)

/-- Every value slot is byte-pooled on every row. -/
def valuePoolLegs : List AirLeg :=
  (List.range NSLOTS).map (fun k =>
    AirLeg.limbs ⟨limbCols (VAL_BASE + SK * k), SB, rangeTidW SB⟩)

/-- The three witness pools, by range class. -/
def witnessPoolLegs : List AirLeg :=
  [ AirLeg.limbs ⟨[W1_COL], CBITS, rangeTidW CBITS⟩
  , AirLeg.limbs ⟨(List.range SK).map (W8_BASE + ·), SB, rangeTidW SB⟩
  , AirLeg.limbs ⟨(List.range (NG - 1)).map (W16_BASE + ·), CB, rangeTidW CB⟩ ]

/-! ### The complement-masked carries.

A slot must carry its value across every transition EXCEPT the one that hands it to a new tenant.
The handover phases of slot `s` are `d − 1` for each value defined into `s` at row `d ≥ 1`; the
mask is `1 − Σ SEL(handovers)`, so the leg's size is the slot's TENANT count, not its live
length — the whole reason a 301-row schedule's carry block stays readable. On a live transition
the mask reads 1 (`PhaseIndicator` + the handovers being elsewhere), so `carried_constant`
applies verbatim; on a handover it reads 0 and the slot is free. -/

/-- The rows at which slot `s` acquires a NEW tenant (the tenant's definition row), minus one:
the transitions the carry must NOT constrain. From the literal tables, so a leg build never runs
the allocator. -/
def handoverPhases (s : Nat) : List Nat :=
  ((List.range NVALS).filterMap (fun v =>
    if slotOfF v == s && decide (0 < loOfF v) then some (loOfF v - 1) else none)).eraseDups

def carryMaskF (s : Nat) : WindowExpr :=
  .add (.const 1) (.mul (.const (-1)) (sumLoc ((handoverPhases s).map SEL)))

def carryLegsF : List AirLeg :=
  (List.range NSLOTS).flatMap (fun s =>
    (List.range SK).map (fun j =>
      AirLeg.window ⟨.transition,
        .mul (carryMaskF s)
          (.add (.nxt (VAL_BASE + SK * s + j))
                (.mul (.const (-1)) (.loc (VAL_BASE + SK * s + j))))⟩))

/-! ### The scheduled op gates. -/

def coreOfF : FKind → SoundCore
  | .mul => mulCore qLimb
  | .add => addSubCore qLimb 1 (-1)
  | .sub => addSubCore qLimb (-1) 1
  | .eq => { legs := fun _ _ _ _ => [], width := 0 }

def witOfF : FKind → Nat
  | .mul => MUL_WIT
  | _ => ADDSUB_WIT

def isGate : AirLeg → Bool
  | .gate _ => true
  | _ => false

def gateBy (sel : Nat) : AirLeg → AirLeg
  | .gate c => .gate ⟨.mul (.var sel) c.lhs, c.rhs⟩
  | l => l

/-- The 32 equality gates of an `eq` op — `SEL i · (x_j − y_j)`. -/
def eqLegs (i xB yB : Nat) : List AirLeg :=
  (List.range SK).map (fun j =>
    AirLeg.gate ⟨.mul (.var (SEL i))
      (.add (.var (xB + j)) (.mul (.const (-1)) (.var (yB + j)))), .const 0⟩)

def opLegsF (i : Nat) (o : FOp) : List AirLeg :=
  match o.k with
  | .eq => eqLegs i (valueColF o.x) (valueColF o.y)
  | k =>
      (((coreOfF k).legs (valueColF o.x) (valueColF o.y) (valueColF (NIN_VALS + i))
          (witOfF k)).filter isGate).map (gateBy (SEL i))

def scheduleLegsF : List AirLeg :=
  (List.range finalizeProg.length).flatMap
    (fun i => match finalizeProg[i]? with | some o => opLegsF i o | none => [])

/-! ### The constant pins, the zero-high pins, and the PI pins — all `.first`, all carried. -/

/-- Pin a block at row 0 to a 255-bit literal, limb by limb. -/
def constFirstBlock (col : Nat) (v : Nat) : List AirLeg :=
  (List.range SK).map (fun j =>
    AirLeg.window ⟨.first, .add (.loc (col + j)) (.const (-(limbAt v j)))⟩)

/-- ⚑ The Wrap-side domain generator (`MinaRealBlockGate.OMEGA`'s own value, the `2^14` domain),
and `zkPolyR`'s three roots as descriptor literals, computed by the kernel-friendly ladder
(`MinaWrapFtEval0.powFast`, 28 multiplies) rather than unary `Monoid.npow`. The weld checks
`OMEGA_Q` against `MinaWrapFtEval0.rootOfUnity qN 14` and the roots against `OMEGA_Q`'s powers. -/
def OMEGA_Q : Nat := 13720502009405270468270247285101677286753189198487843249698478072631298866919
def OM3_C : Nat := (Dregg2.Bridge.MinaWrapFtEval0.powFast ((OMEGA_Q : Nat) : ZMod qN) (DOMN - 3)).val
def OM2_C : Nat := (Dregg2.Bridge.MinaWrapFtEval0.powFast ((OMEGA_Q : Nat) : ZMod qN) (DOMN - 2)).val
def OM1_C : Nat := (Dregg2.Bridge.MinaWrapFtEval0.powFast ((OMEGA_Q : Nat) : ZMod qN) (DOMN - 1)).val

/-- The seven Tock coset shifts of the deployed Wrap verifier index —
`MinaMultiBlockConformance`'s own `shift` fixture (identical across every wrap block: shifts are
per-INDEX constants). The weld pins the equality against that fixture. -/
def SHIFTS_Q : List Nat :=
  [ 1
  , 328286983623303317637963920346571898945724874896624808297627776768640590563
  , 220790353665890403705559231885806581221301230221265349993193424985261418438
  , 211720422259245489258933986578227917398506328781182391541883955346082631533
  , 211634429328372259348572816867521795029192573698954618296359582461568682420
  , 317476258975906211462498873025720239242336777696786967497139785505242641540
  , 99141114743446054294525453467100398765600279346526770105380817318185104545 ]

def constLegsF : List AirLeg :=
  constFirstBlock (valueColF vONE) 1
  ++ constFirstBlock (valueColF vZERO) 0
  ++ constFirstBlock (valueColF vOM3) OM3_C
  ++ constFirstBlock (valueColF vOM2) OM2_C
  ++ constFirstBlock (valueColF vOM1) OM1_C
  ++ (List.range PERMUTS).flatMap (fun i =>
       constFirstBlock (valueColF (vSH i)) (SHIFTS_Q.getD i 0))

/-- β and γ are LOW-128-BIT squeezes: limbs 16..31 are pinned zero, so the phase-1 weld is
16 limbs + 16 zero-pins — the `v′` pattern, in-leaf. -/
def zeroHighLegs : List AirLeg :=
  [vBETA, vGAMMA].flatMap (fun v =>
    (List.range (SK / 2)).map (fun j =>
      AirLeg.window ⟨.first, .loc (valueColF v + SK / 2 + j)⟩))

/-- The PI pins: the 103 input blocks, in value order, at row 0. -/
def piPinsF : List AirLeg :=
  (List.range NPI_BLOCKS).flatMap (fun v =>
    (List.range SK).map (fun j =>
      AirLeg.pin ⟨VmRow.first, valueColF v + SK * 0 + j, SK * v + j⟩))

def FS_PI_COUNT : Nat := NPI_BLOCKS * SK

theorem fs_pi_count_eq : FS_PI_COUNT = 3296 := by decide

/-! ## §8 — THE AIR AND THE DESCRIPTOR. -/

def fsTables : List TableDef :=
  [ mainTableDef FS_WIDTH
  , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
  , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
  , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]

def finalizeAir : EffectAir :=
  { tables := fsTables
  , legs := selBooleanLegs ++ [selOneHotLeg] ++ selShiftLegs
      ++ valuePoolLegs ++ witnessPoolLegs
      ++ carryLegsF
      ++ scheduleLegsF
      ++ constLegsF ++ zeroHighLegs
      ++ piPinsF }

def finalizeDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-mina-finalize-scalars::v1" FS_WIDTH FS_PI_COUNT [] finalizeAir

/-! ## §9 — THE CENSUS, against the corrected numbers, and the two rail verdicts.

Declared **4 461** columns (302 selectors + 127 × 32 value slots + 95 witness pool), committed
**12 903** (`AirColumnAlloc.committedWidth`'s aux law over the pool legs), 27 319 constraints,
512 rows — the inner LDE at the descriptor engine (`log_blowup 6`) is `2^15`.

For scale against the tree's own prices: the row-local rendering of the same 301 ops would have
declared ~31K columns (301 ops × ~126 fresh columns + the 3 296-column pin surface); the
scheduled row is ~7× narrower, the same ratio `PastaCurveScheduled` measures on the RCB. Against
`MinaWrapVerifierAir.WRAP_CELLS = 161 308 368`: this whole trace commits
`12 903 × 512 ≈ 6.6 × 10⁶` cells — ~4 % of one wrap verification's committed cells. ⚠ The
brief's `~2.4K columns × 256 rows` estimate under-counted the PIN SURFACE: 103 input blocks are
3 296 columns before an op is scheduled, and the pin mechanism (`.first`-row pins) forces every
one of them to exist as a column. The measured number is the honest one. -/

set_option maxHeartbeats 40000000 in
theorem fs_width_eq : FS_WIDTH = 4461 := by decide

set_option maxHeartbeats 40000000 in
theorem fs_layout_eq :
    NPHASE = 301 ∧ VAL_BASE = 302 ∧ W1_COL = 4366 ∧ NSLOTS = 127 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxHeartbeats 1000000000 in
theorem fs_committed_width :
    Dregg2.Circuit.Emit.AirColumnAlloc.committedWidth FS_WIDTH finalizeAir = 12903 := by decide

set_option maxHeartbeats 1000000000 in
theorem fs_constraint_count : finalizeDesc.constraints.length = 27319 := by decide

/-- ⚑ **THE COMPILER ACCEPTS EVERY LEG.** Window legs read `nxt` only under `.transition`, every
pool is `0 < bits ≤ 29`, and no leg is refused — the verdict `lowerAir` gates on.

⚠ **COMPILER-TRUSTED, and said out loud** (`native_decide` + `#assert_compiled`): the kernel
measurably cannot walk this leg list — the verdict re-instantiates `finalizeAir.legs` (23 290
legs, 14K of them sound-core convolution gates) under the traversal lambdas, defeating the whnf
cache; a 21-minute 16 GiB kernel attempt sat at 3 % CPU. `SeamSpec` §4 records the same wall for
`readCols` walks and puts the confession at the declaration site; `PastaCurveScheduled`'s
kernel-decided twin of this verdict stands at 33 ops, and re-proving it kernel-side at 301 ops is
undone work with a shape (materialize the leg list the way the slot tables are), not a theorem of
the model. -/
theorem finalizeAir_mainRailOk : finalizeAir.mainRailOk = true := by native_decide

/-- ⚑ **EVERY PUBLISHED COLUMN IS READ BY ANOTHER LEG** — each pinned block's columns appear in
its slot's pool leg, so a decorative pin is unrepresentable. Being read is not being forced; the
forcing claims live in the header table. ⚠ Compiler-trusted, same confession as above — the inner
`legs.any` rescan per pin is quadratic in exactly the terms the kernel cannot cache. -/
theorem finalizeAir_pinsTied :
    Dregg2.Circuit.EffectAirIR.EffectAir.pinsTied finalizeAir = true := by native_decide

#assert_axioms finalizeProg_length
#assert_axioms the_rows_hold_the_program
#assert_axioms nvals_eq
#assert_axioms the_tables_cover_the_values
#assert_axioms the_ranges_cover_the_reads
#assert_axioms same_slot_ranges_are_disjoint
#assert_axioms inputs_are_live_from_the_top
#assert_axioms fs_pi_count_eq
#assert_axioms fs_width_eq
#assert_axioms fs_layout_eq
#assert_axioms fs_committed_width
#assert_axioms fs_constraint_count
-- ⚑ COMPILER-TRUSTED, and said out loud: the two leg-walk verdicts.
#assert_compiled finalizeAir_mainRailOk
#assert_compiled finalizeAir_pinsTied

end Dregg2.Circuit.Emit.MinaFinalizeScalars
