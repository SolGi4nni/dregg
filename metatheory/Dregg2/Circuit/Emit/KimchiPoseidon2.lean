/-
# Dregg2.Circuit.Emit.KimchiPoseidon2 — GENERATING the Poseidon2-w16 permutation as Kimchi rows

## Why this object

A Kimchi circuit that verifies a dregg STARK proof is, by measurement, a **hashing** circuit:
`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` prices the whole route at ~11,000 Poseidon2-w16-BabyBear
permutations and puts the AIR arithmetic at ≈3.5%. Every rung of the verifier — the Merkle-opening
checks against the committed roots, the `DuplexChallenger` that derives the challenges and the
query indices, the 16-layer commit-phase fold — is made of THIS permutation. So the permutation is
the right first object for a compiler that must eventually emit the verifier: it is 96% of the
cost, it is KAT-pinned in Lean, and it is measured in o1js at **2,600.5 rows**.

## It is GENERATED, not written

`permGen` is a `def`-generator over the SAME round constants the specification uses
(`Poseidon2BabyBearW16.rcExtInitial / rcInternal / rcExtFinal` — imported, not re-typed) and the
same round structure. There are 141 S-boxes in one permutation and not one of them is spelled out:
`sboxGen` is written once and `externalRoundGen`/`internalRoundGen` fold it over the constants.
Changing a round constant changes the emitted circuit with no edit here.

## The BabyBear-in-Pasta representation, and why the reduction dominates

One BabyBear lane is ONE native Pasta variable holding a possibly NON-CANONICAL integer
representative, carrying an explicit integer upper bound — the o1js design, and the reason no
`ForeignField` gadget is needed. `p` is a compile-time constant, so `q·p` is a coefficient rather
than a multiplication. Reductions happen only when a bound would otherwise approach the Pasta
modulus, at which point field arithmetic stops agreeing with integer arithmetic and the circuit
becomes UNSOUND rather than slow. `boundsSafe` is that check, and it is a `#guard`, not a comment.

The measured split says the reduction is ~64% of the cost, and the shape below reproduces it: an
S-box is four multiplications riding unreduced plus **exactly one** `bbReduce`, and that single
reduction is 8 of its ~10 rows.

## The differential

Four `#guard`s, over the ACTUAL emitted object:

  * `permGen` on `[0..15]` produces output lanes whose canonical residues are the deployed
    permutation's Lean-pinned KAT (`Poseidon2BabyBearW16.perm`, itself `#guard`ed bit-exact against
    `default_babybear_poseidon2_16().permute` at p3 rev `82cfad73`);
  * **every emitted row is satisfied by the generated witness** — the circuit accepts a witness
    whose output is the KAT, checked row by row, not assumed;
  * the emitted ROW COUNT and gate histogram, against o1js's `Generic 1,623 · RangeCheck0 701 ·
    Lookup 278 = 2,602`;
  * `boundsSafe` — no tracked bound reaches the Pasta modulus.

The row count is where a compiler earns or loses its claim, so §7 states the measured delta and
what accounts for it rather than quoting a match.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; `#guard`/`rfl`/`decide` only, no
`sorry`/`native_decide`. NEW file; imports `KimchiLower` and `Poseidon2BabyBearW16`.
-/
import Dregg2.Circuit.Emit.KimchiLower
import Dregg2.Circuit.Poseidon2BabyBearW16

namespace Dregg2.Circuit.Emit.KimchiPoseidon2

open Dregg2.Circuit.Emit.KimchiTarget
open Dregg2.Circuit.Emit.KimchiLower
open Dregg2.Circuit.Poseidon2BabyBearW16 (P inv2 fdiv2exp perm rcExtInitial rcInternal rcExtFinal)

set_option autoImplicit false
set_option maxRecDepth 20000

/-! ## §1 — the builder: a straight-line circuit and its witness, from one traversal.

Synthesising the circuit and generating the witness in two passes is the classic way to get a
prover and a verifier that disagree. `Ctx` carries both: every operation allocates a variable,
records its value, and emits the instruction that forces it. -/

/-- The Pasta base-field modulus (`PastaField.pN`, the Vesta/Pallas base field), restated locally so
this module does not drag in the Pasta tower. A bound reaching this is where integer arithmetic and
field arithmetic part company. -/
def pastaN : Nat :=
  28948022309329048855892746252171976963363056481941560715954676764349967630337

/-- The compiler's state: witness values indexed by variable, and the emitted instruction stream. -/
structure Ctx where
  vals : Array ℤ
  ops : Array KOp
  deriving Inhabited

def Ctx.empty : Ctx := ⟨#[], #[]⟩

/-- **The pinned zero variable.** Every emission starts here, and `ZERO_VAR` is its index. -/
def ZERO_VAR : Nat := 0

/-- The next free variable index. -/
def Ctx.wm (c : Ctx) : Nat := c.vals.size

/-- The recorded witness value of a variable. -/
def Ctx.get (c : Ctx) (i : Nat) : ℤ := c.vals.getD i 0

/-- The witness as an assignment. -/
def Ctx.asg (c : Ctx) : Nat → ℤ := fun i => c.get i

/-- Allocate a fresh variable holding `x`. -/
def Ctx.alloc (c : Ctx) (x : ℤ) : Nat × Ctx := (c.vals.size, { c with vals := c.vals.push x })

/-- Emit one instruction. -/
def Ctx.emit (c : Ctx) (o : KOp) : Ctx := { c with ops := c.ops.push o }

/-- **Where every emission starts**: variable `ZERO_VAR` allocated and PINNED to zero by one
`Gen1.isZero` sub-gate. One sub-gate for the whole program (one Kimchi row, because the next
instruction is a range check and the packer flushes a lone generic), and it is what makes the two
copy columns of all 1,126 `RangeCheck0` rows a constant rather than a witness. See `bbRange64`. -/
def Ctx.start : Ctx :=
  let (z, c) := Ctx.empty.alloc 0
  c.emit (.gen (Gen1.isZero z))

/-- **A BabyBear lane in-circuit**: the variable holding a (possibly non-canonical) integer
representative, and the tracked exclusive upper bound on it. -/
structure BB where
  v : Nat
  bound : Nat
  deriving Repr, Inhabited

/-! ### §1a — the arithmetic primitives.

Each emits ONE `Gen1` (half a Kimchi row) except `bbReduce`, and each has a forcing lemma saying
what a satisfying assignment is compelled to put in the output variable. -/

/-- `o := x + y`. One sub-gate. -/
def bbAdd (c : Ctx) (x y : BB) : BB × Ctx :=
  let (o, c1) := c.alloc (c.get x.v + c.get y.v)
  (⟨o, x.bound + y.bound⟩, c1.emit (.gen (Gen1.lin2 x.v y.v o 1 1)))

/-- `o := kx·x + ky·y`, the peephole that folds a scaling into the addition it feeds. One sub-gate
where the naive form would cost two — this is where the external layer's `2·x₀` lives. -/
def bbLin2 (c : Ctx) (x y : BB) (kx ky : ℤ) (bnd : Nat) : BB × Ctx :=
  let (o, c1) := c.alloc (kx * c.get x.v + ky * c.get y.v)
  (⟨o, bnd⟩, c1.emit (.gen (Gen1.lin2 x.v y.v o kx ky)))

/-- `o := k·x`. One sub-gate. -/
def bbScale (c : Ctx) (x : BB) (k : ℤ) (bnd : Nat) : BB × Ctx :=
  let (o, c1) := c.alloc (k * c.get x.v)
  (⟨o, bnd⟩, c1.emit (.gen (Gen1.scale x.v o k)))

/-- `o := x · y`. One sub-gate; the bound MULTIPLIES, which is why a multiplication chain must be
reduced and an addition chain need not be. -/
def bbMul (c : Ctx) (x y : BB) : BB × Ctx :=
  let (o, c1) := c.alloc (c.get x.v * c.get y.v)
  (⟨o, x.bound * y.bound⟩, c1.emit (.gen (Gen1.mul x.v y.v o)))

/-- A constant lane. -/
def bbConst (c : Ctx) (k : Nat) : BB × Ctx :=
  let (o, c1) := c.alloc (k : ℤ)
  (⟨o, k + 1⟩, c1.emit (.gen (Gen1.const o (k : ℤ))))

/-- `o := x + k`, a round-constant materialisation. `generic.rs`'s `Plus(k)` — one sub-gate, NOT
free, which is the 128 rows/permutation the original estimate did not budget. -/
def bbAddConst (c : Ctx) (x : BB) (k : Nat) : BB × Ctx :=
  let (o, c1) := c.alloc (c.get x.v + (k : ℤ))
  (⟨o, x.bound + k + 1⟩, c1.emit (.gen (Gen1.addConst x.v o (k : ℤ))))

/-- The smallest multiple of `p` that is at least `b`. -/
def pCeil (b : Nat) : Nat := P * ((b + P - 1) / P)

/-- **`o := x + k·y` with `k` possibly NEGATIVE.**

This is where an integer-representative emulation differs from field arithmetic and where a naive
port goes silently wrong: `x − k·y` can be negative as an INTEGER while being a perfectly good field
element, and a witness generator that lets it go negative produces garbage that the range checks
then reject for the wrong reason. The fix is the compensation `k·⌈bound⌉_p` — a multiple of the
EMULATED modulus, so the residue is untouched — carried in the generic row's own constant slot
`c₄`. It therefore costs NOTHING: still one sub-gate.

Keeping the compensation proportional to the coefficient rather than reaching for `p − k` is what
preserves the measured bound behaviour: the six small-coefficient internal lanes gain ~2 bits a
round, not ~31. -/
def bbAddSigned (c : Ctx) (x y : BB) (k : ℤ) : BB × Ctx :=
  let comp : Nat := if k < 0 then k.natAbs * pCeil y.bound else 0
  let (o, c1) := c.alloc (c.get x.v + k * c.get y.v + (comp : ℤ))
  (⟨o, x.bound + k.natAbs * y.bound + comp⟩,
   c1.emit (.gen (Gen1.lin2c x.v y.v o 1 k (comp : ℤ))))

/-! ### §1b — the range check and the witnessed-quotient reduction. -/

/-- Bit length of a natural. -/
def bitLen (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- Split `x` into the twelve limb/crumb columns of a standalone 64-bit `RangeCheck0` row: four
12-bit plookup limbs (`w₃..w₆`, place values `2⁵²,2⁴⁰,2²⁸,2¹⁶`) and eight 2-bit crumbs
(`w₇..w₁₄`, `2¹⁴..2⁰`). Columns 1 and 2 are zeroed — that is what makes the row a 64-bit check
rather than an 88-bit one (`range_check/gadget.rs:63-69` + `connect_64bit`). -/
def rc64Limbs (x : Nat) : List Nat :=
  (KimchiTarget.rc0Places.drop 2).map (fun pl => (x >>> pl.2) % (if pl.2 ≥ 16 then 4096 else 4))

/-- Emit a standalone 64-bit `RangeCheck0` row on `x`. Costs ONE Kimchi row and is o1js's cheapest
bulk check (`rangeCheck64`, ~66 bits/row is the ceiling Kimchi's lookup gates impose).

⚑ **THE TWO COPY COLUMNS ARE THE PINNED ZERO VARIABLE, AND THAT IS LOAD-BEARING.** `rc0Places`
carries columns 1 and 2 at place values `2⁷⁶` and `2⁶⁴`, and the recomposition body is
`Σ 2^place·w_col − w₀`. Their 12-bit lookups are DEFERRED to a companion `Zero` row
(`range_check/gadget.rs:100-111`), which a standalone check does not emit — so if those columns hold
FRESH variables, `rc0Bodies` is satisfiable for **any** `w₀` whatsoever by solving for `w₁`, and the
row constrains nothing at all.

This generator allocated two fresh zero-valued variables there until 2026-07-30, which made every
one of the 1,126 emitted `RangeCheck0` rows a no-op in `KimchiTarget`'s semantics — the whole bound
argument resting on rows that admitted every assignment. o1js does not have the bug: `rangeCheck64`
passes `createField(0), createField(0)` (`gadgets/range-check.js:61`), and a CONSTANT is not a
witness anyone can move. `ZERO_VAR` is this emission's constant: one `Gen1.isZero` for the whole
program, pinned by `Ctx.start`, reused by every row. -/
def bbRange64 (c : Ctx) (x : BB) : Ctx :=
  let xv : Nat := (c.get x.v).toNat
  let (cols, c) := (rc64Limbs xv).foldl (fun (st : List Nat × Ctx) l =>
      let (i, c') := st.2.alloc (l : ℤ)
      (st.1 ++ [i], c')) ([], c)
  let gc : Nat → Nat := fun i => cols.getD i 0
  c.emit (.rc0 x.v ZERO_VAR ZERO_VAR (gc 0) (gc 1) (gc 2) (gc 3)
            (gc 4) (gc 5) (gc 6) (gc 7) (gc 8) (gc 9) (gc 10) (gc 11))

/-- The stride o1js witnesses a quotient at. The limb DIGITS are `Q_STRIDE` bits — that is what makes
`Σ limbᵢ·2^{53i} = q` exact — while the range check on each is the cheap 64-bit one, which
over-covers. Masking the digits to 64 bits instead of 53 makes consecutive limbs OVERLAP and the
recomposition double-counts eleven bits per limb; the circuit then computes a wrong `q·p` while
still producing the right digest through the reduction, so only the row-level acceptance check
catches it. It did. -/
def Q_STRIDE : Nat := 53

/-- How many 64-bit quotient limbs a bound needs. -/
def qLimbCount (bnd : Nat) : Nat := (bitLen (bnd / P) + Q_STRIDE - 1) / Q_STRIDE

/-- **The witnessed-quotient reduction** — `v = q·p + r` with `r < 2³¹`, over the INTEGERS (both
sides below the Pasta modulus, so the field equation implies the integer one).

`p` is a constant, so `q·p` is a linear combination of the quotient's limbs with coefficients
`p·2^{53i}` — no multiplication. The cost is the range checks: `qLimbCount` `RangeCheck0` rows for
the quotient plus one for `r`, which is why this single operation is ~8 of an S-box's ~10 rows and
~64% of the whole permutation. -/
def bbReduce (c : Ctx) (x : BB) : BB × Ctx :=
  let xv : Nat := (c.get x.v).toNat
  let n : Nat := qLimbCount x.bound
  let qv : Nat := xv / P
  let rv : Nat := xv % P
  -- witness the quotient limbs and range-check each
  let step : (List BB × Ctx) → Nat → (List BB × Ctx) := fun st i =>
    let lv : Nat := (qv >>> (Q_STRIDE * i)) % (2 ^ Q_STRIDE)
    let (li, c') := st.2.alloc (lv : ℤ)
    let lane : BB := ⟨li, 2 ^ 64⟩
    (st.1 ++ [lane], bbRange64 c' lane)
  let (limbs, c) := (List.range n).foldl step ([], c)
  -- q·p as one linear combination: acc ← acc + (p·2^{53i})·limbᵢ
  let mkQP : (Option BB × Ctx) → Nat → (Option BB × Ctx) := fun st i =>
    let coeff : ℤ := (P : ℤ) * (2 : ℤ) ^ (Q_STRIDE * i)
    let lane := limbs.getD i ⟨0, 0⟩
    match st.1 with
    | none =>
        let (o, c') := bbScale st.2 lane coeff (P * 2 ^ (Q_STRIDE * i) * 2 ^ 64)
        (some o, c')
    | some acc =>
        let (o, c') := bbLin2 st.2 acc lane 1 coeff (acc.bound + P * 2 ^ (Q_STRIDE * i) * 2 ^ 64)
        (some o, c')
  let (qpOpt, c) := (List.range n).foldl mkQP (none, c)
  -- witness r, range-check it, and assert v = q·p + r
  let (ri, c) := c.alloc (rv : ℤ)
  let r : BB := ⟨ri, 2 ^ 31⟩
  let c := bbRange64 c r
  match qpOpt with
  | none =>
      -- the value was already below p: assert v = r directly
      (r, c.emit (.gen (Gen1.scale x.v ri 1)))
  | some qp =>
      (r, c.emit (.gen (Gen1.lin2 qp.v ri x.v 1 1)))

/-! ## §2 — the Poseidon2 generators.

Every one is a fold over the imported round constants. Nothing below spells out a round. -/

/-- The S-box `x ↦ x⁷`: four multiplications riding unreduced, then EXACTLY one reduction. Bound
chain: an input at `2³⁶·¹⁷` gives `x⁷ < 2²⁵³·²`, under the Pasta modulus with ~0.8 bits to spare —
which is why a `2³²` lane target would wrap and be unsound rather than merely slow. -/
def sboxGen (c : Ctx) (x : BB) : BB × Ctx :=
  let (x2, c) := bbMul c x x
  let (x4, c) := bbMul c x2 x2
  let (x6, c) := bbMul c x4 x2
  let (x7, c) := bbMul c x6 x
  bbReduce c x7

/-- `apply_mat4` on a block of four — the `MDSMat4` circulant `[[2,3,1,1],…]`,
operation-for-operation as `Poseidon2BabyBearW16.mat4`. ADD-ONLY: the `2·x` factors are folded into
`bbLin2` coefficients, so a block costs nine sub-gates and no multiplication. -/
def mat4Gen (c : Ctx) (x0 x1 x2 x3 : BB) : (BB × BB × BB × BB) × Ctx :=
  let (t01, c) := bbAdd c x0 x1
  let (t23, c) := bbAdd c x2 x3
  let (t0123, c) := bbAdd c t01 t23
  let (t01123, c) := bbAdd c t0123 x1
  let (t01233, c) := bbAdd c t0123 x3
  let (y3, c) := bbLin2 c t01233 x0 1 2 (t01233.bound + 2 * x0.bound)
  let (y1, c) := bbLin2 c t01123 x2 1 2 (t01123.bound + 2 * x2.bound)
  let (y0, c) := bbAdd c t01123 t01
  let (y2, c) := bbAdd c t01233 t23
  ((y0, y1, y2, y3), c)

/-- The width-16 external linear layer: `mat4` on each block of four, then the outer circulant
`state[i] += Σ_{j≡i mod 4} state[j]`. Add-only; the composed fan-in is 35, which is the constant
that sets every downstream bound. -/
def mdsLightGen (c : Ctx) (s : List BB) : List BB × Ctx :=
  let gb : Nat → BB := fun i => s.getD i ⟨0, 0⟩
  let blkStep : (List BB × Ctx) → Nat → (List BB × Ctx) := fun st k =>
    let ((y0, y1, y2, y3), c') := mat4Gen st.2 (gb (4*k)) (gb (4*k+1)) (gb (4*k+2)) (gb (4*k+3))
    (st.1 ++ [y0, y1, y2, y3], c')
  let (m, c) := (List.range 4).foldl blkStep ([], c)
  let gm : Nat → BB := fun i => m.getD i ⟨0, 0⟩
  let sumStep : (List BB × Ctx) → Nat → (List BB × Ctx) := fun st k =>
    let (a, c1) := bbAdd st.2 (gm k) (gm (4+k))
    let (b, c2) := bbAdd c1 (gm (8+k)) (gm (12+k))
    let (t, c3) := bbAdd c2 a b
    (st.1 ++ [t], c3)
  let (sums, c) := (List.range 4).foldl sumStep ([], c)
  let outStep : (List BB × Ctx) → Nat → (List BB × Ctx) := fun st i =>
    let (o, c') := bbAdd st.2 (gm i) (sums.getD (i % 4) ⟨0, 0⟩)
    (st.1 ++ [o], c')
  (List.range 16).foldl outStep ([], c)

/-- One external round: `(state[i] + rc[i])⁷` elementwise, then the external layer. -/
def externalRoundGen (rc : List Nat) (c : Ctx) (s : List BB) : List BB × Ctx :=
  let step : (List BB × Ctx) → Nat → (List BB × Ctx) := fun st i =>
    let (t, c1) := bbAddConst st.2 (s.getD i ⟨0, 0⟩) (rc.getD i 0)
    let (u, c2) := sboxGen c1 t
    (st.1 ++ [u], c2)
  let (sb, c) := (List.range 16).foldl step ([], c)
  mdsLightGen c sb

/-- The internal diagonal `(1 + Diag(V))`, as INTEGER coefficients mod `p`, for lanes 1..15:
`V = [1, 2, ½, 3, 4, −½, −3, −4, 2⁻⁸, ¼, ⅛, 2⁻²⁷, −2⁻⁸, −2⁻⁴, −2⁻²⁷]`.
Lane 0 is the `V₀ = −2` case and is handled separately as `partSum − s₀`.
`d k` is `2⁻ᵏ mod p`, taken from the specification's own `fdiv2exp` so the two cannot drift. -/
def diagCoeff (i : Nat) : ℤ :=
  let d : Nat → ℤ := fun k => (fdiv2exp 1 k : ℤ)
  match i with
  | 1 => 1        | 2 => 2        | 3 => d 1      | 4 => 3        | 5 => 4
  | 6 => -(d 1)   | 7 => -3       | 8 => -4       | 9 => d 8      | 10 => d 2
  | 11 => d 3     | 12 => d 27    | 13 => -(d 8)  | 14 => -(d 4)  | _ => -(d 27)

/-- The nine lanes whose diagonal coefficient is a FULL-WIDTH field inverse. They gain ~31 bits
every internal round and must be reduced every round; the six small-coefficient lanes (±1,±2,±3,±4)
gain ~2 bits and are left to grow. Reducing `partSum` once rather than all fifteen lanes is what
keeps the internal rounds at ~56 rows each instead of ~1,000 for the block. -/
def fullWidthLane (i : Nat) : Bool := decide (4 < (diagCoeff i).natAbs)

/-- One internal round. -/
def internalRoundGen (rc : Nat) (c : Ctx) (s : List BB) : List BB × Ctx :=
  let gb : Nat → BB := fun i => s.getD i ⟨0, 0⟩
  -- s0 := sbox(state[0] + rc)
  let (t0, c) := bbAddConst c (gb 0) rc
  let (s0, c) := sboxGen c t0
  -- partSum := Σ_{j=1..15} state[j], reduced ONCE (the optimisation the estimate did not model)
  let sumStep : (Option BB × Ctx) → Nat → (Option BB × Ctx) := fun st j =>
    match st.1 with
    | none => (some (gb j), st.2)
    | some acc => let (o, c') := bbAdd st.2 acc (gb j); (some o, c')
  let (psOpt, c) := ((List.range 15).map (· + 1)).foldl sumStep (none, c)
  let ps := psOpt.getD ⟨0, 1⟩
  let (partSum, c) := bbReduce c ps
  -- fullSum := partSum + s0 ; lane 0 := partSum − s0  (the V₀ = −2 case)
  let (fullSum, c) := bbAdd c partSum s0
  let (n0, c) := bbAddSigned c partSum s0 (-1)
  let laneStep : (List BB × Ctx) → Nat → (List BB × Ctx) := fun st i =>
    let (o, c1) := bbAddSigned st.2 fullSum (gb i) (diagCoeff i)
    let (o2, c2) := if fullWidthLane i then bbReduce c1 o else (o, c1)
    (st.1 ++ [o2], c2)
  let (rest, c) := ((List.range 15).map (· + 1)).foldl laneStep ([], c)
  (n0 :: rest, c)

/-- **THE PERMUTATION**, generated: the initial external layer, four external-initial rounds,
thirteen internal rounds, four external-final rounds — folded over the imported constants.

A final re-bound before the closing external layer keeps the output lanes usable by the next
permutation; note the closing add-only layer's 35× fan-in means the OUTPUT lanes are not `< 2³¹`,
which is why `provableCompress` reduces them again on the o1js side. -/
def permGen (c : Ctx) (input : List BB) : List BB × Ctx :=
  let (s, c) := mdsLightGen c input
  let (s, c) := rcExtInitial.foldl (fun (st : List BB × Ctx) rc =>
    externalRoundGen rc st.2 st.1) (s, c)
  let (s, c) := rcInternal.foldl (fun (st : List BB × Ctx) rc =>
    internalRoundGen rc st.2 st.1) (s, c)
  -- ⚑ The re-bound. The six small-coefficient internal lanes are deliberately left to grow ~2 bits
  -- a round; after thirteen rounds they are far past 2³¹, and an external round would then cube-
  -- and-square them past the Pasta modulus — UNSOUND, not slow. Each of these reductions is cheap
  -- (a one-limb quotient) because the bound is small, which is why the whole re-bound is ~4 rows a
  -- lane and not ~10.
  let (s, c) := s.foldl (fun (st : List BB × Ctx) l =>
      let (o, c') := if l.bound < 2 ^ 31 then (l, st.2) else bbReduce st.2 l
      (st.1 ++ [o], c')) ([], c)
  let (s, c) := rcExtFinal.foldl (fun (st : List BB × Ctx) rc =>
    externalRoundGen rc st.2 st.1) (s, c)
  (s, c)

/-! ## §3 — driving the generator, and reading the emitted object. -/

/-- Witness sixteen input lanes, each range-checked to be a legitimate private BabyBear input
(`assertLaneLt2p31` — without it the bound-tracking claim is vacuous). -/
def inputLanes (c : Ctx) (xs : List Nat) : List BB × Ctx :=
  let step : (List BB × Ctx) → Nat → (List BB × Ctx) := fun st i =>
    let (v, c1) := st.2.alloc ((xs.getD i 0 : Nat) : ℤ)
    let lane : BB := ⟨v, 2 ^ 31⟩
    (st.1 ++ [lane], bbRange64 c1 lane)
  (List.range 16).foldl step ([], c)

/-- The whole emission for one permutation on a concrete input. -/
def emitPerm (xs : List Nat) : List BB × Ctx :=
  let (inp, c) := inputLanes Ctx.start xs
  permGen c inp

/-- The emitted Kimchi rows. -/
def permRows (xs : List Nat) : List KRow := renderOps (emitPerm xs).2.ops.toList

/-- The canonical residues of the output lanes under the generated witness — what the circuit
actually computes. -/
def permOut (xs : List Nat) : List Nat :=
  let (s, c) := emitPerm xs
  s.map (fun l => ((c.get l.v) % (P : ℤ)).toNat)

/-- The largest tracked bound anywhere in the emission. -/
def maxBound (xs : List Nat) : Nat :=
  let (s, _) := emitPerm xs
  s.foldl (fun m l => max m l.bound) 0

/-! ### §3a — the acceptance check, over the emitted rows.

House convention (`Sha256Gadget.acceptB`, `PastaField.acceptB`): a `Bool`-valued evaluation of every
emitted gate body at the witness. This is what makes the differential a statement about the CIRCUIT
rather than about the reference function. -/

/-- Evaluate one generic sub-gate's body at the witness. -/
def gen1EvalB (c : Ctx) (g : Gen1) : Bool :=
  decide (g.cl * c.get g.l + g.cr * c.get g.r + g.co * c.get g.o
    + g.cm * (c.get g.l * c.get g.r) + g.cc = 0)

/-- Evaluate a `RangeCheck0` row: the eight crumbs are in `[0,4)`, the four plookup limbs are in
`[0,2¹²)` (the lookup argument's obligation, checked here on the witness), and the 88-bit
recomposition holds with the two copy columns zeroed. -/
def rc0EvalB (c : Ctx) (v c1 c2 p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 : Nat) : Bool :=
  let cols : List (Nat × Nat) :=
    [(c1, 76), (c2, 64), (p3, 52), (p4, 40), (p5, 28), (p6, 16),
     (k7, 14), (k8, 12), (k9, 10), (k10, 8), (k11, 6), (k12, 4), (k13, 2), (k14, 0)]
  let recomp : ℤ := (cols.map (fun q => (2 : ℤ) ^ q.2 * c.get q.1)).sum
  let crumbsOk := [k7, k8, k9, k10, k11, k12, k13, k14].all
    (fun i => decide (0 ≤ c.get i) && decide (c.get i < 4))
  let limbsOk := [p3, p4, p5, p6].all
    (fun i => decide (0 ≤ c.get i) && decide (c.get i < 4096))
  crumbsOk && limbsOk && decide (recomp = c.get v)

/-- One instruction, at the witness. -/
def opAcceptB (c : Ctx) : KOp -> Bool
  | .gen g => gen1EvalB c g
  | .rc0 v a b p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 =>
      rc0EvalB c v a b p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14
  | .zeroRow => true

/-- Every emitted instruction is satisfied by the generated witness. -/
def opsAcceptB (c : Ctx) : Bool := c.ops.toList.all (opAcceptB c)


/-- No tracked bound reaches the Pasta modulus — `assertSafe`, as a check rather than a comment. -/
def boundsSafe (xs : List Nat) : Bool := decide (maxBound xs < pastaN)

/-- Every witness value is a NON-NEGATIVE integer representative. This is the tripwire on the
subtraction compensation: `bbReduce` reads its input through `Int.toNat`, which turns a negative
into `0` SILENTLY, so a missing compensation would show up as a wrong digest rather than as an
error. This guard makes it show up here instead. -/
def valsNonneg (xs : List Nat) : Bool := (emitPerm xs).2.vals.all (fun v => decide (0 ≤ v))

/-! ## §4 — THE DIFFERENTIAL.

Against the Lean specification (which is `#guard`ed bit-exact to `default_babybear_poseidon2_16`)
and against the o1js measurement. -/

/-- The specification's own KAT input. -/
def katInput : List Nat := List.range 16

/-- Diagnostic: the index and shape of the first instruction the witness fails. -/
def firstBadOp : Option (Nat × KOp) :=
  let c := (emitPerm katInput).2
  (c.ops.toList.zipIdx.find? (fun q => ! opAcceptB c q.1)).map (fun q => (q.2, q.1))

def badOpCount : Nat :=
  let c := (emitPerm katInput).2
  (c.ops.toList.filter (fun o => ! opAcceptB c o)).length

def totalOps : Nat := (emitPerm katInput).2.ops.size

/-- The emitted row count for one permutation. -/
def permRowCount : Nat := (permRows katInput).length

/-- The gate histogram of the emitted permutation. -/
def permHistogram : List (KGateType × Nat) := gateHistogram (permRows katInput)

/-! ⚑ **No emitted instruction is unsatisfied by the generated witness.** This is the diagnostic
turned into a ratchet: `opsAcceptB` says "all rows hold", but a `#guard` on a conjunction tells you
nothing about WHICH row failed when it goes red, and this generator has already been wrong once in a
way only the row-level check caught (the 53-vs-64-bit quotient stride, §1b). `badOpCount = 0` and
`firstBadOp = none` keep the failure legible. -/
#guard badOpCount = 0
#guard firstBadOp.isNone
-- 3,920 until 2026-07-30; `Ctx.start`'s single `Gen1.isZero` pin is the 3,921st, and it is what
-- makes the 1,126 `RangeCheck0` rows constrain anything (see `bbRange64`).
#guard totalOps = 3921

/-! ⚑ **The emitted circuit computes the deployed permutation.** The generated witness's output
lanes, reduced canonically, are exactly `Poseidon2BabyBearW16.perm`'s — which is itself `#guard`ed
against `default_babybear_poseidon2_16().permute` at p3 rev `82cfad73`. -/
#guard permOut katInput = perm katInput

/-! The same on the all-zeros input, the specification's second pinned vector. -/
#guard permOut (List.replicate 16 0) = perm (List.replicate 16 0)

/-! ⚑ **The emitted circuit ACCEPTS that witness.** Every emitted row's body vanishes — so the two
`#guard`s above are a statement about the CIRCUIT, not merely about a reference function evaluated
alongside it. -/
#guard opsAcceptB (emitPerm katInput).2

/-! ⚑ **The bound tracking holds.** No intermediate could reach the Pasta modulus, which is the
line between a circuit that is slow and a circuit that is unsound. -/
#guard boundsSafe katInput

/-! Every witness value is a non-negative representative — the subtraction compensation is doing
its job everywhere, not just where the digest happens to notice. -/
#guard valsNonneg katInput

/-- The o1js measurement this is compared against: `Provable.constraintSystem` reports 2,602 rows
for one permutation and 8,673 for three, so the marginal cost is 2,600.5
(`bridge/mina-zkapp/scripts/poseidon2-babybear-rows.ts`, ratcheted at 2% by
`scripts/check-mina-attestation.sh`). -/
def O1JS_ROWS_PER_PERM : Nat := 2602

/-- The o1js gate mix for one permutation (`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.8):
`Generic 1,623 · RangeCheck0 701 · Lookup 278`. -/
def O1JS_GENERIC : Nat := 1623
def O1JS_RANGECHECK0 : Nat := 701
def O1JS_LOOKUP : Nat := 278

example : O1JS_GENERIC + O1JS_RANGECHECK0 + O1JS_LOOKUP = O1JS_ROWS_PER_PERM := rfl

/-! ## §6 — ⚑ THE MEASURED RESULT, and the delta.

**Digest: EXACT.** The emitted circuit's witness reproduces `Poseidon2BabyBearW16.perm` on both
pinned vectors, and every one of the 3,920 emitted instructions is satisfied by that witness. The
compiler emits a circuit that computes the deployed permutation, not a circuit that resembles it.

**Rows: 2,669 emitted against 2,602 measured in o1js — +67, or +2.6%.**

| | Generic | RangeCheck0 | Lookup | total |
|---|---:|---:|---:|---:|
| o1js 2.15.0, `Provable.constraintSystem` | 1,623 | 701 | 278 | **2,602** |
| this generator | 1,543 | 1,126 | 0 | **2,669** |

⚑ **THE TWO SIDES' RANGE ROWS NOW RECONCILE EXACTLY, AND THAT IS WORTH MORE THAN THE TOTAL.**
o1js's 278 `Lookup` rows are its 278 `assertLt2p31` calls (one per `reduce`), and its 701
`RangeCheck0` rows are the quotient limbs — 141 S-boxes × 4 limbs + 13 `partSum` + 117 full-width
lanes + the re-bound. This generator emits 16 input checks + 277 remainder checks + 833 quotient
limbs = 1,126, all labelled `RangeCheck0`. The **833 against 701** is the whole quotient delta and
it has one cause: `qLimbCount` needs `53·n ≥ bitLen(q)` while o1js's `quotientTimesP` needs
`64 + 53·(n−1) ≥ bitLen(q)` — it lets the FIRST limb carry the full 64 bits its range check already
covers and masks only the lower limbs to the 53-bit stride. On the S-box's `q ≈ 2^222` that is
**4 limbs against 5**, i.e. 141 of the 132-row gap. Adopting o1js's rule here needs the last limb
left unmasked (`bbReduce` masks every limb, which is right for its own count and wrong for o1js's)
and is the obvious next −141.

The two differences are both accounted for and neither is a modelling error:

1. **Every range check here is a `RangeCheck0` row; o1js splits them.** o1js's `rangeCheck3x12`
   (three 12-bit lookups, used by `assertLt2p31`) lands on `GateType::Lookup`, while its
   `rangeCheck64` lands on `RangeCheck0`. This generator routes both through `RangeCheck0`, whose
   four plookup columns already carry 4×12 bits under `LookupPattern::RangeCheck`
   (`lookup/lookups.rs:447-524`). Same ONE row either way, different label — so 979 o1js rows
   (701 + 278) correspond to 979 of the 1,126 here, and the gate mix is not comparable line by line.
2. **The remaining ~147 range rows and −81 generic rows are the quotient-limb schedule.**
   `qLimbCount` is driven by the tracked bound and is deliberately conservative; o1js's
   `quotientTimesP` computes a `soundMax` and throws if it is too loose, which lets it shave a limb
   where the bound is only just over a stride boundary. Batching quotient limbs across S-boxes into
   shared `multiRangeCheck` slots — named in `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.8 as the
   obvious 10–20% — is not done here.

**+2.6% is the honest reading and it is not a match.** The number that matters is that a GENERATED
circuit prices within a few percent of a hand-tuned one while computing the KAT: the compiler is
not paying a structural penalty for being a compiler. At 2,669 rows the Pickles arithmetic moves
from 25 permutations per 2^16 step to **24**, which is a ~4% step-count effect on any budget built
on it — worth naming, not worth hiding.

⚠ **AND THE COMPARISON IS NOT LIKE FOR LIKE ON SOUNDNESS.** §5d records that this generator's
`bbReduce` range-checks its remainder at 64 bits while tracking `2³¹`; o1js's `assertLt2p31` checks
it properly and costs one `Lookup` row for it. So the +67 is measured between a circuit that buys a
real `2³¹` bound and one that does not, and closing that gap here moves this side UP by ~586 rows,
not down. The honest reading of the row comparison is therefore: **the arithmetic and the linear
layers price at parity; the range discipline does not, and the gap is the `Lookup` gate this target
has not modelled.**

⚠ **This is one permutation, not a verifier.** `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` measures a
Merkle LEVEL at 2,677 rows and a whole FRI query at 684,726 — objects that consume a dregg proof.
The permutation is their dominant sub-object and the right first differential; it is not itself a
verification of anything.
-/

/-! ⚑ The emitted row count, pinned. Moving it is a deliberate act.

Moved once, deliberately: **2,668 → 2,669** on 2026-07-30. The `Ctx.start` zero pin is one generic
sub-gate at the head of the stream, and the instruction after it is a `RangeCheck0`, so `renderOpsGo`
has no partner to pack it with and flushes it as its own row. Exactly `+1`, and the parity of every
later run of generics is untouched. -/
#guard permRowCount = 2669

/-! The emitted gate mix, pinned: generic rows and range-check rows, nothing else. The `RangeCheck0`
count is unchanged by the zero pin — it added a generic, not a check. -/
#guard permHistogram.filter (fun x => x.2 != 0)
  = [(KGateType.generic, 1543), (KGateType.rangeCheck0, 1126)]

/-! The emission is within 3% of the o1js measurement. -/
#guard permRowCount * 100 < O1JS_ROWS_PER_PERM * 103

/-- Permutations that fit in one Pickles step at this price (`⌊65536 / 2668⌋ = 24`). -/
def permsPerPickleStep : Nat := PICKLES_MAX_ROWS / permRowCount

#guard permsPerPickleStep = 24

/-! ## §5 — what is PROVED about the generator, and what is only measured.

The primitives' forcing lemmas below are the composable half: each says a satisfying assignment is
COMPELLED to put the right value in the output variable. `permGen_forces` — the composition all the
way to "a satisfying assignment forces the output lanes to be `perm` of the input lanes" — is NOT
proved here and is the first item of the named remainder. What IS established is that the emitted
circuit is SATISFIED by a witness computing the KAT (§4), which is the completeness half and is
checked over the emitted rows themselves. -/

section Forcing

variable {R : Type} [CommRing R]

/-- An `bbAdd` output is forced to the sum. -/
theorem bbAdd_forces (a : Nat → R) (x y : BB) (o : Nat)
    (h : (Gen1.lin2 x.v y.v o 1 1).holds a) : a o = a x.v + a y.v := by
  have := Gen1.lin2_forces a x.v y.v o 1 1 h
  simpa using this

/-- A `bbMul` output is forced to the product — this is the S-box's whole content. -/
theorem bbMul_forces (a : Nat → R) (x y : BB) (o : Nat)
    (h : (Gen1.mul x.v y.v o).holds a) : a o = a x.v * a y.v :=
  Gen1.mul_forces a x.v y.v o h

/-- A `bbLin2` output is forced to the linear combination — the diagonal lanes' content. -/
theorem bbLin2_forces (a : Nat → R) (x y : BB) (o : Nat) (kx ky : ℤ)
    (h : (Gen1.lin2 x.v y.v o kx ky).holds a) : a o = (kx : R) * a x.v + (ky : R) * a y.v :=
  Gen1.lin2_forces a x.v y.v o kx ky h

/-- **The reduction's closing equation FORCES `v = q·p + r`.** With `r` range-checked below `2³¹`
and `q` below its limb bound, this is the foreign-modulus reduction, and it is the operation the
measured cost says is ~64% of the permutation. -/
theorem bbReduce_forces (a : Nat → R) (qp r v : Nat)
    (h : (Gen1.lin2 qp r v 1 1).holds a) : a v = a qp + a r := by
  have := Gen1.lin2_forces a qp r v 1 1 h
  simpa using this

end Forcing

/-- The generator emits only MODELLED gates, so nothing above is discharged by `KimchiTarget`'s
fail-closed `False`. -/
theorem permRows_all_modelled : ∀ r ∈ permRows katInput, r.gate.modelled = true :=
  renderOps_all_modelled _

/-! ## §5b — ⚑ THE S-BOX RUNG: TWO EMISSIONS, ONE `def`.

Route B's apex is `two_emissions_one_def`: two lowerings of one source, each with a forcing lemma
landing on the SAME Lean `def`, so the question "are these still the same semantics?" has an answer
that is not a differential. This is that shape for the permutation's **nonlinearity**, which is the
only place the two sides could disagree about anything but addition.

⚠ **AND IT IS THE S-BOX, NOT THE PERMUTATION.** `permGen_forces` — the composition all the way to
"a satisfying assignment forces the output lanes to be `perm` of the input lanes" — is still NOT
proved; it needs the fold induction through 141 S-boxes and the bound reasoning that keeps every
intermediate below the Pasta modulus. What §4 establishes for the whole permutation is the
COMPLETENESS half (the emitted circuit is SATISFIED by a witness computing the KAT, checked row by
row over the emitted object). What §5b establishes is the SOUNDNESS half for one rung. Saying
otherwise would be the vacuity this file's fail-closed target exists to make visible. -/

section SboxRung

variable {R : Type} [CommRing R]

/-- **ARROW ONE — the emitted Kimchi sub-gates force `x ↦ x⁷`.**

The four multiplication sub-gates `sboxGen` emits, at arbitrary `CommRing`. Each `Gen1.mul` forces
its output from its inputs regardless of aliasing or freshness (`KimchiLower` §3), so this composes
without a well-formedness side condition — which is what lets it be a rung rather than a lemma about
one emission. -/
theorem sbox_gens_force (a : Nat → R) (x x2 x4 x6 x7 : Nat)
    (h2 : (Gen1.mul x x x2).holds a) (h4 : (Gen1.mul x2 x2 x4).holds a)
    (h6 : (Gen1.mul x4 x2 x6).holds a) (h7 : (Gen1.mul x6 x x7).holds a) :
    a x7 = a x ^ 7 := by
  have e2 := Gen1.mul_forces a x x x2 h2
  have e4 := Gen1.mul_forces a x2 x2 x4 h4
  have e6 := Gen1.mul_forces a x4 x2 x6 h6
  have e7 := Gen1.mul_forces a x6 x x7 h7
  rw [e7, e6, e4, e2]
  ring

/-- The linear block, for the same reason: `mat4Gen`'s nine sub-gates force the `MDSMat4` circulant
row-for-row. Add-only, so the bound never multiplies and no reduction interposes — the whole
external layer is four of these plus the outer block-sum. -/
theorem mat4Gen_forces (a : Nat → R) (x0 x1 x2 x3 t01 t23 t0123 t01123 t01233 y0 : Nat)
    (h01 : (Gen1.lin2 x0 x1 t01 1 1).holds a)
    (h23 : (Gen1.lin2 x2 x3 t23 1 1).holds a)
    (h0123 : (Gen1.lin2 t01 t23 t0123 1 1).holds a)
    (h1 : (Gen1.lin2 t0123 x1 t01123 1 1).holds a)
    (h3 : (Gen1.lin2 t0123 x3 t01233 1 1).holds a)
    (hy0 : (Gen1.lin2 t01123 t01 y0 1 1).holds a) :
    a y0 = 2 * a x0 + 3 * a x1 + a x2 + a x3 := by
  have e01 := Gen1.lin2_forces a x0 x1 t01 1 1 h01
  have e23 := Gen1.lin2_forces a x2 x3 t23 1 1 h23
  have e0123 := Gen1.lin2_forces a t01 t23 t0123 1 1 h0123
  have e1 := Gen1.lin2_forces a t0123 x1 t01123 1 1 h1
  have ey0 := Gen1.lin2_forces a t01123 t01 y0 1 1 hy0
  rw [ey0, e1, e0123, e23, e01]
  push_cast
  ring

end SboxRung

/-- **ARROW TWO — the deployed BabyBear permutation's nonlinearity is the SAME `def`.**

`Poseidon2BabyBearW16.sbox` is what `externalRound` and `internalRound` apply, and the module it
lives in is `#guard`ed bit-exact against `default_babybear_poseidon2_16().permute` at p3 rev
`82cfad73`. Its body IS the four-multiplication chain arrow one forces, evaluated in `ℕ`-mod-`p`:
`x² · x² · x² · x` with a `% P` at every step. Stated as a definitional identity so the shared
target is visible rather than argued.

⚠ Arrow two is a KAT PIN, not a theorem. There is no Lean model of the deployed Rust to prove
against; `Poseidon2BabyBearW16`'s `#guard`s are what tie this `def` to the binary, and they are
checks over two vectors. Naming that is the difference between a weld and a claim. -/
theorem babybear_sbox_is_the_mul_chain (x : Nat) :
    Poseidon2BabyBearW16.sbox x
      = Poseidon2BabyBearW16.fmul
          (Poseidon2BabyBearW16.fmul
            (Poseidon2BabyBearW16.fmul (Poseidon2BabyBearW16.fmul x x)
              (Poseidon2BabyBearW16.fmul x x))
            (Poseidon2BabyBearW16.fmul x x)) x :=
  rfl

/-! ### §5c — the WELD: the abstract rung is about the ACTUAL emitted instructions.

`sbox_gens_force` is a statement about four `Gen1`s. Without this, nothing says the generator emits
those four — the lemma would be true and unattached, which is the shape a forcing lemma most often
fails in. The `#guard` runs `sboxGen` on a one-variable context and reads its instruction stream. -/

/-- A `KOp` as a generic sub-gate, when it is one. -/
def opAsGen : KOp → Option Gen1
  | .gen g => some g
  | .rc0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => none
  | .zeroRow => none

/-- One variable holding a lane value, and nothing else — the smallest context an S-box can run in. -/
def sboxProbe : Ctx := (Ctx.empty.alloc 5).2

/-- ⚑ **The generator really does emit that multiplication chain**, at the variable indices its own
allocator hands out. Change `sboxGen`'s shape and this goes red before any row count moves. -/
#guard ((sboxGen sboxProbe ⟨0, 2 ^ 31⟩).2.ops.toList.take 4).map opAsGen
  = [some (Gen1.mul 0 0 1), some (Gen1.mul 1 1 2), some (Gen1.mul 2 1 3), some (Gen1.mul 3 0 4)]

/-- Satisfiability at birth, positive polarity: the S-box emission on lane `5` accepts its own
generated witness, and the witness computes `5⁷ mod p`. A forcing lemma over an unsatisfiable
circuit is true for free. -/
#guard opsAcceptB (sboxGen sboxProbe ⟨0, 2 ^ 31⟩).2

#guard (let (o, c) := sboxGen sboxProbe ⟨0, 2 ^ 31⟩; c.get o.v) = ((5 ^ 7 % P : Nat) : ℤ)

/-- Negative polarity: the emitted chain REFUSES an assignment that puts anything else in the output.
`opAcceptB` is evaluated at the generated witness with the final variable moved by one, and the
`Gen1.mul` that defines it stops vanishing. -/
#guard
  (let (o, c) := sboxGen sboxProbe ⟨0, 2 ^ 31⟩
   let bad : Ctx := { c with vals := c.vals.set! o.v (c.get o.v + 1) }
   ! opsAcceptB bad)

/-! ### §5d — ⚑ THE REMAINING BOUND GAP, AS A CHECK RATHER THAN A COMMENT.

`bbReduce` returns its remainder with a tracked bound of `2³¹` and range-checks it with `bbRange64`,
which is **64 bits**. `inputLanes` does the same to every private input. So the emitted circuit
enforces `2⁶⁴` where the bound chain — and therefore `boundsSafe`, and therefore the claim that field
arithmetic still agrees with integer arithmetic — needs `2³¹`. A lane at `2⁶⁴` puts `x⁷` at ~`2^485`
against a Pasta modulus of ~`2^254`.

`boundsSafe` cannot see this: it reads TRACKED bounds. That is the same shape as the o1js-side defect
fixed in `bridge/mina-zkapp/src/Poseidon2BabyBearW16.ts` on 2026-07-30 (a check enforcing `2^32.005`
under a tracked `2³¹`), one storey worse, and it is why the wound gets an instrument here instead of
a paragraph.

**Why it is not simply fixed:** getting `< 2³¹` out of `KimchiTarget`'s vocabulary costs a SECOND
`RangeCheck0` on `2³¹ − 1 − r` plus a generic to form it — the two-sided trick — at ~293 sites, i.e.
~+586 rows on 2,669. o1js buys the same bound in one row because it can emit `GateType::Lookup`
(`rangeCheck3x12`), and `KGateType.modelled` does not include `lookup`, so this generator cannot.
**That is the price of the fail-closed vocabulary, and modelling `Lookup` in `KimchiTarget` is what
closes it back to parity.** Named in the remainder with its price, not deferred silently.

The guard below is the wound, in the polarity that makes it detectable: it ASSERTS that a value far
past `2³¹` is accepted by the row a `2³¹`-tracked lane gets. It goes RED the day the gadget is
tightened — at which point the fix is to flip it, not to delete it. -/

/-- A lane at `2⁶³ − 1` presented to the range check a `2³¹`-tracked lane receives. -/
def rangeGapCtx : Ctx :=
  let (v, c) := Ctx.start.alloc (((2 ^ 63 - 1 : Nat) : ℤ))
  bbRange64 c ⟨v, 2 ^ 31⟩

/-- ⚑ **THE GAP, ASSERTED.** `2⁶³ − 1` satisfies the row. The enforced bound is at least `2⁶³`
where the tracked bound is `2³¹` — 32 bits of daylight, in the operation that is 64% of the
permutation's cost. -/
#guard opsAcceptB rangeGapCtx

/-! ## §7 — THE EMITTED ARTIFACT.

The o1js consumer must not re-author anything, so it reads THIS: the instruction stream verbatim,
with the variable indices and coefficients the generator produced. `Gates.generic` takes exactly
`Gen1.body`'s five coefficients and `Gates.rangeCheck0` takes exactly `mkRangeCheck0`'s fifteen
columns, so the TypeScript side is a transcription loop and contains no Poseidon2 at all — no round
constant, no diagonal, no round structure, nothing it could get wrong independently.

⚑ **THE INSTRUCTION STREAM IS INPUT-INDEPENDENT AND THAT IS WHAT MAKES A STATIC ARTIFACT LEGITIMATE.**
`emitPerm` takes a concrete input because it generates a WITNESS alongside the circuit, but every
`KOp` carries variable INDICES and COEFFICIENTS only: allocation order is driven by the round
structure, `qLimbCount` by tracked BOUNDS, and `bbAddSigned`'s compensation by `pCeil` of a bound.
None of those read a value. So one emission serves every input, and the consumer supplies the
sixteen input lanes and solves for the rest. -/

private def i2s (z : ℤ) : String := toString z

private def joinS (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinS sep xs

/-- One instruction as JSON. `g` is a generic sub-gate, `r` a standalone 64-bit `RangeCheck0` with
its fifteen columns in `rc0Places` order, `z` a companion `Zero` row. -/
def opJson : KOp → String
  | .gen g =>
      "{\"k\":\"g\",\"l\":" ++ toString g.l ++ ",\"r\":" ++ toString g.r
        ++ ",\"o\":" ++ toString g.o ++ ",\"cl\":" ++ i2s g.cl ++ ",\"cr\":" ++ i2s g.cr
        ++ ",\"co\":" ++ i2s g.co ++ ",\"cm\":" ++ i2s g.cm ++ ",\"cc\":" ++ i2s g.cc ++ "}"
  | .rc0 v c1 c2 p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 =>
      "{\"k\":\"r\",\"w\":["
        ++ joinS "," ([v, c1, c2, p3, p4, p5, p6, k7, k8, k9, k10, k11, k12, k13, k14].map toString)
        ++ "]}"
  | .zeroRow => "{\"k\":\"z\"}"

/-- The variable indices of the sixteen input lanes. -/
def inputVars : List Nat := (inputLanes Ctx.start katInput).1.map (fun l => l.v)

/-- The variable indices of the sixteen output lanes. -/
def outputVars : List Nat := (emitPerm katInput).1.map (fun l => l.v)

/-- The tracked bound on each output lane — what a caller must carry to stay sound. -/
def outputBounds : List Nat := (emitPerm katInput).1.map (fun l => l.bound)

/-- Every variable the emission mentions. -/
def nVars : Nat := (emitPerm katInput).2.vals.size

/-- **THE ARTIFACT.** Everything the o1js side needs and nothing it could reinterpret.

`honestVals` is the generator's own witness at `katInput`. The TypeScript solver reads only the
emitted coefficients, so it is an INDEPENDENT implementation; agreeing with this vector is what keeps
it from being a third opinion about the same circuit, exactly as `honestFresh` does for route B. -/
def emitJson : String :=
  "{\"air\":\"poseidon2-babybear-w16-kimchi\""
    ++ ",\"source\":\"Dregg2.Circuit.Emit.KimchiPoseidon2.permGen\""
    ++ ",\"width\":16"
    ++ ",\"modulus\":" ++ toString P
    ++ ",\"zeroVar\":" ++ toString ZERO_VAR
    ++ ",\"nVars\":" ++ toString nVars
    ++ ",\"subGates\":" ++ toString totalOps
    ++ ",\"kimchiRows\":" ++ toString permRowCount
    ++ ",\"inputVars\":[" ++ joinS "," (inputVars.map toString) ++ "]"
    ++ ",\"outputVars\":[" ++ joinS "," (outputVars.map toString) ++ "]"
    ++ ",\"outputBounds\":[" ++ joinS "," (outputBounds.map toString) ++ "]"
    ++ ",\"honestInput\":[" ++ joinS "," (katInput.map toString) ++ "]"
    ++ ",\"honestOutput\":[" ++ joinS "," ((permOut katInput).map toString) ++ "]"
    ++ ",\"honestVals\":[" ++ joinS "," ((emitPerm katInput).2.vals.toList.map i2s) ++ "]"
    ++ ",\"prog\":[" ++ joinS "," ((emitPerm katInput).2.ops.toList.map opJson) ++ "]}"

/-! ### §7a — the artifact's own tripwires. -/

#guard inputVars.length = 16
#guard outputVars.length = 16
/-- Every variable the program mentions is inside `[0, nVars)` — what makes `honestVals` the WHOLE
witness and not a prefix of one. -/
#guard (emitPerm katInput).2.ops.toList.all (fun o =>
  match o with
  | .gen g => g.l < nVars && g.r < nVars && g.o < nVars
  | .rc0 v c1 c2 p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 =>
      [v, c1, c2, p3, p4, p5, p6, k7, k8, k9, k10, k11, k12, k13, k14].all (fun i => i < nVars)
  | .zeroRow => true)
/-- The pinned zero really is pinned, and it really is variable `ZERO_VAR`. -/
#guard (emitPerm katInput).2.get ZERO_VAR = 0
#guard opAsGen ((emitPerm katInput).2.ops.toList.getD 0 .zeroRow) = some (Gen1.isZero ZERO_VAR)
/-- The output lanes are NOT `< 2³¹`: the last thing that runs is the add-only external layer with
fan-in 35, so a consumer chaining permutations must reduce before re-feeding. Carried in the artifact
rather than left to a reader. -/
#guard outputBounds.all (fun b => 2 ^ 31 < b)

#assert_axioms bbMul_forces
#assert_axioms bbLin2_forces
#assert_axioms bbReduce_forces
#assert_axioms sbox_gens_force
#assert_axioms mat4Gen_forces
#assert_axioms babybear_sbox_is_the_mul_chain
#assert_axioms permRows_all_modelled

end Dregg2.Circuit.Emit.KimchiPoseidon2
