/-
# `KimchiWrapMainField` — the **Fq / Vesta** VALUE LAYER under `KimchiWrapMain`

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** Nothing here is a constraint; it is the arithmetic a `wrap_main`
witness is made of. `proof-systems` RUNS the artifact and authors no constraint. House Law #1.

## WHY THIS FILE EXISTS AT ALL

Two reasons, and the second is the load-bearing one.

  1. `KimchiWrapMain.lean` was 2013 lines and 150 s to elaborate. The step side's single file hit
     2437 s before it was split into seventeen; the recipe there was `Field` (constants) / `Core`
     (defs) / `Fixture` / `PinsNN`, and this is that file's `Field`.
  2. ⚑ **`wrap_verifier.ml:539-617` puts the x_hat MSM's OUTPUT into the transcript.** `absorb sponge
     PC x_hat` at `:617` is fed by the MSM at `:539-616`, and the MSM reads no sponge state at all —
     it is bases (SRS constants) times the packed previous STEP statement. So the value `x_hat` has
     to be computable BEFORE `KimchiWrapMain`'s §2 schedule, and Lean is order-sensitive. Emitting
     the MSM below the schedule and leaving `x_hat` a fixture above it would be exactly the shape
     this campaign calls a value the file fakes and calls derived.

## ⚑ Fq, NOT Fp — and Vesta, not Pallas

`wrap_main_inputs.ml:11-12` — `Me = Tock`, so the wrap circuit's native field is `Tock.Field = Fq`.
`wrap_verifier.ml:45-49` types `Inner_curve` with `Impl.field = Backend.Tock.Field` and
`Inner_curve.Constant.Scalar.t = Backend.Tick.Field`; a curve whose BASE field is Fq and whose SCALAR
field is Fp is **Vesta**. Every arithmetic function below is `% qN`, and `KimchiRenderVarBaseMul` /
`KimchiRenderCompleteAdd` are deliberately NOT reused: both are hardcoded to `pN`
(`KimchiRenderVarBaseMul.lean:62-74`, `KimchiRenderCompleteAdd.lean:66-83`), and a single `% pN`
reaching a wrap witness cell is a silent field confusion that every gate would still accept.

Vesta and Pallas share `y² = x³ + 5` (`PastaCurve.lean:96`), so the FORMULAS are the same and only
the modulus moves; `xhat_bases_are_on_vesta` checks the bases against the Fq curve equation rather
than trusting that.

## What is here

  * `qInv` and the Vesta affine ops (`complete_add`'s eleven cells, `add_fast`, doubling, negate).
  * `stepVbmQ` / `runVbmQ` — `scale_fast_unpack`'s per-bit chain (`plonk_curve_ops.ml:150-213`) at Fq.
  * ⚑ **`xhatBits`** — the packed STEP statement's PER-ENTRY widths, read at source and cross-checked
    against `MinaStepSrsLagrange.WIDTHS`, which a Rust binary printed independently.
  * `runXhat` — the whole MSM as a value: corrections reduced into `init`, then the 67-entry fold in
    `List.foldi` order, then `Inner_curve.negate`, then `x_hat blinding`.

## Axiom hygiene / build

NO `main`. No `sorry`, no `native_decide`. The facts are NAMED THEOREMS closed by `decide`/`rfl` in
the kernel; `#assert_namespace_axioms` at the foot accounts for every one.
-/
import Dregg2.Tactics
import Dregg2.Circuit.Emit.PastaField
import Dregg2.Circuit.Emit.MinaStepSrsLagrange

namespace Dregg2.Circuit.Emit.KimchiWrapMain

open Dregg2.Circuit.Emit.PastaField (qN)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §0 — **Fq** arithmetic.

Every value in this file and in `KimchiWrapMain` lives mod `qN`. Nothing is shared with
`KimchiStepMain`, which is mod `pN`; a single `% pN` reaching either file would be a silent field
confusion, so the arithmetic is defined once, here, and the two constants a copy-paste would get
wrong are pinned in `KimchiWrapMain` §11a/§11b. -/

/-- `x + y` over `Fq`. -/
def qAdd (x y : Nat) : Nat := (x + y) % qN
/-- `x − y` over `Fq`. -/
def qSub (x y : Nat) : Nat := (x + qN - y % qN) % qN
/-- `x · y` over `Fq`. -/
def qMul (x y : Nat) : Nat := (x * y) % qN

private def qPowAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, base, e, acc =>
      if e == 0 then acc
      else qPowAux fuel ((base * base) % qN) (e / 2) (if e % 2 == 1 then (acc * base) % qN else acc)

/-- **`qInv`** — the `Fq` multiplicative inverse by Fermat (`a^(q−2) mod q`), `qN` prime.
`qN − 2 < 2^255`, so 260 units of fuel are ample. -/
def qInv (a : Nat) : Nat := qPowAux 260 (a % qN) (qN - 2) 1

theorem q_inv_is_an_inverse :
    qMul 7 (qInv 7) = 1 ∧ qMul (qN - 1) (qInv (qN - 1)) = 1 := by decide

/-! ## §0b — the **Vesta** affine ops, at Fq.

`y² = x³ + 5` — the same short-Weierstrass shape as Pallas (`PastaCurve.lean:96`, `b = 5` shared),
so the formulas below are `KimchiRenderCompleteAdd`'s and `KimchiRenderVarBaseMul`'s with the
modulus moved. That is stated rather than assumed: reusing those modules verbatim would have run
Vesta coordinates through `% pN`. -/

/-- The `add_fast` slope `(y₂−y₁)/(x₂−x₁)` (distinct-x case). -/
def qAddSlope (x1 y1 x2 y2 : Nat) : Nat := qMul (qSub y2 y1) (qInv (qSub x2 x1))
/-- The doubling slope `3x₁²/(2y₁)`. -/
def qDblSlope (x1 y1 : Nat) : Nat := qMul (qMul 3 (qMul x1 x1)) (qInv (qMul 2 y1))

/-- **`caWitnessQ P Q`** — the eleven `complete_add` cells
`[x₁,y₁,x₂,y₂,x₃,y₃,inf,same_x,s,inf_z,x21_inv]`, exactly per
`complete_add.rs::verify_complete_add`, over **Fq**. -/
def caWitnessQ (x1 y1 x2 y2 : Nat) : List Nat :=
  let sameX := if x1 == x2 then 1 else 0
  let s := if x1 == x2 then qDblSlope x1 y1 else qAddSlope x1 y1 x2 y2
  let x3 := qSub (qSub (qMul s s) x1) x2
  let y3 := qSub (qMul s (qSub x1 x3)) y1
  let inf := if x1 == x2 && y1 != y2 then 1 else 0
  let infZ := if y1 == y2 then 0 else if x1 == x2 then qInv (qSub y2 y1) else 0
  let x21Inv := if x1 == x2 then 0 else qInv (qSub x2 x1)
  [x1, y1, x2, y2, x3, y3, inf, sameX, s, infZ, x21Inv]

/-- `Ops.add_fast P Q` as a value — the `complete_add` row's output cells. -/
def addAQ (P Q : Nat × Nat) : Nat × Nat :=
  let c := caWitnessQ P.1 P.2 Q.1 Q.2
  (c.getD 4 0, c.getD 5 0)

/-- Affine doubling. -/
def dblAQ (P : Nat × Nat) : Nat × Nat :=
  let s := qDblSlope P.1 P.2
  let x3 := qSub (qSub (qMul s s) P.1) P.1
  (x3, qSub (qMul s (qSub P.1 x3)) P.2)

/-- `Inner_curve.negate (x, y) = (x, F.negate y)` (`snarky_curve.ml:206`) — a `Cvar` scale, which is
why it costs no row upstream. -/
def negAQ (P : Nat × Nat) : Nat × Nat := (P.1, qSub 0 P.2)

/-- `y² = x³ + 5` over **Fq** — the Vesta curve equation. -/
def onCurveQ (P : Nat × Nat) : Bool := qMul P.2 P.2 == qAdd (qMul P.1 (qMul P.1 P.1)) 5

/-! ## §0c — `scale_fast_unpack`'s per-bit chain, at Fq.

`plonk_curve_ops.ml:150-213`, verbatim: `sᵢ = (yᵢ − (2bᵢ−1)·yT)/(xᵢ − xT)`,
`s₂ = 2yᵢ/(2xᵢ + xT − sᵢ²) − sᵢ`, `xᵢ₊₁ = xT + s₂² − sᵢ²`, `yᵢ₊₁ = (xᵢ − xᵢ₊₁)·s₂ − yᵢ`, i.e.
`accᵢ₊₁ = [2]accᵢ + (2bᵢ−1)·T`, alongside `nₖ₊₁ = 2nₖ + bₖ`. -/

/-- One `single_bit` step: `(sᵢ, xᵢ₊₁, yᵢ₊₁)`. `bsign = 2b − 1 ∈ {−1, 1}`. -/
def stepVbmQ (xT yT xi yi b : Nat) : Nat × Nat × Nat :=
  let bsign := if b == 1 then (1 : Nat) else qN - 1
  let s := qMul (qSub yi (qMul bsign yT)) (qInv (qSub xi xT))
  let ssq := qMul s s
  let s2 := qSub (qMul (qMul 2 yi) (qInv (qSub (qAdd (qMul 2 xi) xT) ssq))) s
  let xo := qSub (qAdd xT (qMul s2 s2)) ssq
  (s, xo, qSub (qMul (qSub xi xo) s2) yi)

/-- One ladder's stored trace: the base, the `5·chunks + 1` accumulator points, the `5·chunks`
slopes, and the counter at every chunk boundary. -/
structure TermDataQ where
  T : Nat × Nat
  accs : List (Nat × Nat)
  slopes : List Nat
  /-- `nₖ` at BIT boundaries — the chunk-boundary values are every fifth. -/
  ns : List Nat
  deriving Repr, Inhabited

/-- Run the chain. `acc₀` is `Ops.add_fast base base` (`plonk_curve_ops.ml:157`) and `n₀ = 0`
(`:158`); both are supplied by the caller so the emitter can PIN them rather than leave them free. -/
def runVbmQ (T acc0 : Nat × Nat) (bits : List Nat) : TermDataQ :=
  let st := bits.foldl
    (fun (st : List (Nat × Nat) × List Nat × List Nat) b =>
      let cur := st.1.getLastD (0, 0)
      let r := stepVbmQ T.1 T.2 cur.1 cur.2 b
      (st.1 ++ [(r.2.1, r.2.2)], st.2.1 ++ [r.1], st.2.2 ++ [2 * st.2.2.getLastD 0 + b]))
    ([acc0], [], [0])
  { T := T, accs := st.1, slopes := st.2.1, ns := st.2.2 }

/-! ## ⚑⚑ §15a — **THE PACKED STEP STATEMENT'S PER-ENTRY WIDTHS**, read at source.

`wrap_main.ml:404-411` feeds `incrementally_verify_proof` with

    Array.map (pack_statement Max_proofs_verified.n prev_statement) ~f:(function
      | `Field (Shifted_value x) -> `Field (split_field x)
      | `Packed_bits (x, n)      -> `Packed_bits (x, n))

and `pack_statement` (`wrap_main.ml:33-38`) is `Spec.pack (module Impl) (Types.Step.Statement.spec
max_proofs_verified Backend.Tock.Rounds.n) (Statement.to_data t)`. Then `wrap_verifier.ml:542-548`
expands each entry:

    | `Field (x, b)      -> [| `Field (x, Field.size_in_bits); `Field ((b :> Field.t), 1) |]
    | `Packed_bits (x,n) -> [| `Field (x, n) |]

### The 57 packed words

`Types.Step.Statement.spec proofs_verified bp_log2` (`composition_types.ml:1453-1459`) is

    Struct [ Vector (per_proof, proofs_verified) ; B Digest ; Vector (B Digest, proofs_verified) ]

and `per_proof = Proof_state.Per_proof.In_circuit.spec bp_log2` (`:1268-1276`) is

    Struct [ Vector (B Field, N5) ; Vector (B Digest, N1) ; Vector (B Challenge, N2)
           ; Vector (Scalar Challenge, N3) ; Vector (B Bulletproof_challenge, bp_log2)
           ; Vector (B Bool, N1) ]

At `proofs_verified = Max_proofs_verified.n = 2` and `bp_log2 = Backend.Tock.Rounds.n = 15` that is
`2 × 27 + 1 + 2 = 57` words. `pack_basic` (`spec.ml:360-393`) gives each a width: `Field` →
`` `Field x `` (255 through `Field.size_in_bits`), `Digest` → 255, `Challenge` /
`Scalar Challenge` / `Bulletproof_challenge` → `Challenge.length = 64 · 2 = 128`
(`limb_vector/constant.ml:71`), `Bool` → 1.

⚠ **`bp_log2` here is `Tock.Rounds.n = 15`, not `Tick`'s 16.** This is the STEP statement, whose
`bulletproof_challenges` are the WRAP proof's IPA rounds — the mirror image of the step side's
§1b, where the WRAP statement carries `Tick.Rounds.n = 16`. Carrying 16 across would have made a
68-entry MSM and put the census one ladder out.

### The 67 entries

Each of the 10 `` `Field `` words becomes TWO entries — a 255-bit value and a 1-bit parity — so
`57 + 10 = 67`, laid out as two 32-entry `per_proof` blocks and then three `Digest`s:

    j = 0..9    the five `B Field` words, as (255, 1) pairs
    j = 10      `B Digest`                                   255
    j = 11..30  2 Challenge + 3 Scalar Challenge + 15 Bulletproof_challenge   128
    j = 31      `B Bool` (should_finalize)                     1
    i = 64      messages_for_next_step_proof   `B Digest`    255
    i = 65,66   messages_for_next_wrap_proof   `B Digest`    255

**Census: 15 × 255, 40 × 128, 12 × 1.** ⚑ And that census is not this file's word for it:
`MinaStepSrsLagrange.WIDTHS` is the same list printed by a Rust binary that walked the real SRS,
and `xhat_widths_agree_with_the_extractor` is the equality.

### ⚑ …and Mina's own compiled wrap circuit says the same number

`mina-canonical-circuit-oracle.mjs --circuit wrap-transaction` reports **`VarBaseMul 2417`**. The
whole circuit's `VarBaseMul` gates come from exactly three places, and each is `chunks_needed`
applied to a width read at source:

    W-XHAT     15 × chunks_needed 254 + 40 × chunks_needed 127 = 15 × 51 + 40 × 26 = 1805
    W-FTCOMM   8 `scale_fast` at `Other_field.Packed.Constant.size_in_bits = 255`
               (`common.ml:238-256` has 1 + 6 + 1 scales at `tComms = 7`)  = 8 × 51 =  408
    W-BULLET   the FOUR `scale_fast` of `check_bulletproof` (`wrap_verifier.ml:411,428,430,433`)
                                                                            = 4 × 51 =  204
                                                                                       ----
                                                                                       2417

`xhat_chunk_census_closes_minas_var_base_mul_count` is that arithmetic as a theorem. It is the
strongest independent check this census has: a wrong per-entry width, a wrong entry count or a
wrong `bp_log2` all miss 2417. -/

/-- `Ops.chunks_needed ~num_bits` — `(num_bits + bits_per_chunk − 1) / bits_per_chunk` at
`bits_per_chunk = 5` (`plonk_curve_ops.ml:64-68`). -/
def chunksNeededQ (numBits : Nat) : Nat := (numBits + 4) / 5

/-- `Ops.bits_per_chunk` (`plonk_curve_ops.ml:57`). -/
def BITS_PER_CHUNK : Nat := 5

/-- `Field.size_in_bits` — `B Field` and `B Digest`. -/
def WQ_FIELD : Nat := 255
/-- `Challenge.length = 64 · Nat.to_int N2` — `Challenge`, `Scalar Challenge`,
`Bulletproof_challenge`. -/
def WQ_CHAL : Nat := 128
/-- `B Bool`, and the parity half of every split `` `Field ``. -/
def WQ_BOOL : Nat := 1

/-- Entries per `per_proof` block after `wrap_verifier.ml:542-548`'s expansion: 5 `Field` → 10,
plus 1 Digest + 2 + 3 + 15 challenges + 1 Bool. -/
def XHAT_PER_PROOF : Nat := 32
/-- `Max_proofs_verified.n` for the compiled wrap circuits. -/
def XHAT_PREVS : Nat := 2
/-- **67** — every entry `wrap_verifier.ml:539-548` produces. -/
def XHAT_TERMS_FULL : Nat := XHAT_PER_PROOF * XHAT_PREVS + 1 + XHAT_PREVS

/-- ⚑ Entry `i`'s packed bit width. -/
def xhatBits (i : Nat) : Nat :=
  if i ≥ XHAT_PER_PROOF * XHAT_PREVS then WQ_FIELD          -- the three trailing `B Digest`s
  else
    let j := i % XHAT_PER_PROOF
    if j < 10 then (if j % 2 == 0 then WQ_FIELD else WQ_BOOL)  -- 5 × `B Field` → (value, parity)
    else if j == 10 then WQ_FIELD                              -- `B Digest`
    else if j < 31 then WQ_CHAL                                -- 2 + 3 + 15 challenge words
    else WQ_BOOL                                               -- `B Bool` should_finalize

/-- ⚑ Entry `i`'s 5-bit chunk count. A one-bit entry takes the `` `Cond_add `` path
(`wrap_verifier.ml:573-577`) and runs NO ladder; every other entry is `Ops.scale_fast2'`, whose
`chunks_needed` is applied to `num_bits − 1` (`plonk_curve_ops.ml:250-256`). -/
def xhatChunksAt (i : Nat) : Nat :=
  if xhatBits i == WQ_BOOL then 0 else chunksNeededQ (xhatBits i - 1)

/-- `actual_bits_used = chunks_needed × bits_per_chunk` (`plonk_curve_ops.ml:254`) — the ladder's
ACTUAL width, which for a 128-bit entry is **130**, not 128. -/
def xhatActualBits (i : Nat) : Nat := BITS_PER_CHUNK * xhatChunksAt i

/-- ⚑ How many TOP bits `scale_fast2` asserts zero (`plonk_curve_ops.ml:262-265`):
`for i = s_div_2_bits to Array.length bits_lsb − 1`, i.e. `actual_bits_used − (num_bits − 1)`
positions. **255 → 1, 128 → 3.** These are defect class 2's second half inside the MSM, and the
emitter has to make them σ-classable cells rather than advice. -/
def xhatTopZeros (i : Nat) : Nat :=
  if xhatChunksAt i == 0 then 0 else xhatActualBits i - (xhatBits i - 1)

/-- Chunks over the entries below `n`. -/
def xhatChunkPrefix (n : Nat) : Nat := ((List.range n).map xhatChunksAt).foldl (· + ·) 0

/-- ⚑ **WHICH entries a reduced shape emits.** At `XHAT_TERMS_FULL` this is every entry in order,
which is what the committed wrap shape uses and what `wrap_verifier.ml:539-609` does. Below it, the
selection is a NAMED spread — not a prefix — because a prefix of fewer than twelve never reaches a
128-bit entry, and a smoke shape that cannot reach one cannot exercise the three-bit top-zero
assert. It covers both partitions and all three widths.

⚑ **ENTRY 64 MOVED TO POSITION 3 AT `w9_prev`, AND THAT IS A GATE AND NOT A PREFERENCE.** Entry 64
is packed word `PREV_MSG_NEXT_STEP`, the one `wrap_main.ml:350-351` ties to a PUBLIC word. A smoke
shape that exposes that word while its MSM never reads the variable would be a public word tied to a
cell no other row constrains — defect class 5 wearing a public vector, in the very rung that adds
it. So the smoke shape selects it. -/
def xhatSel (n : Nat) : List Nat :=
  if n ≥ XHAT_TERMS_FULL then List.range XHAT_TERMS_FULL
  else ([0, 1, 11, 64, 31, 10, 12, 2] : List Nat).take n

/-! ## §15b — the BASES, and where they come from.

`MinaStepSrsLagrange` holds them; `MinaStepSrsLagrangePin` proves the SRS construction that produced
them reproduces Mina's devnet SRS coordinate for coordinate. Nothing here owns a literal. -/

/-- Entry `i`'s base — `lagrange ~domain srs i` / `lagrange_with_correction`'s first component. -/
def xhatBase (i : Nat) : Nat × Nat :=
  (Dregg2.Circuit.Emit.MinaStepSrsLagrange.LAGRANGE_XY.getD (2 * i) 0,
   Dregg2.Circuit.Emit.MinaStepSrsLagrange.LAGRANGE_XY.getD (2 * i + 1) 0)

/-- Where entry `i`'s correction sits in `CORRECTION_XY`, which is indexed over the
`Add_with_correction` partition only. -/
def xhatCorrIdx (i : Nat) : Nat :=
  ((List.range i).filter (fun k => xhatChunksAt k != 0)).length

/-- Entry `i`'s correction — `negate (pow2pow g actual_shift)`, `wrap_verifier.ml:255-256`. -/
def xhatCorr (i : Nat) : Nat × Nat :=
  (Dregg2.Circuit.Emit.MinaStepSrsLagrange.CORRECTION_XY.getD (2 * xhatCorrIdx i) 0,
   Dregg2.Circuit.Emit.MinaStepSrsLagrange.CORRECTION_XY.getD (2 * xhatCorrIdx i + 1) 0)

/-- `Generators.h` — the STEP URS's blinding base, which `x_hat blinding` adds. -/
def XHAT_H : Nat × Nat :=
  (Dregg2.Circuit.Emit.MinaStepSrsLagrange.URS_H_XY.getD 0 0,
   Dregg2.Circuit.Emit.MinaStepSrsLagrange.URS_H_XY.getD 1 0)

/-! ## §15c — the SCALARS, and where they come from AFTER `w9_prev`.

⚠ ⚑ **THE SCALARS ARE STILL FREE WITNESSES, AND SAYING OTHERWISE WOULD BE THE WHOLE DEFECT.**
Entry `i`'s scalar is a packed word of `prev_statement`, which `wrap_main.ml:201-256` obtains as
`exists ~request:Req.Proof_state` — a witnessed previous STEP proof state. It is free UPSTREAM too;
what ties it there is W-FINALIZE (`finalize_other_proof` consumes the deferred values), W-WRAPHACK
(the two `hash_messages_for_next_wrap_proof` digests) and `assert_eq_plonk`.

So `x_hat` does NOT leave `WRAP_UNCONSUMED`, at `w6_xhat` or at `w9_prev`. What changed at
`w6_xhat`: `x_hat` stopped being a fixture pair the prover handed the sponge and became the image of
67 scalars under an MSM over bases the circuit PINS. What changes at `w9_prev` is narrower and also
real, and it is a change to THIS file:

  * the 67 scalars stop being 67 INDEPENDENT draws and become the packed image of **57** statement
    words under `Spec.pack` + `split_field` — `xhatWordOf` is that map, and it is many-to-one exactly
    where `wrap_verifier.ml:542-548` expands a `` `Field `` into a (value, parity) pair;
  * so `split_field`'s recomposition `2·hi + is_odd = x` is an IDENTITY on the witness rather than a
    definition of `x` — `w7_split`'s `x` was a downward-derived cell and is now the statement word
    itself (`split_field_recomposes_the_statement_word`);
  * and word 54 (`messages_for_next_step_proof`) is `Field.Assert.equal`-tied to a PUBLIC word
    (`wrap_main.ml:350-351`), which is `w9_prev`'s 23rd.

Sixty-six of the 67 are still the prover's, so an MSM over them still spans the group. The census
says so rather than dropping the entry.

⚑ **THE 57 WORDS' VALUES ARE A NAMED FIXTURE AND UPSTREAM'S ARE A FREE WITNESS** — those are the
same thing, and this is the one place in the chain where a fixture is the FAITHFUL choice rather
than a stand-in for a derivation. What is NOT free is the SHAPE: each word is reduced to the width
`spec.ml:374-392` packs it at, so `scale_fast2`'s top-bit asserts have something honest to assert,
and the derived split halves land inside their own widths by construction. -/

/-- The named filler. Same shape as `KimchiWrapMain.wrapFixture`, defined here because §2's schedule
needs `x_hat` and `x_hat` needs the scalars. -/
def wrapFixtureQ (tag i : Nat) : Nat := (11 + 1000003 * (17 * tag + i)) % qN

/-! ### §15c′ — ⚑ **THE PACKED PREVIOUS STEP STATEMENT** (W-PREV, `wrap_main.ml:201-256`).

`Types.Step.Statement.spec 2 15` (`composition_types.ml:1453-1459`) is
`Struct [Vector (per_proof, 2); B Digest; Vector (B Digest, 2)]` and `per_proof`
(`:1268-1276`) is 27 words: 5 `B Field`, 1 `B Digest`, 2 `B Challenge`, 3 `Scalar Challenge`,
15 `B Bulletproof_challenge` (`bp_log2 = Backend.Tock.Rounds.n = 15`, HARDCODED at `:1358`), 1
`B Bool`. So the statement is `2·27 + 1 + 2 = 57` words, and `wrap_verifier.ml:542-548` expands the
ten `` `Field `` ones into pairs to reach §15a's 67 entries.

⚠ ⚑ **AND `~assert_16_bits` IS PASSED AND NEVER FIRES.** `wrap_main.ml:208` hands
`Types.Step.Proof_state.typ` an `~assert_16_bits:(Wrap_verifier.assert_n_bits ~n:16)`, and
`spec.ml:414-429` consumes that argument in exactly ONE arm — `Branch_data` — which the STEP
per-proof spec does not contain (`Branch_data` is the WRAP statement's, `wrap_main.ml:189-199`).
Every other basic is check-free at source: `Field` is `Shifted_value.Type2.typ Field.typ`,
`Digest.typ` is a `Typ.transport Field.typ` (`digest.ml:79-83`), and — the one worth naming —
**`Limb_vector.Challenge.typ` is `Typ.field` with a transport and NO range check at all**
(`limb_vector/make.ml:14-19`), which `Scalar_challenge.typ` and `Bulletproof_challenge.typ`
(`bulletproof_challenge.ml:18-22`) inherit. So W-PREV's `exists` costs, in the whole 57-word
statement, **two `Boolean.typ` checks** and nothing else. §13 item 9 said this typ carried "a
`to_field_checked` at a width this file does not emit"; it does not, and that is corrected here. -/

/-- `Per_proof.In_circuit.spec`'s word count: 5 + 1 + 2 + 3 + 15 + 1. -/
def PREV_PER_PROOF_WORDS : Nat := 27
/-- **57** — `Statement.spec 2 15`'s packed words, before `:542-548`'s expansion. -/
def PREV_WORDS : Nat := PREV_PER_PROOF_WORDS * XHAT_PREVS + 1 + XHAT_PREVS
/-- Word 54 — `messages_for_next_step_proof`, the one `wrap_main.ml:350-351` ties to the wrap
statement. -/
def PREV_MSG_NEXT_STEP : Nat := PREV_PER_PROOF_WORDS * XHAT_PREVS
/-- Word 26 of a block — `should_finalize`, the one `B Bool` and the only word whose `typ` emits a
constraint. -/
def PREV_SHOULD_FINALIZE : Nat := PREV_PER_PROOF_WORDS - 1

/-- ⚑ Entry `i` is the VALUE half of a `split_field` pair — the five `B Field` words of each
`per_proof` block, whose successor entry carries the parity. The `j = 10` digest and the three
trailing `B Digest`s are `WQ_FIELD` too and are NOT splits: they arrive as `` `Packed_bits ``, never
through `wrap_main.ml:409`. -/
def xhatIsSplitHi (i : Nat) : Bool :=
  i < XHAT_PER_PROOF * XHAT_PREVS && i % XHAT_PER_PROOF < 10 && i % XHAT_PER_PROOF % 2 == 0
/-- …and `i` is the PARITY half — `split_field`'s `is_odd`, at the odd position. -/
def xhatIsSplitLo (i : Nat) : Bool :=
  i < XHAT_PER_PROOF * XHAT_PREVS && i % XHAT_PER_PROOF < 10 && i % XHAT_PER_PROOF % 2 == 1

/-- ⚑ **WHICH PACKED WORD ENTRY `i` CAME OUT OF.** The inverse of `wrap_verifier.ml:542-548`: a
`` `Packed_bits `` word gives one entry, a `` `Field `` word gives two, so the map is many-to-one on
exactly the split pairs and injective everywhere else. -/
def xhatWordOf (i : Nat) : Nat :=
  if i ≥ XHAT_PER_PROOF * XHAT_PREVS then
    PREV_PER_PROOF_WORDS * XHAT_PREVS + (i - XHAT_PER_PROOF * XHAT_PREVS)
  else
    let b := i / XHAT_PER_PROOF
    let j := i % XHAT_PER_PROOF
    PREV_PER_PROOF_WORDS * b + (if j < 10 then j / 2 else j - 5)

/-- Word `w`'s width under `pack_basic` (`spec.ml:374-392`). ⚑ `WQ_FIELD` on a `B Field` word is
`Field.size_in_bits` and is not a bound: `qN < 2^255`, so reducing an Fq element mod `2^255` is the
identity. It is a bound on the twenty challenge words and on the `B Bool`. -/
def prevWordWidth (w : Nat) : Nat :=
  if w ≥ PREV_PER_PROOF_WORDS * XHAT_PREVS then WQ_FIELD
  else
    let j := w % PREV_PER_PROOF_WORDS
    if j < 6 then WQ_FIELD else if j < PREV_SHOULD_FINALIZE then WQ_CHAL else WQ_BOOL

/-- ⚑ Word `w`'s WITNESSED VALUE — a named fixture, exactly as `exists ~request:Req.Proof_state` is a
free witness upstream.

⚑ **THE NINTH POWER IS NOT DECORATION, AND THE OLD `/ 7` WAS THE SAME LESSON, MEASURED AGAIN.**
`wrapFixtureQ 34 w = 11 + 1000003·(578 + w)` never wraps `qN`, so it is a ~29-bit integer whose
parity is `w mod 2` — and every one-bit entry sits at an odd `i`, so the raw mixer gives all twelve
`Cond_add` entries the same bit, the mux's `~else_` branch has no honest witness at all, and half of
what `w6_xhat` exercises is quietly dead. A `/ 7` was the previous patch for the previous shape of
this bug. `a^9` is the smallest odd power of a 29-bit value that WRAPS `qN` (`9 × 29 > 255`), so it
is four `qMul`s — cheap enough for the kernel, where a `qInv` here cost 57 × 260 recursion levels and
blew `maxRecDepth` outright — and a 254-bit `B Digest` is what a digest actually looks like.
⚠ Reduction to `prevWordWidth` happens AFTER, so the twenty challenge words are 128-bit and the two
`B Bool`s are bits. `xhat_cond_add_takes_both_branches` and `xhat_smoke_selection_covers_every_path`
are the pins that keep it fixed; both go red under the raw mixer. -/
def prevWordVal (w : Nat) : Nat :=
  let a := wrapFixtureQ 34 w
  let a2 := qMul a a
  let a4 := qMul a2 a2
  qMul (qMul a4 a4) a % 2 ^ prevWordWidth w

/-- ⚑ **ENTRY `i`'s SCALAR — the packed image of a statement word, not a draw of its own.**
`split_field` (`wrap_main.ml:69-81`) is `y = (x − is_odd)/2`, `is_odd = x mod 2`; every other entry
IS its word. -/
def xhatScalar (i : Nat) : Nat :=
  let v := prevWordVal (xhatWordOf i)
  if xhatIsSplitHi i then v / 2 else if xhatIsSplitLo i then v % 2 else v

/-- `scale_fast2'`'s `s_div_2` (`plonk_curve_ops.ml:271-283`). -/
def xhatSDiv2 (i : Nat) : Nat := xhatScalar i / 2
/-- …and its `s_odd`. -/
def xhatSOdd (i : Nat) : Nat := xhatScalar i % 2

/-- The `actual_bits_used` bits of `s_div_2`, MSB-first — what `scale_fast_unpack` unpacks
(`plonk_curve_ops.ml:151-156`).

⚠ ⚑ **`v` IS HOISTED, AND THAT IS THE MODULE'S OWN PERF LESSON APPLIED AGAIN.** `xhatSDiv2 i` inside
the `map`'s lambda is re-evaluated once per BIT — 255 times per 255-bit entry, 130 per 128-bit one,
14 550 times over the wrap shape's 55 ladders. That was free while the scalar was `wrapFixtureQ 21 i
/ 7`; at `w9_prev` the scalar is four `qMul`s deep, and Lean does not sink a `let` into a lambda. -/
def xhatBitsOf (i : Nat) : List Nat :=
  let n := xhatActualBits i
  let v := xhatSDiv2 i
  (List.range n).map (fun k => v / 2 ^ (n - 1 - k) % 2)

/-! ## §15d — the MSM as a VALUE.

`wrap_verifier.ml:578-609`, in upstream's own order: reduce the corrections, fold the constant part
into the init (EMPTY here — see below), then `List.foldi terms ~init` over every entry, then
`Inner_curve.negate` (`:610`) and `x_hat blinding` (`:612-616`).

⚑ **THE CONSTANT PARTITION IS EMPTY ON THE WRAP SIDE, AND THAT IS NOT AN ASSUMPTION.**
`wrap_verifier.ml:550-565` partitions on `` `Field (Constant c, _) ``. The STEP statement's spec
(`composition_types.ml:1268-1276,1453-1459`) is six `Vector`s of plain basics — no `Spec.T.Constant`
node and no `Opt`, so `Spec.pack`'s `~zero`/`~one` arms (`spec.ml:399-400`) are never taken and every
word arrives as a `Cvar.Var` out of `exists ~request:Req.Proof_state`. That is the MIRROR of the step
side, where the WRAP statement's `feature_flags` ARE `Spec.T.Constant` and nine one-bit words leave
the circuit. Here **all 67 entries are in-circuit** and the twelve one-bit ones take `` `Cond_add ``
rather than dropping out. -/

/-- One entry's ladder, seeded exactly as upstream: `acc₀ = Ops.add_fast base base`
(`plonk_curve_ops.ml:157`), `n₀ = 0` (`:158`). -/
def xhatLadder (i : Nat) : TermDataQ :=
  let T := xhatBase i
  runVbmQ T (addAQ T T) (xhatBitsOf i)

/-- `scale_fast2 g (s_div_2, s_odd) ~num_bits` (`plonk_curve_ops.ml:258-268`):
`h = scale_fast_unpack …`, then `G.if_ s_odd ~then_:h ~else_:(add_fast h (G.negate g))`. -/
def xhatScaled (i : Nat) : Nat × Nat :=
  let h := (xhatLadder i).accs.getLastD (0, 0)
  if xhatSOdd i == 1 then h else addAQ h (negAQ (xhatBase i))

/-- The correction reduce (`wrap_verifier.ml:588-596`) — `List.reduce_exn … ~f:Ops.add_fast` over the
`Add_with_correction` partition, left-associated. `init` is exactly this, because the constant
partition is empty. -/
def xhatInit (sel : List Nat) : Nat × Nat :=
  let cs := (sel.filter (fun i => xhatChunksAt i != 0)).map xhatCorr
  match cs with
  | [] => (0, 0)
  | c :: rest => rest.foldl addAQ c

/-- ⚑ **THE WHOLE FOLD, AS A PREFIX LIST** (`wrap_verifier.ml:598-609`) — entry `k`'s incoming
accumulator is index `k` and its outgoing one is `k + 1`, so `xhatFolds sel` has `sel.length + 1`
elements. `` `Cond_add `` is `Inner_curve.if_ b ~then_:(add_fast g acc) ~else_:acc`;
`` `Add_with_correction `` is `Ops.add_fast acc (scale_fast2' … )`, in that argument order.

⚠ ⚑ **THIS REPLACES A QUADRATIC `xhatFoldAt sel k`, AND THE COST WAS NOT THEORETICAL.** The old
form re-ran `(sel.take k).foldl` from `~init` for EVERY `k`, and each `Add_with_correction` step in
that fold calls `xhatScaled`, which runs a whole `scale_fast2` ladder — 255 `stepVbmQ`s at three
`qInv` apiece. `xhatRows` and `xhatEnv` each index it once per entry, wired and unwired, so the
emitter ran Θ(n²) ladders: **2 278 at the committed 67-entry shape where 67 are needed**, under
`lean --run`'s interpreter. Same emitted values, same order — `foldl` over the whole list produces
exactly the prefixes the per-`k` folds did. -/
def xhatFolds (sel : List Nat) : List (Nat × Nat) :=
  sel.foldl
    (fun acc i =>
      let cur := acc.getLastD (0, 0)
      acc ++ [ if xhatChunksAt i == 0 then
                 (if xhatScalar i == 1 then addAQ (xhatBase i) cur else cur)
               else addAQ cur (xhatScaled i) ])
    [xhatInit sel]

/-- Entry `k`'s incoming accumulator. ⚠ Callers that need MORE THAN ONE `k` must bind `xhatFolds sel`
themselves and index it — this convenience form rebuilds the whole fold per call, which is the
quadratic shape it exists to make visible rather than to reintroduce. -/
def xhatFoldAt (sel : List Nat) (k : Nat) : Nat × Nat := (xhatFolds sel).getD k (0, 0)

/-- `x_hat` before blinding — `|> Inner_curve.negate` (`wrap_verifier.ml:610`). -/
def xhatNegated (sel : List Nat) : Nat × Nat := negAQ ((xhatFolds sel).getLastD (0, 0))

/-- ⚑ **`x_hat`** — `Ops.add_fast x_hat (Inner_curve.constant Generators.h)`
(`wrap_verifier.ml:612-616`). This is the pair `wrap_verifier.ml:617` absorbs. -/
def xhatOut (n : Nat) : Nat × Nat := addAQ (xhatNegated (xhatSel n)) XHAT_H

end Dregg2.Circuit.Emit.KimchiWrapMain

/-! ⚑ **THE FACTS LIVE IN THEIR OWN NAMESPACE, AND THAT IS NOT COSMETIC.**

The DEFINITIONS above are `Dregg2.Circuit.Emit.KimchiWrapMain`'s, because `KimchiWrapMain` uses them
unqualified and a rename would be churn for nothing. The THEOREMS are not: `#assert_namespace_axioms`
walks every theorem under a namespace, and with the facts filed under `…KimchiWrapMain` the pin at
the foot of `KimchiWrapMain.lean` swept this file's as well — measured, that took the wrap file from
185 s (green, every declaration checked) to unfinished at 9.6 GB. Each file now pins what it proves. -/
namespace Dregg2.Circuit.Emit.KimchiWrapMainField

open Dregg2.Circuit.Emit.KimchiWrapMain

/-! ## §15e — the pins, as NAMED THEOREMS.

Every one is closed by `decide`/`rfl` in the kernel and accounted for by `#assert_namespace_axioms`
at the foot of the file. -/

/-- ⚑ **THE CENSUS, against a source this file does not own.** `MinaStepSrsLagrange.WIDTHS` was
printed by `xhat_lagrange_export.rs`, which walks the real SRS and computes the widths from its own
transcription of `spec.ml`. Two independent transcriptions of the same OCaml. -/
theorem xhat_widths_agree_with_the_extractor :
    (List.range XHAT_TERMS_FULL).map xhatBits = Dregg2.Circuit.Emit.MinaStepSrsLagrange.WIDTHS := by
  decide

/-- …and the census itself: 15 × 255, 40 × 128, 12 × 1, and 67 entries in all. -/
theorem xhat_width_census :
    (((List.range XHAT_TERMS_FULL).map xhatBits).filter (· == 255)).length = 15
  ∧ (((List.range XHAT_TERMS_FULL).map xhatBits).filter (· == 128)).length = 40
  ∧ (((List.range XHAT_TERMS_FULL).map xhatBits).filter (· == 1)).length = 12
  ∧ XHAT_TERMS_FULL = 67 := by decide

/-- The chunk widths: 51 for a 255-bit entry, 26 for a 128-bit one, 0 for a one-bit one. -/
theorem xhat_chunk_widths :
    xhatChunksAt 0 = 51 ∧ xhatChunksAt 1 = 0 ∧ xhatChunksAt 11 = 26 ∧ xhatChunksAt 31 = 0
  ∧ xhatChunkPrefix XHAT_TERMS_FULL = 1805 := by decide

/-- ⚑ **MINA'S OWN COMPILED WRAP CIRCUIT CLOSES THIS CENSUS.**
`mina-canonical-circuit-oracle.mjs --circuit wrap-transaction` reports `VarBaseMul 2417`, and the
three sub-circuits that emit `VarBaseMul` account for it exactly. A wrong per-entry width, a wrong
entry count, or `bp_log2` read as `Tick`'s 16 instead of `Tock`'s 15 all miss it. -/
theorem xhat_chunk_census_closes_minas_var_base_mul_count :
    xhatChunkPrefix XHAT_TERMS_FULL
      + 8 * chunksNeededQ 255      -- W-FTCOMM: `common.ml:246-256`, 1 + 6 + 1 `scale_fast`
      + 4 * chunksNeededQ 255      -- W-BULLET: `wrap_verifier.ml:411,428,430,433`
      = 2417 := by decide

/-- ⚑ …and it is a MEASUREMENT, not an identity: reading `bp_log2` as `Tick.Rounds.n = 16` — the
step side's value, and the exact mistake §1b of `KimchiStepMainCore` had to correct in the other
direction — gives a different entry count and misses 2417. -/
theorem xhat_census_is_falsified_by_the_step_side_rounds :
    (XHAT_PER_PROOF + 1) * XHAT_PREVS + 1 + XHAT_PREVS ≠ XHAT_TERMS_FULL := by decide

/-- Both `lowest_128_bits`-style halves have somewhere to be asserted: a 255-bit entry's ladder runs
at 255 actual bits and asserts ONE top bit zero, a 128-bit entry's runs at **130** and asserts
THREE. A model that ran the 128-bit ladder at 128 bits would assert none. -/
theorem xhat_top_zero_counts :
    xhatActualBits 0 = 255 ∧ xhatTopZeros 0 = 1
  ∧ xhatActualBits 11 = 130 ∧ xhatTopZeros 11 = 3
  ∧ xhatTopZeros 1 = 0 := by decide

/-- The correction index is a bijection onto the `Add_with_correction` partition, so
`xhatCorr` never reads two entries' corrections off one slot. -/
theorem xhat_correction_index_is_injective_on_the_partition :
    ((List.range XHAT_TERMS_FULL).filter (fun i => xhatChunksAt i != 0)).map xhatCorrIdx
      = List.range 55 := by decide

/-- ⚑ Every base is a REAL point of the **Vesta** curve `y² = x³ + 5` over **Fq**. A base transcribed
into the wrong field, or a Pallas point mistaken for a Vesta one, fails here. -/
theorem xhat_bases_are_on_vesta :
    ((List.range XHAT_TERMS_FULL).map xhatBase).all onCurveQ = true := by decide

/-- …so is every correction, and so is `Generators.h`. -/
theorem xhat_corrections_and_h_are_on_vesta :
    (((List.range XHAT_TERMS_FULL).filter (fun i => xhatChunksAt i != 0)).map xhatCorr).all
      onCurveQ = true
  ∧ onCurveQ XHAT_H = true := by decide

/-- ⚑ **THE CORRECTION IS THE ONE `scale_fast2` NEEDS.** `scale_fast2 g s ~num_bits` returns
`[s + 2^actual_bits_used]·g` (`plonk_curve_ops.ml:236-268`, and its own `%test_unit`), so the MSM is
right only if the correction is `−[2^actual_bits_used]·g`. `lagrange_with_correction` computes
`−[2^(5·chunks_needed input_length)]·g` — at `input_length` and not `input_length − 1`, which
upstream flags with its own TODO (`wrap_verifier.ml:249-252`). This says the two agree at BOTH live
widths, so the `+2^N` cancels; it is the check that TODO deserves. -/
theorem xhat_correction_shift_matches_the_ladder :
    BITS_PER_CHUNK * chunksNeededQ 255 = xhatActualBits 0
  ∧ BITS_PER_CHUNK * chunksNeededQ 128 = xhatActualBits 11 := by decide

/-- …and it is not vacuous: at a width where the TODO would bite — any multiple of 5 — the two
expressions DIFFER by a whole chunk, so the equality above is about these widths and not about the
shape of the formula. -/
theorem xhat_correction_shift_would_differ_at_a_chunk_boundary :
    BITS_PER_CHUNK * chunksNeededQ 126 ≠ BITS_PER_CHUNK * chunksNeededQ (126 - 1) := by decide

/-- The scalars respect their own widths — `scale_fast2`'s top-bit asserts have to be satisfiable by
the honest witness or every rung would refuse. -/
theorem xhat_scalars_fit_their_widths :
    (List.range XHAT_TERMS_FULL).all (fun i => decide (xhatScalar i < 2 ^ xhatBits i)) = true := by
  decide

/-- ⚑ …and BOTH `Cond_add` branches are taken by the honest witness: some one-bit entry carries a
0 and some carries a 1, so `Inner_curve.if_`'s `~else_` arm is a live path and not dead weight. -/
theorem xhat_cond_add_takes_both_branches :
    (((List.range XHAT_TERMS_FULL).filter (fun i => xhatChunksAt i == 0)).map xhatScalar).any
      (· == 0) = true
  ∧ (((List.range XHAT_TERMS_FULL).filter (fun i => xhatChunksAt i == 0)).map xhatScalar).any
      (· == 1) = true := by decide

/-- ⚑ The smoke selection reaches all three widths and both partitions, so the pins that run on it
are not exercising one code path five times — AND it reaches entry 64, the packed word `w9_prev`
exposes as a public one. -/
theorem xhat_smoke_selection_covers_every_path :
    ((xhatSel 5).map xhatBits) = [255, 1, 128, 255, 1]
  ∧ ((xhatSel 5).filter (fun i => xhatChunksAt i == 0)).length = 2
  ∧ (((xhatSel 5).filter (fun i => xhatChunksAt i == 0)).map xhatScalar) = [1, 0]
  ∧ (xhatSel 5).contains (XHAT_PER_PROOF * XHAT_PREVS) = true := by decide

/-- …and at the committed count the selection is the identity, i.e. the wrap shape emits
`wrap_verifier.ml:539-609`'s own entry list in its own order. -/
theorem xhat_full_selection_is_every_entry :
    xhatSel XHAT_TERMS_FULL = List.range XHAT_TERMS_FULL := by decide

/-! ### §15c″ — ⚑ **W-PREV'S PINS ON THE VALUE LAYER** (`wrap_main.ml:201-256`). -/

/-- The statement's own word count, from its own spec: `2 × 27 + 1 + 2`. ⚑ And it is `bp_log2`
that decides it — at `Tick`'s 16 instead of `Tock`'s 15 the per-proof block is 28 words and the
statement is 59, which the entry census would have missed by two `Bulletproof_challenge`s. -/
theorem prev_statement_is_fifty_seven_words :
    PREV_WORDS = 57 ∧ PREV_PER_PROOF_WORDS = 5 + 1 + 2 + 3 + 15 + 1
  ∧ PREV_PER_PROOF_WORDS * XHAT_PREVS + 1 + XHAT_PREVS ≠ (PREV_PER_PROOF_WORDS + 1) * XHAT_PREVS + 1 + XHAT_PREVS := by
  decide

/-- ⚑ **`xhatWordOf` IS `wrap_verifier.ml:542-548`'s EXPANSION, INVERTED.** It hits every one of the
57 words, it is two-to-one exactly on the ten `split_field` pairs and injective on the other 47
entries, and each pair's two entries share ONE word — which is the whole content of the tie. -/
theorem prev_word_map_is_the_packed_expansion :
    (List.range PREV_WORDS).all (fun w =>
      ((List.range XHAT_TERMS_FULL).filter (fun i => xhatWordOf i == w)).length
        == (if w < PREV_PER_PROOF_WORDS * XHAT_PREVS && w % PREV_PER_PROOF_WORDS < 5 then 2 else 1))
      = true
  ∧ ((List.range XHAT_TERMS_FULL).map xhatWordOf).all (fun w => decide (w < PREV_WORDS)) = true
  ∧ ((List.range XHAT_TERMS_FULL).filter xhatIsSplitHi).length = 10
  ∧ ((List.range XHAT_TERMS_FULL).filter xhatIsSplitLo).length = 10
  ∧ ((List.range XHAT_TERMS_FULL).filter xhatIsSplitHi).all (fun i => xhatWordOf i == xhatWordOf (i + 1))
      = true := by
  decide

/-- ⚑ **THE PACKED WIDTH AND THE ENTRY WIDTH ARE THE SAME NUMBER** on every entry that is not a
`split_field` half, and on a split pair they are `(Field.size_in_bits, 1)` against a `B Field` word.
A word/entry map off by one anywhere makes a 128-bit challenge into a 255-bit entry, which
`scale_fast2` would range-check at the wrong width and still accept. -/
theorem prev_word_widths_are_the_entry_widths :
    (List.range XHAT_TERMS_FULL).all (fun i =>
      if xhatIsSplitHi i then decide (xhatBits i = WQ_FIELD && prevWordWidth (xhatWordOf i) == WQ_FIELD)
      else if xhatIsSplitLo i then decide (xhatBits i = WQ_BOOL && prevWordWidth (xhatWordOf i) == WQ_FIELD)
      else decide (xhatBits i = prevWordWidth (xhatWordOf i))) = true := by
  decide

/-- ⚑ **`split_field`'s RECOMPOSITION IS AN IDENTITY ON THE WITNESS.** `wrap_main.ml:80` asserts
`2·y + is_odd = x`; before `w9_prev` this file DEFINED `x` as `2·y + is_odd` from two independent
draws, so the assert could not fail and `w7_split` pinned nothing. Now `x` is the statement word and
the two halves are its image, so the equation is a fact about the packed statement — over ℕ, not
merely mod `qN`, because `prevWordVal < qN < 2^255`. -/
theorem split_field_recomposes_the_statement_word :
    ((List.range XHAT_TERMS_FULL).filter xhatIsSplitHi).all (fun i =>
      decide (2 * xhatScalar i + xhatScalar (i + 1) = prevWordVal (xhatWordOf i))) = true := by
  decide

/-- …and the halves are `split_field`'s own, not some other decomposition: the parity is the low bit
and the value is the floor-half. -/
theorem split_field_halves_are_the_gadgets_own :
    ((List.range XHAT_TERMS_FULL).filter xhatIsSplitLo).all (fun i =>
      decide (xhatScalar i = prevWordVal (xhatWordOf i) % 2)) = true
  ∧ ((List.range XHAT_TERMS_FULL).filter xhatIsSplitHi).all (fun i =>
      decide (xhatScalar i = prevWordVal (xhatWordOf i) / 2)) = true := by
  decide

/-- ⚑ **THE SCALARS MOVED.** The red control for `w9_prev`, kept for the same reason
`xhat_derived_is_not_the_old_fixture` keeps `RC_XHAT`: the value the MSM used to consume, exhibited
rather than merely asserted to be gone. `wrapFixtureQ 21 i / 7 % 2 ^ xhatBits i` was §15c's filler.

⚠ **THE HONEST COUNT IS 63 OF 67, NOT 67 OF 67**, and the residue is not a hole: a one-bit entry has
two possible values, so four of the twelve `Cond_add` scalars coincide with the old filler by
arithmetic and not by inheritance. Every entry the MSM runs a LADDER over — all **55** — moved.
Quoting 67 here would be the flattering number of a pair. -/
theorem xhat_scalars_are_not_the_old_per_entry_fixture :
    ((List.range XHAT_TERMS_FULL).filter (fun i =>
      xhatScalar i != wrapFixtureQ 21 i / 7 % 2 ^ xhatBits i)).length = 63
  ∧ ((List.range XHAT_TERMS_FULL).filter (fun i =>
      xhatChunksAt i != 0 && xhatScalar i == wrapFixtureQ 21 i / 7 % 2 ^ xhatBits i)).length = 0 := by
  decide

/-- ⚑ …and each `should_finalize` is a REAL bit of the statement, which is what makes `Boolean.typ`'s
check (`spec.ml:419-420`) satisfiable and non-trivial: there are exactly two such words in the
57-word statement, they are the ONLY words whose `typ` emits a constraint at all, and they carry
DIFFERENT bits — so the check is exercised on both a 0 and a 1. -/
theorem prev_should_finalize_words_are_bits :
    prevWordVal PREV_SHOULD_FINALIZE < 2
  ∧ prevWordVal (PREV_PER_PROOF_WORDS + PREV_SHOULD_FINALIZE) < 2
  ∧ prevWordVal PREV_SHOULD_FINALIZE ≠ prevWordVal (PREV_PER_PROOF_WORDS + PREV_SHOULD_FINALIZE)
  ∧ ((List.range PREV_WORDS).filter (fun w => prevWordWidth w == WQ_BOOL)).length = XHAT_PREVS := by
  decide

#assert_namespace_axioms Dregg2.Circuit.Emit.KimchiWrapMainField

end Dregg2.Circuit.Emit.KimchiWrapMainField
