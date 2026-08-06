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
import Dregg2.Circuit.Emit.PastaPoseidonFq
import Dregg2.Circuit.Emit.PastaCurve
-- ⚑ THE STEP PROOF'S OWN IPA OPENING. `KimchiStepWrapChainFixture` imports only `PastaField`, so
-- this adds no cycle; it is what makes `lrPointQ`/`deltaPointQ` read a real `openings_proof`
-- instead of cycling SRS Lagrange bases.
import Dregg2.Circuit.Emit.KimchiStepWrapChainFixture

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

/-! ### §15a′ — ⚑⚑ **THERE IS ONE ENTRY SPACE SINCE 2026-08-06, AND IT IS MINA'S SIXTY-SEVEN.**

`wrap_verifier.ml:539-548`'s expansion of a Pickles `Types.Step.Statement` produces the 67 entries
`0 … XHAT_TERMS_FULL − 1` above, and **dregg's own step rule now publishes exactly that object**.
`KimchiStepWrapChainFixture.STEP_PUBLIC = 67`, `STEP_XHAT_BITS` is the exporter's own reading of the
57 words' expansion (15 at 255, 40 at 128, 12 at 1), and `STEP_PUBLIC_IN` is the packed statement the
prover handed `kimchi::verifier`. So this file's table and dregg's step proof's public input are one
list, and the `xhat*` accessors read it directly.

⚠ ⚑ **`XHAT_OWN_BASE` / `XHAT_OWN_TERMS` / `XHAT_OWN_SEL` / `xhatIsOwn` / `xhatOwnIdx` ARE DELETED,
AND KEEPING THEM WOULD HAVE BEEN THE DEFECT.** They existed because the step rule proved a
twelve-word unconstrained public input — no `per_proof` blocks, no `split_field` pairs, no
`should_finalize` — so a 67-entry table was not a description of it and a DISJOINT index space was
the honest way to carry both. With a real statement there is nothing to carry twice: dregg's entries
**are** Mina's 67, and two index spaces that agree are two index spaces that will disagree later.

⚠ ⚑ **AND THE BASES FOLLOWED THE DOMAIN, BECAUSE A LAGRANGE BASIS IS A FUNCTION OF THE DOMAIN.**
`MinaStepSrsLagrange.LAGRANGE_XY` is taken at `2 ^ STEP_LOG2 = 65536`, Mina's `step-transaction`
domain; this proof's is `2 ^ STEP_DOMAIN_LOG2`. Bases from the wrong domain are on-curve, are genuine
SRS Lagrange commitments **of the same SRS**, and reproduce nothing — the same shape as
`lrPointQ i = xhatBase (5 + i % 50)`, which `onCurveQ` was structurally incapable of noticing.
`the_xhat_msm_is_this_proofs_public_input_commitment` is the re-derivation that catches it and
`xhat_bases_are_not_minas_step_transaction_domains` is the inequality that catches a copy-paste. -/

/-- ⚑ Entry `i`'s packed bit width — `wrap_verifier.ml:542-548`'s expansion of
`Types.Step.Statement.spec 2 15`. `xhat_entry_widths_are_the_exporters` pins the whole table against
`STEP_XHAT_BITS`, which the Rust exporter computed off the same statement by its own route. -/
def xhatBits (i : Nat) : Nat :=
  if i ≥ XHAT_PER_PROOF * XHAT_PREVS then WQ_FIELD        -- the three trailing `B Digest`s
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

/-- Entry `i`'s base — `lagrange ~domain srs i` / `lagrange_with_correction`'s first component, at
**this step proof's own domain**.

⚠ ⚑ **THE `~domain` ARGUMENT IS THE TRAP, AND IT IS INVISIBLE TO EVERY CURVE CHECK.**
`MinaStepSrsLagrange.LAGRANGE_XY` is the same `SRS::<Vesta>::create(65536)`'s Lagrange basis taken at
`2 ^ MinaStepSrsLagrange.STEP_LOG2 = 65536`, Mina's `step-transaction` domain; this proof's is
`2 ^ STEP_DOMAIN_LOG2`. Reading one for the other is on-curve, is a genuine SRS Lagrange commitment,
and reproduces nothing. Until 2026-08-06 this function had a second arm reading Mina's table, and
that arm is gone with `xhatIsOwn`: there is one domain here because there is one step proof. -/
def xhatBase (i : Nat) : Nat × Nat :=
  (Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_LAGRANGE_XY.getD (2 * i) 0,
   Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_LAGRANGE_XY.getD (2 * i + 1) 0)

/-- Where entry `i`'s correction sits in `CORRECTION_XY`, which is indexed over the
`Add_with_correction` partition only. -/
def xhatCorrIdx (i : Nat) : Nat :=
  ((List.range i).filter (fun k => xhatChunksAt k != 0)).length

/-- Entry `i`'s correction — `negate (pow2pow g actual_shift)`, `wrap_verifier.ml:255-256`.

⚠ ⚑ **INDEXED BY `xhatCorrIdx`, NOT BY `i`, AND THE FIXTURE IS BUILT THAT WAY.**
`STEP_XHAT_CORRECTION_XY` runs over the `Add_with_correction` PARTITION only — **55** entries, not
67 — because the twelve one-bit slots take `` `Cond_add `` (`:573-577`), run no ladder and have no
correction. Reading it at `i` would slide every correction past slot 1 by the number of one-bit
entries below it, which is on-curve and cancels nothing. -/
def xhatCorr (i : Nat) : Nat × Nat :=
  (Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_XHAT_CORRECTION_XY.getD
      (2 * xhatCorrIdx i) 0,
   Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_XHAT_CORRECTION_XY.getD
      (2 * xhatCorrIdx i + 1) 0)

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

/-- ⚑ **`xhatWordOf` INVERTED — word `w`'s FIRST entry.** On a `` `Field `` word that is the value
half and `w`'s parity half is the next index; on every other word it is the word's only entry.
Written in closed form rather than as a search over `xhatWordOf`'s fibre: the search is 67 tests per
call and `prevWordVal` is read once per statement word per emitted row.
`prev_entry_map_inverts_the_expansion` is the round trip. -/
def xhatEntryOf (w : Nat) : Nat :=
  if w ≥ PREV_PER_PROOF_WORDS * XHAT_PREVS then
    XHAT_PER_PROOF * XHAT_PREVS + (w - PREV_PER_PROOF_WORDS * XHAT_PREVS)
  else
    let b := w / PREV_PER_PROOF_WORDS
    let k := w % PREV_PER_PROOF_WORDS
    XHAT_PER_PROOF * b + (if k < 5 then 2 * k else k + 5)

/-- Word `w`'s width under `pack_basic` (`spec.ml:374-392`). ⚑ `WQ_FIELD` on a `B Field` word is
`Field.size_in_bits` and is not a bound: `qN < 2^255`, so reducing an Fq element mod `2^255` is the
identity. It is a bound on the twenty challenge words and on the `B Bool`. -/
def prevWordWidth (w : Nat) : Nat :=
  if w ≥ PREV_PER_PROOF_WORDS * XHAT_PREVS then WQ_FIELD
  else
    let j := w % PREV_PER_PROOF_WORDS
    if j < 6 then WQ_FIELD else if j < PREV_SHOULD_FINALIZE then WQ_CHAL else WQ_BOOL

/-! ### §15c″ — ⚑ **W-WRAPHACK's VALUE LAYER** (`wrap_hack.ml:99-141`, `wrap_main.ml:340-355,421-431`).

It is declared HERE, above `prevWordVal`, because two of the 57 packed statement words are NOT
witnessed: `wrap_main.ml:340-348` COMPUTES them.

    let prev_messages_for_next_wrap_proof =
      Vector.map2 prev_step_accs old_bp_chals ~f:(fun sacc (T (mlmb, chals)) →
        Wrap_hack.Checked.hash_messages_for_next_wrap_proof mlmb
          { challenge_polynomial_commitment = sacc; old_bulletproof_challenges = chals })

and `prev_statement.messages_for_next_wrap_proof` is that vector, which `pack_statement` puts at
words `PREV_MSG_NEXT_STEP + 1` and `+ 2` — 55 and 56. So `prevWordVal` may not answer with a
fixture there, and the override below is what makes the SAME two words derived on the value side
that §21 derives on the row side.

⚑ **THE ABSORPTION ORDER IS THE OPPOSITE OF THE STEP SIDE'S.**
`Messages_for_next_wrap_proof.to_field_elements` (`composition_types.ml:411-418`) is

    Array.concat [ Vector.to_array old_bulletproof_challenges |> Array.concat_map ~f:Vector.to_array
                 ; Array.of_list (g1_to_field_elements challenge_polynomial_commitment) ]

— every old bulletproof challenge FIRST, flattened, and the commitment's `[x; y]` LAST. The step
side interleaves; this one does not.

⚑ **AND THE FRONT PAD IS A PRECOMPUTED SPONGE STATE, NOT AN IN-CIRCUIT ABSORB.** `pad_vector`
(`wrap_hack.ml:26-28`) is `Vector.extend_front_exn v Padded_length.n dummy` — the padding goes at
the FRONT, which is exactly why upstream can precompute it: `Checked
.hash_messages_for_next_wrap_proof` (`wrap_hack.ml:110-137`) does NOT pad `t` at all. It opens the
sponge at `dummy_messages_for_next_wrap_proof_sponge_states.(2 − max_proofs_verified)`, the state a
fresh sponge reaches after absorbing that many DUMMY challenge vectors, injected as
`Impls.Wrap.Field.constant`. -/

/-- `Backend.Tock.Rounds.n` — one `old_bulletproof_challenges` vector's length (`wrap_main.ml:230`,
`composition_types.ml:1358`). ⚠ **Tock's 15, not Tick's 16**; `ipaRounds` is the other one. -/
def WH_ROUNDS : Nat := 15

/-- `Wrap_hack.Padded_length = Nat.N2` (`wrap_hack.ml:24`) — the length every accumulator is padded
UP TO, at the front. -/
def WH_PADDED : Nat := 2

/-- ⚑ How many DUMMY challenge vectors the precomputed opening state stands for
(`wrap_hack.ml:124-130`): `2 − max_proofs_verified`. -/
def whPadVectors (mlmb : Nat) : Nat := WH_PADDED - mlmb

/-- ⚑ **`max_local_max_proofs_verified` AT THE COMMITTED SHAPE, AND IT IS A SHAPE CHOICE THAT IS
SAID RATHER THAN BANKED.** `Max_widths_by_slot.maxes` (`wrap_main.ml:130-133`) is a per-slot
constant of the compiled instance; this assembly fixes it at `WH_PADDED` for every slot, which is
also what `Max_proofs_verified.n = 2` gives the closing hash at `wrap_main.ml:423`. So
`whPadVectors WH_MLMB = 0` in all three sponges and the front pad is the FRESH state — the one this
file can pin to zero out of its own `Sponge.create` rows.

⚠ **THE OTHER CASE IS NOT EMITTED AND THE REASON IS NOT "LATER".** At `mlmb < 2` the opening state
is the sponge state after absorbing `Dummy.Ipa.Wrap.challenges_computed`, and those values are
`Ipa.Wrap.compute_challenge` of `Ro.scalar_chal ()` (`dummy.ml:30-35`) — an OCaml random-oracle draw
this tree has no independent source for. Emitting it would mean a FIXTURE constant standing in for a
derived sponge state, which is defect class 5 in a new place and inside the pad specifically. A
shape choice that avoids inventing a constant is the honest one; `whPadVectors` is here so the
general statement is in the file rather than the instance. -/
def WH_MLMB : Nat := 2

/-- The absorbed elements of ONE `hash_messages_for_next_wrap_proof`, in
`to_field_elements` order. -/
def whTape (chals : List Nat) (g : Nat × Nat) : List Nat := chals ++ [g.1, g.2]

/-- `Tock_field_sponge.digest` in circuit — `Sponge.squeeze_field` of an Fq sponge over the tape
(`wrap_hack.ml:131-137`). ⚑ `newSponge` IS the `whPadVectors WH_MLMB = 0` opening state. -/
def whDigestOf (chals : List Nat) (g : Nat × Nat) : Nat :=
  (Dregg2.Circuit.Emit.PastaPoseidonFq.squeeze1 Dregg2.Circuit.Emit.PastaPoseidonFq.fqParams
      (Dregg2.Circuit.Emit.PastaPoseidonFq.absorbMany Dregg2.Circuit.Emit.PastaPoseidonFq.fqParams
        Dregg2.Circuit.Emit.PastaPoseidonFq.newSponge (whTape chals g))).2

/-- `old_bp_chals.(p)` flattened — `Vector.typ (Vector.typ Field.typ Tock.Rounds.n)` with NO check
of any kind (`wrap_main.ml:226-256`), so a free witness upstream and a NAMED FIXTURE here. -/
def whOldChal (p k : Nat) : Nat := wrapFixtureQ 41 (WH_PADDED * WH_ROUNDS * p + k)
def whOldChals (p : Nat) : List Nat := (List.range (WH_MLMB * WH_ROUNDS)).map (whOldChal p)

/-- `prev_step_accs.(p)` — ⚑ the TRANSCRIPT's own `sg_old` coordinates, not a second copy of them.
This mirrors `KimchiWrapMain.itemVal T_SGOLD` exactly, including its fallback, so §21's tie row
joins two cells that already hold one value.

⚠ ⚑ **AND "MIRRORS" WAS ONE EDIT AWAY FROM FALSE, WHICH IS WHY IT NOW READS THE SAME LIST.** This
def used to name `PastaPoseidonFq.PREVCOMM_XY` and `itemVal T_SGOLD` used to name it too, so the
sentence above was true by coincidence of two literals. On 2026-08-05 `RC_SGOLD` moved to the step
proof this pipeline is actually about and this one did not — instantly making the emitted §21 rows
(which read the TRANSCRIPT cells, `absPtVal t.sp T_SGOLD p`) hash a different `sg_old` from the one
`prevWordVal` packs into statement words 55/56 and the x_hat MSM consumes.
`wraphack_digest_is_the_emitted_squeeze` is the pin that would have gone red for it. Two defs holding one object is the defect; both now
resolve through `KimchiStepWrapChainFixture.STEP_PREVCOMM_XY`. -/
def whSgOld (p : Nat) : Nat × Nat :=
  ((Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY).getD (2 * p)
      (wrapFixtureQ 1 (2 * p)),
   (Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY).getD (2 * p + 1)
      (wrapFixtureQ 1 (2 * p + 1)))

/-- ⚑ **PACKED STATEMENT WORD `55 + p`** — `prev_statement.messages_for_next_wrap_proof.(p)`. -/
def whPrevDigest (p : Nat) : Nat := whDigestOf (whOldChals p) (whSgOld p)

/-- `new_bulletproof_challenges` — `finalize_other_proof`'s output (`wrap_main.ml:258-338`), i.e.
**W-FINALIZE's**, which this file does not assemble (§13 item 7). Free here, and named as free. -/
def whNewChal (k : Nat) : Nat := wrapFixtureQ 42 k
def whNewChals : List Nat := (List.range (WH_MLMB * WH_ROUNDS)).map whNewChal

/-- `openings_proof.challenge_polynomial_commitment` — `exists (Openings.Bulletproof.typ …)` at
`wrap_main.ml:357-383`. ⚠ Its `Inner_curve.typ` `assert_on_curve` is **W-OPENINGS's** row, not §21's,
and this file does not assemble that sub-circuit.

⚑ **THE VALUE IS REAL SINCE 2026-08-05, AND IT IS THE SAME RECORD `lr` AND `delta` COME FROM.**
`wrap_main.ml:357-383` destructures ONE `Openings.Bulletproof.t` — `{lr; delta; z_1; z_2; sg}` — and
`challenge_polynomial_commitment` is that record's `sg`. Having wired `lr` and `delta` from the step
proof's opening and left this a `wrapFixtureQ`, the file would have been reading one upstream record
from two sources, which is the precise defect this whole change exists to close.

⚑ It is also the one field of that record Mina checks ARITHMETICALLY before it consults any key:
`pickles_kimchi_marshal` MEASURES `⟨b_poly_coefficients(u⃗), srs.g⟩ == opening.sg` over Mina's own
65,536 generators, and `accumulator_check.rs:10-64` is the verifier's side of that identity. So this
pair is not merely "from a real proof" — it is the accumulator the next proof's `sg_old` must be. -/
def whSg : Nat × Nat :=
  ( Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_SG_XY.getD 0 (wrapFixtureQ 43 0)
  , Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_SG_XY.getD 1 (wrapFixtureQ 43 1) )

/-- ⚑ **WRAP STATEMENT WORD 11** — `messages_for_next_wrap_proof_digest`, the value
`wrap_main.ml:421-431` `Field.Assert.equal`s. -/
def whCloseDigest : Nat := whDigestOf whNewChals whSg

/-! ### §15c‴ — ⚑ **W-FINSPONGE's VALUE LAYER**: three deferred words that are NOT witnessed either.

`finalize_other_proof` returns `Boolean.all [xi_correct; b_correct; combined_inner_product_correct;
plonk_checks_passed]` and `wrap_main.ml:335` asserts `Boolean.Assert.any [finalized; not
should_finalize]`. Once **all four** legs are emitted (`KimchiWrapMain` §20), the block whose
`should_finalize` word is 1 must carry the DERIVED `combined_inner_product`, `b` and `xi` — an
honest previous statement does, and a fixture there makes the rung unsatisfiable rather than strict.

⚑ **SO THESE THREE ARE A MEMO WITH A PROOF OBLIGATION, in the shape of `WrapShape.xhatXY` and for
the same reason.** The derivation that produces them is a 91-element Fq sponge plus a 1200-op
straight-line program, which lives two modules above this one. ⚠ They are NOT fixtures:
`KimchiWrapMain.fin_deferred_words_are_the_derivation` (`…Pins12`) closes them against
`finSpDerivedWords` — the very function `finSpRows` builds its witness from — and
`EmitWrapMainJson` REFUSES to emit a tree where they disagree. A value that cannot reach a proved
circuit while wrong is a memo; one that can is a fixture.

⚠⚑ **AND SINCE 2026-08-06 THEY NO LONGER REACH `xhatScalar`, WHICH IS THE POINT AND ALSO THE
FINDING.** `prevWordVal` used to answer with this triple at words 27, 28 and 37 — x_hat entries
32/33, 34/35 and 47 — so the statement the MSM consumed CONTAINED the derivation by construction.
The scalars are the step proof's own published `Types.Step.Statement` now, and that statement does
**not** carry these three values. `the_published_statement_does_not_carry_the_derived_words` states
which words and refuses the claim that it does.

⚠ **THE PRICE, SAID PLAINLY.** `w12_finsponge`'s `Field.equal` legs on the finalizing block have no
satisfying witness on `stepmain_step_r8_finalize`. ⚠ **AND THIS PARAGRAPH USED TO MISNAME WHY.** It
said the step proof had to be re-proved with a statement whose block-1 deferred words are the wrap's
own derivation, "and that is a FIXPOINT, because those words are x_hat entries and moving them moves
every challenge below them." Both halves are refuted below: it is a STRATIFICATION — no transcript
challenge reaches W-FINSPONGE — and those three words are the STEP circuit's own derived
`combined_inner_product`, `b` and `xi` (`bpDiv2`/`bpOdd`, `vXiStmt`), so they cannot be written at
all. What disagrees is two derivations of one quantity, and the wrap's runs on `finColVal` and its
neighbours — `wrapFixtureQ` where `prev_proof.openings.evals` belongs. Nothing at or below `w4_bind`
is affected: the three words are absorbed nowhere and are read only by W-FINSPONGE.

⚠ ⚑ **AND UNTIL 2026-08-05 THAT THEOREM DID NOT EXIST — this paragraph said it "closes them by
`rfl` IN THE KERNEL" and three other docblocks agreed with it.** `grep` over the tree found four
citations and no `theorem`; the only live discharge was the emitter's runtime refusal. It exists
now and it is **`native_decide` + `#assert_compiled`**, because the derivation is two sponges plus a
**1732**-op `Array FOp` program per instance and in `whnf` an `Array` is its `List` model — a ~200-op
program of the same shape does not reduce `.size` alone at 1,000,000 heartbeats
(`KimchiWrapFinalizeSpongeGate`). A kernel `rfl` was never available here; claiming one for four
docblocks is the same laundering as a `#guard`, spread over four files.

⚠ **ONLY ONE BLOCK EVER GOT THEM, WHICH IS WHAT KEPT THE ASSERT FALSIFIABLE**, and with a published
statement NEITHER block carries them. Block 0's `should_finalize` is 0, so its three `Field.equal`
gadgets still run at NONZERO differences and take the `(d⁻¹, 0)` branch — that half is unchanged and
is what a repair must preserve: a step statement carrying the derivation in BOTH blocks would leave
`(1 − finalized)·should_finalize = 0` with no failing instance the emitter can produce. -/

/-- ⚑ The block that claims `should_finalize`. Measured at both committed shapes: block 1's packed
word 53 is **1** and block 0's word 26 is 0 (`KimchiWrapMain` §19's own docblock), so block 1 is the
one whose deferred values must be derived and block 0 is the one that keeps `Field.equal`'s other
branch live. -/
def FIN_LIVE_BLOCK : Nat := 1

/-- `Shifted_value.Type2.of_field` of the derived `combined_inner_product` — the fold
`combine ζ + r · combine ζω` less `2^255`. -/
def FIN_DEFERRED_CIP : Nat :=
  10742481956508484414461324644563643284499330972958261991466391374195412245280
/-- …and of the derived `b` — `challenge_polynomial ζ + r · challenge_polynomial ζω`. -/
def FIN_DEFERRED_B : Nat :=
  1652019457232851511929345484207094574373269249791287408713807329851805585096
/-- …and the RAW 128-bit ξ′, the finalize sponge's first squeeze. -/
def FIN_DEFERRED_XI : Nat :=
  328188568881711558850681563153200103698

/-- ⚑⚑ **ENTRY `i`'s SCALAR IS MEASURED SINCE 2026-08-06 — it is the value the prover handed
`kimchi::verifier`.** `STEP_PUBLIC_IN` is `stepmain_step_r8_finalize.json`'s `public_input` as the
accepted proof consumed it, which `wrap_verifier.ml:539-548` reads as the expansion of a packed
`Types.Step.Statement`. There is nothing left to stand in for: the fixture that used to sit here was
`prevWordVal`'s `a^9` mixer over `exists ~request:Req.Proof_state`, and a mixer is only honest while
no proof's public input is available.

⚠ ⚑ **AND `split_field`'s DERIVATION IS GONE WITH IT — THE PAIR IS PUBLISHED.** This used to compute
`v / 2` and `v % 2` from one word, which made `wrap_main.ml:80`'s `2·y + is_odd = x` an identity on
two cells this file had just built. Both halves are separate PUBLISHED entries now, so the
recomposition is a fact about the step proof's own public input, and
`split_field_halves_are_published_bits` measures what is left to measure rather than restating a
definition. -/
def xhatScalar (i : Nat) : Nat :=
  Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.getD i 0

/-- ⚑⚑ **PACKED WORD `w`'s VALUE, RECOMPOSED FROM THE PUBLISHED ENTRIES.** `wrap_verifier.ml:542-548`
expands a `` `Field `` word into `(value, parity)` and leaves every other word alone; this inverts
that, so the 57 statement words and the 67 published entries are ONE object read two ways rather than
two constructions that must be kept in step.

⚠ ⚑ **IT WAS A NAMED FIXTURE (`a^9`) WITH THREE OVERRIDES UNTIL 2026-08-06, AND KEEPING IT WOULD HAVE
BEEN THE `whSgOld` DEFECT AGAIN.** The overrides existed to give W-WRAPHACK's two digests and
W-FINSPONGE's three deferred values a statement word to be equal to. With `xhatScalar` reading
`STEP_PUBLIC_IN`, a `prevWordVal` that still answered `FIN_DEFERRED_CIP` at word 27 would be a SECOND
copy of the statement disagreeing with the one the MSM consumes — the exact shape that kept
`xhatOut 67` unchanged while `RC_SGOLD` moved, and a green gate was the evidence.

⚠⚑ **WHAT THAT COSTS IS REAL AND IS NAMED, NOT ABSORBED.** The published statement's words 27, 28,
37, 54, 55 and 56 are NOT the values the wrap circuit derives for them, so the ties at `w9_prev`,
`w11_wraphack` and `w12_finsponge` have no satisfying witness on this step proof.
`the_published_statement_does_not_carry_the_derived_words` states exactly which six and refuses the
claim that it does; §15c‴ prices the repair. It is undone work on the STEP side, not a theorem of
this model. -/
def prevWordVal (w : Nat) : Nat :=
  let i := xhatEntryOf w
  if xhatIsSplitHi i then 2 * xhatScalar i + xhatScalar (i + 1) else xhatScalar i

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
(`wrap_verifier.ml:612-616`). This is the pair `wrap_verifier.ml:617` absorbs.

⚠ ⚑ **IT TAKES THE SELECTION, NOT A COUNT, AND THE OLD `xhatOut : Nat → _` IS DELETED.** A count
only names a selection through `xhatSel`, and `xhatSel` is Mina's entry space — so `xhatOut 12` would
have meant "Mina's named spread of twelve", not "this proof's twelve", while reading exactly like the
latter. That is the `nItems + 1` class again: one number, two meanings, no diff at the call site.
`WrapShape` now carries the entry list itself. -/
def xhatOutOf (sel : List Nat) : Nat × Nat := addAQ (xhatNegated sel) XHAT_H

/-! ## §19a — ⚑ **`Scalar_challenge.endo` AT Fq**, the `EndoMul` ladder W-COMBINE and W-BULLET run.

`scalar_challenge.ml:217-307`, read end to end. `num_bits = 128`, `bits_per_row = 4`, so
`rows = 32` — thirty-two `EndoMul` gates and one closing `Zero`, per ladder, and that count is what
closes Mina's own `EndoMul 2528` (§19's census in `KimchiWrapMain`).

⚑ **THE ENDO CONSTANT IS `Endo.Wrap_inner_curve.base`, NOT `Endo.Step_inner_curve.scalar`.**
`wrap_verifier.ml:121` instantiates the `Scalar_challenge` functor with `Endo.Wrap_inner_curve` —
Vesta's pair — and `endo.ml:6` says `base : Backend.Tock.Field.t = Pasta_bindings.Vesta.endo_base ()`.
That is an Fq element and it is the CURVE endomorphism eigenvalue, a different object from `ENDO_Q`
(`Pallas.endo_scalar ()`), which is the SCALAR `to_field_checked` lifts by. Both live in Fq and the
file uses both; `endo_base_q_is_the_curve_endomorphism` pins them apart against two independent
sources.

⚑ And it is the same constant the Rust prover's `EndoMul` gate polynomial uses: for a
**Pallas-committed** proof `KimchiCurve::other_curve_endo()` is `vesta_endos().0`
(`kimchi/src/curve.rs:102-104`), i.e. Vesta's BASE-field endo — the mirror of the step harness,
which proves on Vesta and gets Pallas's. A wrong choice here is refused by the prover, not
absorbed. -/

/-- `Endo.Wrap_inner_curve.base = Pasta_bindings.Vesta.endo_base ()` (`endo.ml:5-9`), an element of
`Backend.Tock.Field = Fq`. -/
def ENDO_BASE_Q : Nat :=
  2942865608506852014473558576493638302197734138389222805617480874486368177743

/-- `Scalar_challenge`'s own `num_bits` (`scalar_challenge.ml:214`) — the raw prechallenge width. -/
def ENDO_BITS : Nat := 128
/-- `bits_per_row` (`scalar_challenge.ml:225`). -/
def ENDO_BITS_PER_ROW : Nat := 4
/-- `rows = num_bits / bits_per_row` — the `EndoMul` gate count of ONE ladder. -/
def ENDO_BLOCKS : Nat := ENDO_BITS / ENDO_BITS_PER_ROW

/-- The `4·ENDO_BLOCKS` bits of `v`, MSB-first — `unpack scalar |> take 128 |> of_list_rev_map`. -/
def endoBitsOfQ (v : Nat) : List Nat :=
  (List.range (4 * ENDO_BLOCKS)).map (fun k => v / 2 ^ (4 * ENDO_BLOCKS - 1 - k) % 2)

/-- `xq(b) = (1 + (endo − 1)·b)·xt` (`scalar_challenge.ml:249`). -/
def xqOfQ (b xt : Nat) : Nat := qMul (qAdd 1 (qMul b (qSub ENDO_BASE_Q 1))) xt
/-- `yq(b) = (2b − 1)·yt` (`scalar_challenge.ml:250`). -/
def yqOfQ (b yt : Nat) : Nat := qMul (if b == 1 then (1 : Nat) else qN - 1) yt

/-- One `endo_mul` 4-bit block's STORED cells (`endosclmul.rs:48-56`): the intermediate point
`(xr,yr)`, the two stored slopes `s1`/`s3`, the distinct-point inverse `inv = w₂`, the output
`(xs,ys)`, and the four bits. `s2`/`s4` are constraint intermediates and are NOT stored. -/
structure EndoBlockQ where
  xr : Nat
  yr : Nat
  s1 : Nat
  s3 : Nat
  inv : Nat
  xs : Nat
  ys : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  b4 : Nat
  deriving Repr, Inhabited

/-- One block: `acc ← [2]([2]acc + Q₁) + Q₂` with `Qₖ = (2b_even − 1)·φ^{b_odd}(T)`, transcribed
line for line from `scalar_challenge.ml:249-271` at Fq. -/
def endoStepQ (xt yt xp yp b1 b2 b3 b4 : Nat) : EndoBlockQ :=
  let xq1 := xqOfQ b1 xt
  let yq1 := yqOfQ b2 yt
  let s1 := qMul (qSub yq1 yp) (qInv (qSub xq1 xp))
  let s2 := qSub (qMul (qMul 2 yp) (qInv (qSub (qAdd (qMul 2 xp) xq1) (qMul s1 s1)))) s1
  let xr := qSub (qAdd xq1 (qMul s2 s2)) (qMul s1 s1)
  let yr := qSub (qMul (qSub xp xr) s2) yp
  let xq2 := xqOfQ b3 xt
  let yq2 := yqOfQ b4 yt
  let s3 := qMul (qSub yq2 yr) (qInv (qSub xq2 xr))
  let s4 := qSub (qMul (qMul 2 yr) (qInv (qSub (qAdd (qMul 2 xr) xq2) (qMul s3 s3)))) s3
  let xs := qSub (qAdd xq2 (qMul s4 s4)) (qMul s3 s3)
  let ys := qSub (qMul (qSub xr xs) s4) yr
  let inv := qInv (qMul (qSub xp xr) (qSub xr xs))
  { xr := xr, yr := yr, s1 := s1, s3 := s3, inv := inv, xs := xs, ys := ys
  , b1 := b1, b2 := b2, b3 := b3, b4 := b4 }

/-- `φ(t) = (endo·xt, yt)` — the endomorphism image (`scalar_challenge.ml:230`, `Field.scale xt
Endo.base` with `yt` UNCHANGED). -/
def endoImgQ (T : Nat × Nat) : Nat × Nat := (qMul ENDO_BASE_Q T.1, T.2)
/-- `p = G.( + ) t (seal (Field.scale xt Endo.base), yt)` (`scalar_challenge.ml:230-231`). -/
def endoPQ (T : Nat × Nat) : Nat × Nat := addAQ T (endoImgQ T)
/-- ⚑ `acc₀ = ref G.(p + p)` (`scalar_challenge.ml:232`) — `2(t + φ(t))`, **not** `2t`. The two are
different gadgets: `scale_fast_unpack` seeds at `add_fast base base` and this seeds at the DOUBLED
sum, and getting them the same way round is the step side's recorded defect. -/
def endoSeedQ (T : Nat × Nat) : Nat × Nat := dblAQ (endoPQ T)

/-- One ladder's whole trace: the accumulator after each block, the blocks, and the counter chain
`nₑ₊₁ = 16nₑ + 8b₁ + 4b₂ + 2b₃ + b₄` from `n₀ = 0` (`scalar_challenge.ml:272-276`). -/
structure EndoDataQ where
  accs : List (Nat × Nat)
  blks : List EndoBlockQ
  ns : List Nat
  deriving Repr, Inhabited

/-- Run `Scalar_challenge.endo T v`. -/
def runEndoQ (T : Nat × Nat) (v : Nat) : EndoDataQ :=
  let bits := endoBitsOfQ v
  let st := (List.range ENDO_BLOCKS).foldl
    (fun (st : List (Nat × Nat) × List EndoBlockQ × List Nat) e =>
      let cur := st.1.getLastD (0, 0)
      let b := endoStepQ T.1 T.2 cur.1 cur.2
        (bits.getD (4*e) 0) (bits.getD (4*e+1) 0) (bits.getD (4*e+2) 0) (bits.getD (4*e+3) 0)
      (st.1 ++ [(b.xs, b.ys)], st.2.1 ++ [b],
       st.2.2 ++ [16 * st.2.2.getLastD 0 + 8*b.b1 + 4*b.b2 + 2*b.b3 + b.b4]))
    ([endoSeedQ T], [], [0])
  { accs := st.1, blks := st.2.1, ns := st.2.2 }

/-- …and the point it leaves. -/
def endoOutQ (T : Nat × Nat) (v : Nat) : Nat × Nat := (runEndoQ T v).accs.getLastD (0, 0)

/-! ## §19b — ⚑ **`group_map` AT Fq**: `Snarky_group_map.Checked.wrap` over the VESTA curve.

`wrap_verifier.ml:280-317` builds `Group_map.Bw19.Params.create (module Field.Constant) { b =
Inner_curve.Params.b }` — the SAME deterministic construction the step side runs, over a DIFFERENT
field. `bw19.ml:39-63` is a function of the field and `b` alone: `u` is the first non-zero abscissa
with non-zero `u³ + b` (so `u = 1`, `fu = 6` at `b = 5`, in either field), and the other three
params are `sqrt(−3u²)`, `(sqrt(−3u²) − u)/2` and `1/(3u²)`.

⚑ **AND `(sqrt(−3) − 1)/2` IS A PRIMITIVE CUBE ROOT OF UNITY** — so `BWQ_SQ3_MU2` is literally
`PastaCurve.zetaQ`, which is `ENDO_BASE_Q`. That is not a coincidence to lean on silently: it is
`bwq_params_are_the_field_construction`'s content, and it makes the group-map constants and the
curve endomorphism constant ONE measured value reached two independent ways. -/

private def qPowAuxQ : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | f + 1, base, e, acc =>
      if e == 0 then acc
      else qPowAuxQ f (qMul base base) (e / 2) (if e % 2 == 1 then qMul acc base else acc)

/-- `a^e` in `Fq`. -/
def qPowW (a e : Nat) : Nat := qPowAuxQ 300 (a % qN) e 1

/-- Euler's criterion over `Fq`. -/
def qIsSquare (a : Nat) : Bool := a % qN == 0 || qPowW a ((qN - 1) / 2) == 1

/-- `Aux.non_residue` (`snarky_group_map/checked_map.ml:5-9`): the first non-square from 2 up. It is
the multiplier `sqrt_flagged`'s `Field.if_` selects when `is_square` is false, so it is a CIRCUIT
constant and not only a witness-generation one. ⚠ It is 5 in `Fq` as it is in `Fp` — the same
number for two different reasons, and `fq_nonresidue_is_the_first_non_square` checks it here. -/
def FQ_NONRES : Nat := 5

/-- `Fq`'s two-adicity: `q − 1 = 2^32 · m`. -/
def FQ_S : Nat := 32
def FQ_M : Nat := (qN - 1) / 2 ^ FQ_S

private def qOrd2 : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, t => if t == 1 then 0 else 1 + qOrd2 f (qMul t t)

private def qTsGo : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, R => R
  | f + 1, M, c, t, R =>
      if t == 1 then R
      else
        let i := qOrd2 (FQ_S + 2) t
        let b := qPowW c (2 ^ (M - i - 1))
        qTsGo f i (qMul b b) (qMul t (qMul b b)) (qMul R b)

/-- A square root in `Fq` (Tonelli–Shanks at `FQ_NONRES`). ⚠ WHICH root: the same one arkworks'
`Field::sqrt` returns, which is the one `Group_map.Bw19.Params.create` calls. Either root satisfies
`assert_square`, so in the CIRCUIT it is a witness convention; in the PARAMS it is not, and
`bwq_params_are_the_field_construction` is what makes the choice measured rather than assumed. -/
def qSqrt (a : Nat) : Nat :=
  if a % qN == 0 then 0
  else qTsGo (FQ_S + 2) FQ_S (qPowW FQ_NONRES FQ_M) (qPowW a FQ_M) (qPowW a ((FQ_M + 1) / 2))

/-- `u` — the first abscissa with `u ≠ 0` and `u³ + b ≠ 0` (`bw19.ml:45-51`). -/
def BWQ_U : Nat := 1
/-- `fu = u³ + b` at `b = 5`. -/
def BWQ_FU : Nat := 6
/-- `sqrt(−3u²)` in `Fq`. -/
def BWQ_SQ3 : Nat :=
  5885731217013704028947117152987276604395468276778445611234961748972736355487
/-- `(sqrt(−3u²) − u)/2` in `Fq` — ⚑ and this IS `ENDO_BASE_Q`. -/
def BWQ_SQ3_MU2 : Nat :=
  2942865608506852014473558576493638302197734138389222805617480874486368177743
/-- `1/(3u²)` in `Fq`. -/
def BWQ_INV3U2 : Nat :=
  19298681539552699237261830834781317975575370987961098253119828498928908632065

/-- `Vesta.Params.b`. `Params.a = 0`, so `y_squared`'s `a·x` term folds away
(`wrap_verifier.ml:310-316` passes it, and `Field.mul` on a constant zero emits nothing). -/
def VESTA_B : Nat := 5

/-- `potential_xs t` (`bw19.ml:78-99`), the three candidate abscissae, at Fq. -/
def bwqPotentialXs (t : Nat) : Nat × Nat × Nat :=
  let t2 := qMul t t
  let alpha := qInv (qMul (qAdd t2 BWQ_FU) t2)
  let x1 := qSub BWQ_SQ3_MU2 (qMul (qMul (qMul t2 t2) alpha) BWQ_SQ3)
  let x2 := qSub (qSub 0 BWQ_U) x1
  let tp := qAdd t2 BWQ_FU
  let x3 := qSub BWQ_U (qMul (qMul (qMul tp tp) (qMul alpha tp)) BWQ_INV3U2)
  (x1, x2, x3)

/-- `group_map t` (`wrap_verifier.ml:280-317`) as a VALUE: the first candidate whose `y² = x³ + 5`
is a square, with its root. In-circuit all three roots are witnessed and `sqrt_flagged`'s
`is_square` bits select the first (`checked_map.ml:37-53`). -/
def gmapFq (t : Nat) : Nat × Nat :=
  let xs := bwqPotentialXs t
  let y2 : Nat → Nat := fun x => qAdd (qMul x (qMul x x)) VESTA_B
  if qIsSquare (y2 xs.1) then (xs.1, qSqrt (y2 xs.1))
  else if qIsSquare (y2 xs.2.1) then (xs.2.1, qSqrt (y2 xs.2.1))
  else (xs.2.2, qSqrt (y2 xs.2.2))

/-- ⚑ **`group_map`'s 43 CELLS, in emission order** — `Snarky_group_map.Checked.wrap`
(`snarky_group_map/checked_map.ml:20-55`) at Fq, one slot per Snarky operation:

    0 t2 · 1 tf · 2 ai · 3 alpha · 4 t4 · 5 ta · 6 x1 · 7 x2 · 8 ti · 9 tf2 · 10 tb · 11 x3
    12+6i  sq · qv · b · db · sel · y      (i = 0,1,2, the three candidates)
    30 p12 · 31 f2 · 32 f3
    33..37  the x dot-product (m0,m1,m2,s12,x)      ⚑ 37 IS `u.x`
    38..42  the y dot-product                        ⚑ 42 IS `u.y`

⚠ `db_i` is `(1 − m)·b_i·q_i` and `sel_i = m·q_i + db_i`, i.e. `Field.if_ b ~then_:q ~else_:(m·q)`
with the `(1 − m)` folded into the multiplication's coefficient — one half rather than two, and the
same value. -/
def gmValsQ (t : Nat) : List Nat :=
  let t2 := qMul t t
  let tf := qAdd t2 BWQ_FU
  let ai := qMul tf t2
  let alpha := qInv ai
  let t4 := qMul t2 t2
  let ta := qMul t4 alpha
  let x1 := qSub BWQ_SQ3_MU2 (qMul BWQ_SQ3 ta)
  let x2 := qSub (qSub 0 BWQ_U) x1
  let ti := qMul alpha tf
  let tf2 := qMul tf tf
  let tb := qMul tf2 ti
  let x3 := qSub BWQ_U (qMul BWQ_INV3U2 tb)
  let xs := [x1, x2, x3]
  let per := xs.flatMap (fun x =>
    let sq := qMul x x
    let qv := qAdd (qMul sq x) VESTA_B
    let b := if qIsSquare qv then 1 else 0
    let db := qMul (qSub 1 FQ_NONRES) (qMul b qv)
    let sel := qAdd (qMul FQ_NONRES qv) db
    [sq, qv, b, db, sel, qSqrt sel])
  let bv : Nat → Nat := fun i => per.getD (6 * i + 2) 0
  let yv : Nat → Nat := fun i => per.getD (6 * i + 5) 0
  let p12 := qSub (qAdd 1 (qMul (bv 0) (bv 1))) (qAdd (bv 0) (bv 1))
  let f2 := qSub (bv 1) (qMul (bv 0) (bv 1))
  let f3 := qMul p12 (bv 2)
  let fs := [bv 0, f2, f3]
  let dot : (Nat → Nat) → List Nat := fun g =>
    let m := (List.range 3).map (fun i => qMul (fs.getD i 0) (g i))
    let s12 := qAdd (m.getD 0 0) (m.getD 1 0)
    m ++ [s12, qAdd s12 (m.getD 2 0)]
  [t2, tf, ai, alpha, t4, ta, x1, x2, ti, tf2, tb, x3] ++ per ++ [p12, f2, f3]
    ++ dot (fun i => xs.getD i 0) ++ dot yv

/-- `group_map`'s OUTPUT, read off the emitted cells rather than restated. -/
def gmOutQ (t : Nat) : Nat × Nat := ((gmValsQ t).getD 37 0, (gmValsQ t).getD 42 0)

/-! ## §19d — ⚑ **`Scalar_challenge.endo_inv`'s WITNESS**, which is a scalar-field inversion.

`scalar_challenge.ml:343-354`:

    let endo_inv ((gx, gy) as g) chal =
      let res = exists G.typ ~compute:(fun () -> G.Constant.scale g Scalar.(one / x)) in
      let x, y = endo res chal in
      Field.Assert.(equal gx x ; equal gy y) ;
      res

so `endo_inv` is **an `endo` ladder plus two equality asserts plus an `Inner_curve.typ`**, and the
only new arithmetic is the WITNESS: `res = [x⁻¹]·g` where `x = Constant.to_field chal` lives in
Vesta's SCALAR field, which is **Fp**. Two consequences this file has to carry:

  * ⚑ **`g` MUST BE ON THE CURVE**, or no `res` exists at all. Upstream's `lr` arrives through
    `Openings.Bulletproof.typ`'s `Inner_curve.typ` and is on-curve by construction; §2d's filler was
    a bare `wrapFixture` and was not. `lrPointQ`/`deltaPointQ` below replace it with doublings of
    real SRS Lagrange bases — the same construction `ftcTVal` already uses for `t_comm` — so the
    absorbed words are points and `assert_on_curve` is satisfiable.
  * **`to_field_constant`** (`scalar_challenge.ml:138-152`) is the SAME crumb recurrence `emsAccsQ`
    runs, over Fp and at `Endo.Wrap_inner_curve.scalar` rather than over Fq at
    `Pallas.endo_scalar ()`. ⚠ Three constants named `endo` are in play in this file now and only
    this one is a SCALAR of the inner curve; `endo_inv_is_the_ladders_inverse` is what makes the
    choice measured — it runs the actual ladder on the actual witness and gets `g` back. -/

/-- `Endo.Wrap_inner_curve.scalar = Pasta_bindings.Vesta.endo_scalar ()` (`endo.ml:5-9`), an element
of `Backend.Tick.Field = Fp` — Vesta's scalar field, i.e. the field its group order lives in. -/
def ENDO_SCALAR_FP : Nat :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

private def pMod : Nat := Dregg2.Circuit.Emit.PastaField.pN
def pAddW (x y : Nat) : Nat := (x + y) % pMod
def pSubW (x y : Nat) : Nat := (x + pMod - y % pMod) % pMod
def pMulW (x y : Nat) : Nat := (x * y) % pMod

private def pPowAuxW : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | f + 1, base, e, acc =>
      if e == 0 then acc
      else pPowAuxW f (pMulW base base) (e / 2) (if e % 2 == 1 then pMulW acc base else acc)
/-- Inverse in **Fp** — Vesta's scalar field, which is where `one / x` is taken. -/
def pInvW (a : Nat) : Nat := pPowAuxW 300 (a % pMod) (pMod - 2) 1

/-- `to_field_constant ~endo:Endo.Wrap_inner_curve.scalar` (`scalar_challenge.ml:138-152`): the
`(a, b)` recurrence from `a₀ = b₀ = 2` over the 64 MSB-first crumbs of a 128-bit challenge, closed by
`a·endo + b`. ⚑ Identical in SHAPE to `emsAccsQ`'s, which is why `cFuncQ`/`dFuncQ` are the same two
tables — and different in FIELD and in CONSTANT, which is the whole point. -/
def toFieldConstantFp (v : Nat) : Nat :=
  let cr := (List.range (ENDO_BITS / 2)).map (fun j => v / 4 ^ (ENDO_BITS / 2 - 1 - j) % 4)
  let ab := cr.foldl
    (fun (ab : Nat × Nat) x =>
      ( pAddW (pAddW ab.1 ab.1) (if x == 2 then pMod - 1 else if x == 3 then 1 else 0)
      , pAddW (pAddW ab.2 ab.2) (if x == 0 then pMod - 1 else if x == 1 then 1 else 0) ))
    (2, 2)
  pAddW (pMulW ab.1 ENDO_SCALAR_FP) ab.2

/-- Vesta scalar multiplication, affine in / affine out (Jacobian inside, so one inversion total). -/
def vestaScMul (k : Nat) (P : Nat × Nat) : Nat × Nat :=
  match Dregg2.Circuit.Emit.PastaCurve.scMulM qN (k % pMod) (P.1, P.2, 1) with
  | none => (0, 0)
  | some J =>
    let zi := qInv J.2.2
    let z2 := qMul zi zi
    (qMul J.1 z2, qMul J.2.1 (qMul z2 zi))

/-- ⚑ **`endo_inv`'s WITNESS**: `[to_field(pre)⁻¹]·g`, so that `Scalar_challenge.endo` of it at the
SAME prechallenge returns `g`. -/
def endoInvPtQ (g : Nat × Nat) (pre : Nat) : Nat × Nat :=
  vestaScMul (pInvW (toFieldConstantFp pre)) g

/-- ⚑ `Ops.scale_fast ~num_bits:255`'s MULTIPLIER. `scale_fast_unpack` runs
`accₖ₊₁ = [2]accₖ + (2bₖ−1)·T` from `acc₀ = 2T` over 255 bits, which is `(2^255 + 2s + 1)·T` and NOT
`[s]·T` — the `Shifted_value.Type1` shift, in Vesta's scalar field. -/
def sfKQ (s : Nat) : Nat := (2 ^ 255 + 2 * s + 1) % pMod

/-! ### ⚑ **`lr` AND `delta` ARE A REAL IPA OPENING SINCE 2026-08-05.**

They were `xhatBase (5 + i % 50)` and `xhatBase 60` — **thirty-two of the thirty-three points were
fifty SRS Lagrange bases, cycled**, and §2d said so in writing ("`lr`/`delta` have no real source in
this tree at all"). The fix was not to build an opening: **an IPA opening IS `lr` and `delta`**, and
`pickles_kimchi_marshal`'s step proof has carried one all along — `ProverProof::create_recursive`
over Mina's own `SRS::<Vesta>::create(65536)`, which is what pins it to sixteen rounds. Nobody had
read them off. `tape.rs` now does, in the same run that produces the forty public words.

⚠ **WHAT THIS DOES NOT SAY.** These are the opening of a *smoke* step circuit, and the wrap
assembly does not yet CHECK the opening — W-BULLET consumes the points (32 endo ladders plus
`Inner_curve.typ`) and `w12_close` asserts `bulletproof_success`, but `combined_inner_product`'s
VALUE is still W-FINALIZE's. What changed is provenance, not verification: the words the transcript
absorbs are now a real `openings_proof`'s, so the challenges squeezed after them are challenges of
something. Cycling Lagrange bases could never be that, whatever `assert_on_curve` said about them. -/

/-- `openings_proof.lr.(r)`'s two points (`wrap_main.ml:381`) — round `i`, from the step proof's own
opening. `STEP_LR_XY` is four Fq coordinates per round: `Lx, Ly, Rx, Ry`. -/
def lrPointQ (i : Nat) : Nat × Nat :=
  ( Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_LR_XY.getD (2 * i) 0
  , Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_LR_XY.getD (2 * i + 1) 0 )

/-- `delta` (`wrap_main.ml:382`), from the same opening. -/
def deltaPointQ : Nat × Nat :=
  ( Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_DELTA_XY.getD 0 0
  , Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_DELTA_XY.getD 1 0 )

end Dregg2.Circuit.Emit.KimchiWrapMain

/-! ⚑ **THE FACTS LIVE IN THEIR OWN NAMESPACE, AND THAT IS NOT COSMETIC.**

The DEFINITIONS above are `Dregg2.Circuit.Emit.KimchiWrapMain`'s, because `KimchiWrapMain` uses them
unqualified and a rename would be churn for nothing. The THEOREMS are not: `#assert_namespace_axioms`
walks every theorem under a namespace, and with the facts filed under `…KimchiWrapMain` the pin at
the foot of `KimchiWrapMain.lean` swept this file's as well — measured, that took the wrap file from
185 s (green, every declaration checked) to unfinished at 9.6 GB. Each file now pins what it proves. -/
namespace Dregg2.Circuit.Emit.KimchiWrapMainField

open Dregg2.Circuit.Emit.KimchiWrapMain

-- ⚑ `set_option` is SCOPED TO THE NAMESPACE, so line 61's `maxRecDepth` died at the `end` above and
-- this section ran at the default 512. It stopped being enough once §19a/§19b landed: `qPowW` at a
-- 254-bit exponent and Tonelli–Shanks are 300-deep fuel recursions, and the kernel walks them.
set_option maxRecDepth 100000

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

set_option maxRecDepth 1000000 in
/-- The scalars respect their own widths — `scale_fast2`'s top-bit asserts have to be satisfiable by
the honest witness or every rung would refuse.

⚠ ⚑ **THE DEPTH BUDGET IS §15c″'s, AND IT IS NOT A WEAKENING.** Entries 65 and 66 are packed words
55 and 56, which stopped being fixtures when W-WRAPHACK landed: reducing them now runs two Fq
Poseidon sponges (16 permutations each) inside this scan. `decide` evaluates in the ELABORATOR,
where `maxRecDepth` bites — the kernel's own `rfl` path does the same work at 28 permutations in
`key_digest_is_the_index_digest` without it. The statement is unchanged; only the budget moved. -/
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

/-! ### §15a″ — ⚑ **THE STEP PROOF'S `x_hat`, AND THE ONE THEOREM THAT MAKES IT REAL.** -/

/-- ⚑ **THE WIDTH TABLE HAS A SECOND SOURCE, AND IT IS THE PROOF'S OWN.** `xhatBits` is this file's
transcription of `wrap_verifier.ml:542-548` over `Types.Step.Statement.spec 2 15`;
`STEP_XHAT_BITS` is the Rust exporter's `step_statement_slot_bits`, computed off the statement it
published and used there to refuse writing the fixture if a word did not fit its slot. Two
transcriptions of the same OCaml, and the fixture is where the SCALARS come from — so a width table
that drifted from the exporter's would range-check the published words at the wrong width and still
accept. -/
theorem xhat_entry_widths_are_the_exporters :
    (List.range XHAT_TERMS_FULL).map xhatBits
      = Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_XHAT_BITS
  ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_XHAT_BITS.length = XHAT_TERMS_FULL
  ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC = XHAT_TERMS_FULL
  ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.length = XHAT_TERMS_FULL
  ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_LAGRANGE_XY.length = 2 * XHAT_TERMS_FULL
  -- ⚑ …and the correction table is the PARTITION's length, 55, not 67.
  ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_XHAT_CORRECTION_XY.length = 2 * 55 := by
  decide

/-- ⚑⚑ **THE 67-ENTRY MSM IS THIS PROOF'S OWN `x_hat`.**

`wrap_verifier.ml:539-616` in full — the correction reduce over the 55-entry `Add_with_correction`
partition, the `scale_fast2'` ladders and `Cond_add` selects over the step SRS's Lagrange basis **at
this proof's domain**, `Inner_curve.negate`, and the `x_hat blinding` add — evaluated on dregg's own
step proof's published `Types.Step.Statement`, IS the negated public-input commitment
`kimchi::verifier` computed for that proof (`verifier.rs:834-857`) and absorbed at
`wrap_verifier.ml:617` as the transcript's `x_hat` block.

⚑ **THIS IS THE STATEMENT `w6_xhat` HAS NEVER HAD AT THE COMMITTED SHAPE.** Until 2026-08-06 the 67
scalars were a NAMED FIXTURE standing in for `exists ~request:Req.Proof_state`, so the fold's output
reproduced nothing and could not — there was no proof whose public input those scalars were. A
twelve-entry side table over a second index space got the identity for a step rule that published
twelve unconstrained words; this gets it for the 67 the wrap circuit actually expands.

⚠ `native_decide`: 55 ladders at up to 51 chunks, three `qInv` per step. `#assert_compiled` is the
confession, per `docs/GUARD-DISCIPLINE.md`. The same identity is asserted a SECOND time, in Rust and
in arkworks' own group arithmetic, by `tape.rs` before it writes the fixture — so this is two
implementations agreeing on one point, not one implementation agreeing with itself. -/
theorem the_xhat_msm_is_this_proofs_public_input_commitment :
    xhatOutOf (List.range XHAT_TERMS_FULL)
      = (Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBCOMM_XY.getD 0 0,
         Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBCOMM_XY.getD 1 0) := by
  native_decide

#assert_compiled the_xhat_msm_is_this_proofs_public_input_commitment

/-- ⚑ **THE NON-VACUITY OF THE DOMAIN TRAP** — the two tables really are different points.

`MinaStepSrsLagrange.LAGRANGE_XY` holds Vesta Lagrange commitments of the SAME
`SRS::<Vesta>::create(65536)` at Mina's `step-transaction` domain, so `onCurveQ`, the width census
and every other predicate this file owns is satisfied by BOTH tables — that is the whole trap, and
it is the same shape as `lrPointQ i = xhatBase (5 + i % 50)`. This says the substitution a reader
might make is a real substitution: not one of the 67 bases, and not one of the 55 corrections,
coincides with the 65536-domain table at the same index.

⚠ **WHAT CATCHES THE SUBSTITUTION IS `the_xhat_msm_is_this_proofs_public_input_commitment`, NOT
THIS.** The MSM lands on the commitment kimchi absorbed only for the right domain's basis; swap the
table and that theorem reds. This one exists so "it would red" is not resting on two tables that
might have been equal. -/
theorem xhat_bases_are_not_minas_step_transaction_domains :
    (List.range XHAT_TERMS_FULL).all (fun i =>
      xhatBase i != (Dregg2.Circuit.Emit.MinaStepSrsLagrange.LAGRANGE_XY.getD (2 * i) 0,
                     Dregg2.Circuit.Emit.MinaStepSrsLagrange.LAGRANGE_XY.getD (2 * i + 1) 0))
      = true
  ∧ (List.range 55).all (fun k =>
      (Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_XHAT_CORRECTION_XY.getD (2 * k) 0,
       Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_XHAT_CORRECTION_XY.getD (2 * k + 1) 0)
        != (Dregg2.Circuit.Emit.MinaStepSrsLagrange.CORRECTION_XY.getD (2 * k) 0,
            Dregg2.Circuit.Emit.MinaStepSrsLagrange.CORRECTION_XY.getD (2 * k + 1) 0)) = true
  -- ⚑ …and neither comparison is against a `getD` default: both of Mina's tables are long enough.
  ∧ decide (2 * XHAT_TERMS_FULL ≤ Dregg2.Circuit.Emit.MinaStepSrsLagrange.LAGRANGE_XY.length) = true
  ∧ decide (2 * 55 ≤ Dregg2.Circuit.Emit.MinaStepSrsLagrange.CORRECTION_XY.length) = true := by
  decide

/-- ⚑ **`Generators.h` IS ONE POINT WITH TWO SOURCES.** `XHAT_H` comes from
`xhat_lagrange_export.rs`'s `SRS::<Vesta>::create(2^16)`; `STEP_URS_H_XY` comes from
`tape.rs` reading `blinding_commitment()` off the verifier index of the proved circuit, which is
openmina's `get_srs::<Fp>()`. Two binaries, two objects, one point — and if they ever disagreed the
blinding add would be over a base the commitment was not masked with, which is invisible to every
curve check and moves `x_hat` by a full point. -/
theorem xhat_blinding_base_has_two_sources :
    XHAT_H = (Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_URS_H_XY.getD 0 0,
              Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_URS_H_XY.getD 1 0)
  ∧ onCurveQ XHAT_H := by decide

/-- ⚑ **EVERY CORRECTION IS THE SHIFT ITS OWN LADDER USES** — `negate (pow2pow g actual_shift)`
against that entry's `xhatActualBits`, which is **255** for a 255-bit slot and **130** (not 128) for
a 128-bit one. A correction computed at the wrong shift is on-curve, is a genuine SRS object, and
cancels nothing; `xhat_correction_shift_matches_the_ladder` says the two FORMULAS agree and this says
the fifty-five published POINTS do.

⚠ The one-bit entries are excluded by the filter and not by an arm: they take `` `Cond_add ``, have
no ladder and have no correction, which is why the table is 55 long. -/
theorem xhat_corrections_are_the_ladders_own_shift :
    ((List.range XHAT_TERMS_FULL).filter (fun i => xhatChunksAt i != 0)).all (fun i =>
      xhatCorr i
        == negAQ ((List.range (xhatActualBits i)).foldl (fun P _ => dblAQ P) (xhatBase i))) = true
  ∧ ((List.range XHAT_TERMS_FULL).filter (fun i => xhatChunksAt i != 0)).length = 55
  ∧ (((List.range XHAT_TERMS_FULL).filter (fun i => xhatChunksAt i != 0)).map xhatActualBits).eraseDups
      = [255, 130] := by
  native_decide

#assert_compiled xhat_corrections_are_the_ladders_own_shift

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

/-- ⚑ **`xhatEntryOf` IS `xhatWordOf`'s SECTION**, in both directions that matter: every word maps
back to an entry that maps forward to it, and on a `` `Field `` word that entry is the VALUE half —
so `prevWordVal`'s `2·hi + lo` reads the pair and not a pair shifted by one.

⚑ It is what lets `prevWordVal` be a closed form rather than a 67-test search over `xhatWordOf`'s
fibre, which is read once per statement word per emitted row. -/
theorem prev_entry_map_inverts_the_expansion :
    (List.range PREV_WORDS).all (fun w => xhatWordOf (xhatEntryOf w) == w) = true
  ∧ (List.range PREV_WORDS).all (fun w =>
      xhatIsSplitHi (xhatEntryOf w) == decide (w < PREV_PER_PROOF_WORDS * XHAT_PREVS
                                               && w % PREV_PER_PROOF_WORDS < 5)) = true
  ∧ (List.range PREV_WORDS).all (fun w => !xhatIsSplitLo (xhatEntryOf w)) = true
  ∧ ((List.range XHAT_TERMS_FULL).filter xhatIsSplitHi).all (fun i =>
      xhatEntryOf (xhatWordOf i) == i) = true := by
  decide

/-- ⚑⚑ **`split_field`'s TWO HALVES ARE PUBLISHED, SO THE RECOMPOSITION STOPPED BEING A DERIVATION.**
`wrap_main.ml:80` asserts `2·y + is_odd = x`. Before `w9_prev` this file drew `y` and `is_odd`
independently and DEFINED `x` as their recomposition, so the assert could not fail. At `w9_prev` `x`
became a packed statement word and the halves became `v / 2` and `v % 2` — better, and still a
derivation this file performed. Since 2026-08-06 both halves are separate entries of the step
proof's own `public_input`, and `prevWordVal` is what reads them BACK.

⚠ **SO THE EQUATION IS NOW DEFINITIONAL AND THIS THEOREM DOES NOT STATE IT.** `prevWordVal w` IS
`2·hi + lo`; asserting that would be a pin against its own definition. What is a fact about the
published data is stated instead: every parity half really is a BIT, so `Boolean.typ`'s check has an
honest witness and `xhatBits`' `WQ_BOOL` is a description rather than a truncation; every
recomposition fits `Field.size_in_bits`, so `w7_split`'s equation holds over ℕ and not merely mod
`qN`; and both bit values occur, so neither `Cond_add` arm is dead. A statement whose halves were
derived could not fail any of these. -/
theorem split_field_halves_are_published_bits :
    ((List.range XHAT_TERMS_FULL).filter xhatIsSplitLo).all (fun i =>
      decide (xhatScalar i < 2)) = true
  ∧ ((List.range XHAT_TERMS_FULL).filter xhatIsSplitHi).all (fun i =>
      decide (2 * xhatScalar i + xhatScalar (i + 1) < 2 ^ WQ_FIELD)) = true
  ∧ (((List.range XHAT_TERMS_FULL).filter xhatIsSplitLo).map xhatScalar).eraseDups.length = 2 := by
  decide

/-- ⚑⚑⚑ **THE STEP STATEMENT IS PUBLISHED, AND IT DOES NOT CARRY THE WORDS THE WRAP CIRCUIT DERIVES.
THIS IS UNDONE WORK ON THE STEP SIDE, STATED AS A REFUSAL SO IT CANNOT BE MISREAD AS CLOSED.**

Three sub-circuits of `wrap_main` tie a packed statement word to a value the wrap circuit computes:

  * **W-FINSPONGE** (`wrap_main.ml:258-338`) — `finalize_other_proof` recomputes the finalizing
    block's `combined_inner_product`, `b` and `xi`, packed words `27·FIN_LIVE_BLOCK + {0, 1, 10}`,
    and `Field.equal`s each against the statement's;
  * **W-WRAPHACK** (`wrap_main.ml:340-348`) — the two `hash_messages_for_next_wrap_proof` squeezes
    ARE packed words 55 and 56;
  * **W-PREV** (`wrap_main.ml:350-351`) — packed word 54 is `Field.Assert.equal`-tied to Mina's
    public slot 12.

Until 2026-08-06 `prevWordVal` ANSWERED WITH THOSE DERIVATIONS at exactly those six words, so all
three ties held by construction and none of them was a question. The scalars are the step proof's own
`STEP_PUBLIC_IN` now, and this measures what that costs: **six words disagree**, and the emitted rows
above `w9_prev` have no satisfying witness on this step proof.

⚠ ⚑ **THE REPAIR WAS PRICED AS A STEP-SIDE FIXPOINT UNTIL 2026-08-06, AND IT IS NOT ONE — WHICH IS
WHY IT KEPT NOT HAPPENING.** This paragraph used to read: the step proof must be re-proved with a
statement whose six words are the wrap's own derivation, and each is an x_hat MSM entry, so
re-proving moves `x_hat`, moves every challenge below it, and moves the derivation. The first clause
is true and the inference is not. `KimchiWrapMain.the_deferred_derivation_does_not_read_the_words_it
_checks` (`…Pins12` §20c) computes the transitive input cone of the two values W-FINSPONGE derives,
over its own 1732-op emitted program, and the three cells it checks are absent from it — **no
transcript squeeze reaches §19 or §20 at all**, because their β, γ and ζ are packed statement words
and their sponge is a fresh one over `finSpTape`. Three independent strata, one evaluation, no loop.

⚠ **AND THE ORDER MATTERS LESS THAN WHAT IT UNCOVERED.** Of the six, only 55 and 56 are FREE on the
step side (`vStmtWrapMsg0` / `vStmtWrapMsgs`, sourceless, no row writes them). Words 27, 28, 37 and 54
are `bpDiv2`/`bpOdd`, `vXiStmt` and `hmOutDigestVar` — values the STEP circuit derives — so writing
the wrap's numbers there makes the step circuit unsatisfiable. The disagreement at 27/28/37 is
therefore two derivations of one quantity, and the wrap's runs on `finColVal`/`finPZetaVal`/
`finPZetaWVal`/`finFtEval1Val`, which are `wrapFixtureQ` fixtures standing where
`prev_proof.openings.evals` belongs. Wiring those to the step proof's real evaluations is the repair,
and it crosses a FIELD BOUNDARY — the evaluations are **Fp** and this circuit is native **Fq**, so
they enter only through `Other_field` (`impls.ml:167-217`). That encoding, not a fixpoint, is what
stands between `w9_prev` and the top of the ladder.

⚑ **WHAT IS NOT AFFECTED, MEASURED RATHER THAN ASSERTED.** None of the six is absorbed by the
transcript and none is read at or below `w4_bind`, which is why the twenty-two slots that rung
derives are unmoved — the last two conjuncts say the six words are exactly the derived ones and that
the other 51 carry the published statement unaltered. -/
theorem the_published_statement_does_not_carry_the_derived_words :
    prevWordVal (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK) ≠ FIN_DEFERRED_CIP
  ∧ prevWordVal (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 1) ≠ FIN_DEFERRED_B
  ∧ prevWordVal (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 10) ≠ FIN_DEFERRED_XI
  -- ⚑ …and the six are the ONLY words at issue: every other packed word is a published entry and
  -- nothing in this file claims a value for it.
  ∧ ((List.range PREV_WORDS).filter (fun w =>
      w == PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK
      || w == PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 1
      || w == PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 10
      || w == PREV_MSG_NEXT_STEP || w == PREV_MSG_NEXT_STEP + 1
      || w == PREV_MSG_NEXT_STEP + 2)).length = 6
  ∧ PREV_WORDS - 6 = 51
  -- ⚑ …and what the statement DOES carry there, exhibited rather than only denied: three small
  -- structured numerals where three Fq derivations belong. A reader can see the gap's shape.
  ∧ (prevWordVal PREV_MSG_NEXT_STEP.succ, prevWordVal (PREV_MSG_NEXT_STEP + 2))
      = (160000365, 77001823)
  ∧ decide (prevWordVal (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 10) < 2 ^ WQ_CHAL) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 1000000 in
/-- ⚑ **THE SCALARS MOVED.** The red control for `w9_prev`, kept for the same reason
`xhat_derived_is_not_the_old_fixture` keeps `RC_XHAT`: the value the MSM used to consume, exhibited
rather than merely asserted to be gone. `wrapFixtureQ 21 i / 7 % 2 ^ xhatBits i` was §15c's filler.

⚠ **THE HONEST COUNT IS 63 OF 67, NOT 67 OF 67**, and the residue is not a hole: a one-bit entry has
two possible values, so four of the twelve `Cond_add` scalars coincide with the old filler by
arithmetic and not by inheritance. Every entry the MSM runs a LADDER over — all **55** — moved.
Quoting 67 here would be the flattering number of a pair.

⚑ **THE GENERAL FACTS COME FIRST AND THE COUNT IS THE INSTANCE THEY IMPLY.** The first two conjuncts
are what this control is actually for — *no ladder entry agrees with the old filler*, and *every
entry that does agree is a one-bit one* — and neither moves when a packed word's value changes. The
count does: it was measured at 62 while a candidate repair derived packed word 31, because that
word's parity landed on the filler's bit. A statement whose only content is a count reds on a
coincidence and says nothing about what changed.

⚠ The depth budget is §15c″'s, exactly as in `xhat_scalars_fit_their_widths`. -/
theorem xhat_scalars_are_not_the_old_per_entry_fixture :
    ((List.range XHAT_TERMS_FULL).filter (fun i =>
      xhatChunksAt i != 0 && xhatScalar i == wrapFixtureQ 21 i / 7 % 2 ^ xhatBits i)).length = 0
  ∧ ((List.range XHAT_TERMS_FULL).filter (fun i =>
      xhatScalar i == wrapFixtureQ 21 i / 7 % 2 ^ xhatBits i)).all
        (fun i => xhatBits i == WQ_BOOL) = true
  ∧ ((List.range XHAT_TERMS_FULL).filter (fun i =>
      xhatScalar i != wrapFixtureQ 21 i / 7 % 2 ^ xhatBits i)).length = 63 := by
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

/-! ### §19c — the pins on this value layer, as NAMED THEOREMS. -/

/-- ⚑ **`ENDO_BASE_Q` IS THE CURVE ENDOMORPHISM, AND IT IS NOT `ENDO_Q`.**

  * it is a NONTRIVIAL cube root of unity in `Fq` — the property `endo_base` HAS
    (`poly-commitment/src/ipa.rs:64-80`, `mina_poseidon::sponge::endo_coefficient`), checked;
  * it is `(sqrt(−3) − 1)/2`, i.e. the group map's own `sqrt_neg_three_u_squared_minus_u_over_2`,
    arrived at by a construction that never mentions an endomorphism;
  * and it is NOT `Pallas.endo_scalar ()`, the Fq element `to_field_checked` lifts by
    (`KimchiWrapMain.ENDO_Q`). Two Fq constants, two different jobs, one file. -/
theorem endo_base_q_is_the_curve_endomorphism :
    qMul (qMul ENDO_BASE_Q ENDO_BASE_Q) ENDO_BASE_Q = 1
    ∧ ENDO_BASE_Q ≠ 1
    ∧ ENDO_BASE_Q = BWQ_SQ3_MU2
    ∧ ENDO_BASE_Q
        ≠ 26005156700822196841419187675678338661165322343552424574062261873906994770353 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE Bw19 PARAMS ARE THE FIELD CONSTRUCTION, NOT A COPY OF THE STEP SIDE'S.**
`bw19.ml:52-62` is `sqrt(−3u²)`, `(that − u)/2` and `1/(3u²)`; each is checked here by its DEFINING
equation rather than against a transcription. ⚑ The last conjunct is the one that would catch the
copy-paste: `Fp`'s `sqrt_neg_three_u_squared` is a different number, and reduced mod `q` it is not a
square root of `−3`. -/
theorem bwq_params_are_the_field_construction :
    qMul BWQ_SQ3 BWQ_SQ3 = qSub 0 3
    ∧ qAdd (qMul 2 BWQ_SQ3_MU2) BWQ_U = BWQ_SQ3
    ∧ qMul 3 BWQ_INV3U2 = 1
    ∧ BWQ_FU = qAdd (qMul BWQ_U (qMul BWQ_U BWQ_U)) VESTA_B
    ∧ qMul 17006931536212783554987228065028097629383328157457783420645920607630467569011
           17006931536212783554987228065028097629383328157457783420645920607630467569011
        ≠ qSub 0 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `FQ_NONRES` is the first non-square from 2 up (`checked_map.ml:5-9`), and `FQ_S`/`FQ_M` are
`Fq`'s real two-adic decomposition — the two facts Tonelli–Shanks is wrong without. -/
theorem fq_nonresidue_is_the_first_non_square :
    qIsSquare 2 = true ∧ qIsSquare 3 = true ∧ qIsSquare 4 = true
    ∧ qIsSquare FQ_NONRES = false
    ∧ 2 ^ FQ_S * FQ_M = Dregg2.Circuit.Emit.PastaField.qN - 1 ∧ FQ_M % 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ `group_map`'s output is ON VESTA, and the ladder seed is the DOUBLED endo sum rather than the
plain doubling. Both on a real value: `RC_DIGEST`-scale input is out of the kernel's reach, so this
runs on a small one and the emitter's own values are checked by the harness. -/
theorem gmap_fq_lands_on_vesta :
    onCurveQ (gmapFq 7) = true
    ∧ onCurveQ (gmapFq 12345) = true
    ∧ qMul (gmapFq 7).2 (gmapFq 7).2
        = qAdd (qMul (gmapFq 7).1 (qMul (gmapFq 7).1 (gmapFq 7).1)) VESTA_B := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **`2(t + φ(t))` IS NOT `2t`** — the seed defect the step side paid for, refuted here on the
Vesta generator rather than described. `φ(t)` keeps `t`'s ordinate and scales only the abscissa. -/
theorem endo_seed_is_the_doubled_endo_sum :
    endoImgQ (xhatBase 0) = (qMul ENDO_BASE_Q (xhatBase 0).1, (xhatBase 0).2)
    ∧ endoSeedQ (xhatBase 0) ≠ dblAQ (xhatBase 0)
    ∧ endoSeedQ (xhatBase 0) = dblAQ (addAQ (xhatBase 0) (endoImgQ (xhatBase 0)))
    ∧ onCurveQ (endoImgQ (xhatBase 0)) = true
    ∧ onCurveQ (endoSeedQ (xhatBase 0)) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The ladder's shape: 32 blocks, 33 accumulator points, and a counter chain that ENDS at the
scalar — which is what `Field.Assert.equal !n_acc scalar` (`scalar_challenge.ml:305`) makes the
emitter wire as a σ class rather than as a row. -/
theorem endo_ladder_counter_reconstructs_the_scalar :
    ENDO_BLOCKS = 32
    ∧ (runEndoQ (xhatBase 0) 12345).ns.getLastD 0 = 12345
    ∧ (runEndoQ (xhatBase 0) 12345).accs.length = ENDO_BLOCKS + 1
    ∧ (runEndoQ (xhatBase 0) 12345).blks.length = ENDO_BLOCKS
    ∧ (endoBitsOfQ 12345).length = 4 * ENDO_BLOCKS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide


/-- ⚑ **THE LADDER AND ITS INVERSE, ON THE SAME POINT** — the one check that ties `ENDO_BASE_Q`
(an Fq BASE-field constant, used by the `EndoMul` gate) to `ENDO_SCALAR_FP` (an Fp SCALAR-field
constant, used by the witness generator). Get either wrong, or confuse `Step_inner_curve` with
`Wrap_inner_curve`, and `endo_inv`'s two `Field.Assert.equal` cannot be satisfied — which is the
failure §13 records as the `MinaWrapFtEval0Weld` defect, in the direction nothing had tested. -/
theorem endo_inv_is_the_ladders_inverse :
    endoOutQ (endoInvPtQ (lrPointQ 0) 12345) 12345 = lrPointQ 0
    ∧ onCurveQ (lrPointQ 0) = true
    ∧ onCurveQ (endoInvPtQ (lrPointQ 0) 12345) = true
    ∧ onCurveQ deltaPointQ = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- …and `Scalar_challenge.endo` IS scalar multiplication by `to_field_constant`, which is what
makes the inverse above the right object rather than a coincidence at one point. -/
theorem endo_ladder_is_scalar_multiplication :
    endoOutQ (lrPointQ 1) 12345 = vestaScMul (toFieldConstantFp 12345) (lrPointQ 1)
    ∧ ENDO_SCALAR_FP ≠ ENDO_BASE_Q := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ⚠ ⚑ **THE THREE `except`ED NAMES ARE §15a″'s, AND EACH CARRIES ITS OWN `#assert_compiled`.**

They are the only theorems in this file the kernel cannot reach, and the reason is one number: each
runs twelve `scale_fast2'` ladders of 51 five-bit chunks — 612 chunk steps at three `qInv` apiece,
where a `qInv` is a 254-bit modular inversion. `xhat_scalars_fit_their_widths` sits next door at
`maxRecDepth 1000000` and closes by `decide` because it runs NO ladder; this file's own note on
`shapeWrap.xhatXY` says the 1805-chunk version is out of the kernel's reach, and 612 is the same
wall a third of the way along.

⚠ **`#assert_compiled` under each is the confession, not a certificate** (`docs/GUARD-DISCIPLINE.md`)
— it passes only if the proof rests on a `native_decide` oracle and nothing worse, and it ERRORS on a
kernel-clean proof, so neither can launder a weaker fact downward. And the headline,
`the_xhat_msm_is_this_proofs_public_input_commitment`, is additionally asserted by a SECOND
implementation in arkworks' own group arithmetic — `tape.rs` refuses to write the fixture unless
`−Σ pᵢ·Lᵢ + h` is the commitment `kimchi::verifier` absorbed. Two implementations, one point. That is
what makes the compiled evaluation here a cross-check rather than a single trusted run.

⚑ The list is SHORTER since 2026-08-06: `xhat_bases_are_not_minas_step_transaction_domains` compares
two constant tables and closes in the kernel now that it no longer has to run a fold. -/
#assert_namespace_axioms Dregg2.Circuit.Emit.KimchiWrapMainField except
  the_xhat_msm_is_this_proofs_public_input_commitment
  xhat_corrections_are_the_ladders_own_shift

end Dregg2.Circuit.Emit.KimchiWrapMainField
