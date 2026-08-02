/-
# Dregg2.Circuit.Emit.KimchiStepMain — `step_verifier.verify_one`, assembled in Lean

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

`KimchiComposeStepFragment` proved the MSM *shape* at scale (132 rows, four gate types, 13 σ-only
probes rejected, a 4058-row ladder). **This file assembles the recursive verifier itself**, in the
five named sub-circuits `verify_one` runs, each provable on its own and each composing into the next.

## ⚑ THE TARGET, CORRECTED (read this before quoting a fraction)

`StepTransactionProof` is `{PRIMARY_LEN 67, ROWS 17806}` — and it is instantiated with
**`N_PREVIOUS = 0`** (`~/dev/mina-rust/crates/ledger/src/proofs/transaction.rs:4286`
`step::step::<StepTransactionProof, 0>`). **Those 17806 rows contain ZERO `verify_one` calls**; they
are the transaction-application `rule.main` plus `hash_messages_for_next_step_proof`. The row
identity is `ROWS = gate_rows + PRIMARY_LEN` (`transaction.rs:3830`), so 17739 gate rows + 67.

The recursive verifier is exercised by the branches that HAVE previous proofs:
`StepMergeProof` (2 prevs, ROWS 29010, `merge.rs:212,276`), `StepBlockProof` (2 prevs, 34797),
`StepZkappProvedProof` (1 prev, 20023). Costed from Snarky's own emitters
(`plonk_constraint_system.ml`; `Ops.add_fast` = 1 `CompleteAdd`; `scale_fast2 ~num_bits:128` =
26 chunks × 2 + 2 = **54 rows**; `~num_bits:255` = 51 × 2 + 2 = **104**; `Scalar_challenge.endo
~num_bits:128` = 32 `EndoMul` + 1 `Zero` + 2 `CompleteAdd` = **35**; `to_field_checked ~num_bits:128`
= **8 `EndoMulScalar`**; one Poseidon permutation = 11 + 1 = **12**), ONE `verify_one` is
**≈ 6.7k rows**:

  * x_hat MSM (`multiscale_known`)             ≈ 1972 `var_base_mul`-family rows + ~30 adds
  * the 47-commitment fold (`combine_split_commitments`) 46 × (endo 35 + add 1) = **1656**
  * `bullet_reduce`, 15 rounds                  15 × (2 endo + add) + 14 add = **1079**
  * `ft_comm`                                   8 × 104 + 8 = **840**
  * `check_bulletproof` tail                    ≈ **460**
  * `finalize_other_proof`                      ~20 × 8 endo-scalar = 160, + ≈ 560 poseidon

**That ≈ 6.7k-row `verify_one` is this file's target**, and the committed shape is sized against its
line items, not against a round number.

## THE FIVE SUB-CIRCUITS

  * **R1 `transcript`** — the Fp Poseidon SPONGE: an init pin, `absorbs` absorb blocks (a `Generic`
    absorb row + an 11-row `Poseidon` permutation + its output `Zero` row), then `chals` squeeze
    permutations. The sponge STATE crosses every block boundary as a σ class — the thing no prior
    rung had: `KimchiRenderPoseidon` proved ONE permutation with an IDENTITY permutation
    (`sevenNones`, self-wired), so a `Poseidon` gate had never been copy-wired to anything.
  * **R2 `challenges`** — `to_field_checked` (`scalar_challenge.ml:12-128`, `bits_per_row = 16`):
    per squeezed challenge, `emsRows = 8` chained `EndoMulScalar` rows, the `(n,a,b)` accumulators
    hopping row→row through σ (row `k`'s `n₈`/`a₈`/`b₈` at cols 1/4/5 IS row `k+1`'s `n₀`/`a₀`/`b₀`
    at cols 0/2/3), `n₀=0, a₀=2, b₀=2` PINNED by `Generic` rows, and a `Generic` decomposition row
    tying the chain's reconstructed `n₈` back to the SPONGE OUTPUT variable. `EndoMulScalar` had
    never been chained and had never been wired to another gate type.
  * **R3 `msm`** — `multiscale_known` / `ft_comm`: `msmTerms` `var_base_mul` scalar multiplications
    of `msmChunks` 5-bit chunks (`bits_per_chunk = 5`, `plonk_curve_ops.ml:66`), summed by a
    `complete_add` chain. ⚑ Each term's scalar counter chain CLOSES ON ITS CHALLENGE: term `i`'s
    final `n'` cell (col 5) and its challenge's final `n₈` cell (col 1) are the SAME VARIABLE, so
    the value `EndoMulScalar` decoded is the value `VarBaseMul` multiplies by — one σ class spanning
    three gate types and three sub-circuits.
  * **R4 `ipa`** — `combine_split_commitments` + `bullet_reduce`: `ipaRounds` `Scalar_challenge.endo`
    scalar multiplications of `ipaBlocks` 4-bit blocks each (the row-OVERLAP chaining pattern, no σ
    hop), each closing on its own challenge, folded by a second `complete_add` chain.
  * **R5 `deferred` + `cip` + `closing`** — two of `finalize_other_proof`'s deferred words:
    `b(ζ) = ∏(1 + uᵢ·ζ^{2^{k−1−i}})` (`Wrap.challenge_polynomial`, `wrap.ml:15-17`; the product
    `KimchiVerify.bEvalSq` folds) and `combined_inner_product = Σ_k ξ^k·(evₖ(ζ) + r·evₖ(ζω))`
    (`Common.combined_evaluation`, the `2 × cipEvals` `mul_and_add`s; pinned against
    `KimchiVerify.combinedInnerProduct`, transcribed READ-ONLY from `verifier.rs`) — both as
    `Generic` chains over the CHALLENGE variables. Then the closing tie of every one of the
    `pubWords` public words to a computed circuit variable. This rung turns the public input on:
    `placeChecked` (not `place`) with `Contract ⟨pubWords, AUX⟩`, so a public word no gate reads
    REFUSES rather than sitting inert, and the circuit's own ids cannot be silently absorbed into
    the public input.

## ⚑ THE SHAPE ORACLE — MEASURED against Mina's own compiled step circuit

o1-labs publishes Mina's compiled circuits as `*_gates.json` release blobs (kimchi's
`Circuit { public_input_size, gates }` serde form; `bridge/mina-zkapp/scripts/
mina-canonical-circuit-oracle.mjs`, whose digest reproduces the md5 in o1-labs' own asset filename).
**`step-zkapp-proved` is branch 4 — the step branch that RUNS `verify_one` on a side-loaded proof**:
PI 67, 20,023 gates, 13,778 non-Generic. Measured against this file's `shapeStep` (2026-08-01):

    gate            Mina step-zkapp-proved     shapeStep    run-lengths (Mina / here)
    total gates            20023                  6459
    non-Generic            13778                  6182
    Poseidon                6292 (31.4%)          1034        11×572    / 11×94    ✓ EXACT
    Generic                 6245 (31.2%)           277        —
    EndoMul                 2465 (12.3%)          2432        32×77+1×1 / 32×76    ✓ EXACT
    Zero                    2246 (11.2%)          1432        —
    VarBaseMul              1596  (8.0%)           988        1×1596    / 1×988    ✓ EXACT
    EndoMulScalar            776  (3.9%)           184        / 8×23  — upstream also runs
                    2×42 8×28 4×25 16×3 1×2 12×2 32×2 9×1 19×1 22×1 24×1 28×1 128×1
    CompleteAdd              403  (2.0%)           112        1×159 2×65 3×23 15×1 30×1 / 1×112

The RUN LENGTHS are the fidelity signal, and four of six match EXACTLY: a `Poseidon` permutation is
11 rows, a 128-bit `Scalar_challenge.endo` is 32 `EndoMul` rows, a `var_base_mul` chunk is a lone
`VarBaseMul` row followed by its `Zero`, and a 128-bit `to_field_checked` is 8 `EndoMulScalar` rows —
and the `EndoMul` COUNT is 2432 against upstream's 2465, i.e. the fold/`bullet_reduce` machinery is
here at full size. The two run-length families that differ are named below (#4, #6). Only SEVEN gate
types appear in any Mina step or wrap circuit — no lookup, no foreign-field, no range-check — and all
seven are emitted here.

⚑ The two shortfalls are NOT of the same kind. `EndoMulScalar`/`CompleteAdd`/`VarBaseMul` are short
because some widths and some fold shapes are not instantiated (cheap, mechanical). `Generic` (277 vs
6245) and `Poseidon` (1034 vs 6292) are short because two named sub-circuits are NOT BUILT: the
`ft_eval0` / `Plonk_checks.checked` scalar arithmetic, and the evaluation-absorption + app-logic
hashing. Those are the frontier, and #4/#5 below say so.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", **NOT** a Mina-valid proof; the
kimchi proof the harness produces is an **INNER** proof of a `verify_one`-shaped circuit, and wrap
is a later rung. What is reportable is INNER-KIMCHI FIDELITY of the assembled recursive verifier:
the Lean-authored five-sub-circuit assembly is accepted by a pure-Rust kimchi prover, and every
sub-circuit boundary BINDS.

## ⚑ THE σ-ONLY PROBES

Every load-bearing shared cell is also gate-read, so flipping one cannot ISOLATE σ. Each sub-circuit
boundary value is therefore ALSO materialized in a standalone `Zero` **probe row** placed into the
same class. A `Zero` gate reads nothing and no gate reads a probe row, so a probe cell is
constrained by σ and by NOTHING ELSE. The `…Unwired` variant is identical EXCEPT the probe rows are
in no class — the control that turns "rejected" into "rejected BY THE WIRE".

## NAMED SIMPLIFICATIONS (undone work, not theorems)

  1. The challenge decomposition row pins `squeeze = n₈ + 2¹²⁸·hi` but does NOT range-check `hi`;
     upstream's `lowest_128_bits ~constrain_low_bits:true` spends 16 rows + 1 generic on that
     (`util.ml:78-101`). **16 rows per challenge not assembled.**
  2. All MSM scalars are assembled at the 128-bit width (54-row `scale_fast2`). Upstream's x_hat MSM
     has 8 scalars at 255 bits (104 rows) and 1 at 10 bits; `ft_comm`'s 8 are all 255-bit. **The
     255-bit width is expressible with `msmChunks = 51` and is not in the committed shape.**
  3. The MSM base points are `basePts` (distinct on-curve Pallas points), not the previous proof's
     actual commitments; the SCALARS are the circuit's own derived challenges.
  4. The deferred rung computes `b(ζ)` and `combined_inner_product` — TWO of
     `finalize_other_proof`'s four outputs. **`ft_eval0` (`step_verifier.ml:1066-1071`) and
     `Plonk_checks.checked` (`:1131-1136`) are NOT assembled**, and with them the `scalars_env` /
     `combined_evals` blocks. That is where the `Generic` shortfall in the table above lives: 6245
     vs 327, i.e. ≈5,900 `Generic` rows of scalar arithmetic. It is the single largest remaining
     sub-circuit and it is UNDONE WORK, not a theorem of the model.
  5. No `group_map` (`step_verifier.ml:214-237`), no opt-sponge masking
     (`branch_data.proofs_verified_mask`), no `equal_g`, no dummy/`should_verify` muxing, no
     `hash_messages_for_next_step_proof`. Those, plus the app-logic `rule.main`, are most of the
     Poseidon shortfall (572 permutations upstream vs 94 here).
  6. Every challenge is derived at ONE width (128 bits, 8 `EndoMulScalar` rows). Upstream also uses
     16/32/64/192/256-bit `to_field_checked` (the 1/2/4/12/16-row runs in the table).

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate list, the coefficients, the cross-gate placement and
the composed witness grid are authored in Lean. `proof-systems` (tag 0.3.0) is the Rust PROVER that
RUNS the artifact and authors no constraint. House Law #1. No OCaml, no Node, no o1js in this path.
The `Poseidon`/`VarBaseMul`/`EndoMul`/`EndoMulScalar`/`CompleteAdd`/`Generic` constraint polynomials
are proof-systems' fixed gate semantics, transcribed read-only in `KimchiVerify`; the `#guard`s below
evaluate them against the ASSEMBLED GRID, not against intermediate Lean lists.

## Axiom hygiene / build

NO `main` (roots cleanly into `PicklesSynthesis`; the emit driver is `EmitStepMainJson.lean`).
`#guard`s reduce in the interpreter; no `sorry`/`native_decide`, no `decide` over the big grid.
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.WitnessBuilder
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.KimchiRenderPoseidon
import Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
import Dregg2.Circuit.Emit.KimchiRenderEndoMul
import Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar
import Dregg2.Circuit.Emit.KimchiRenderPublicInput
import Dregg2.Circuit.Emit.KimchiComposeStepFragment
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaCurve
import Dregg2.Circuit.Emit.PastaPoseidon

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (fAdd fMul)
open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd (completeAddWitness)
open Dregg2.Circuit.Emit.KimchiCustomGates (poseidonRowCoeffs)
open Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar (cFuncFp dFuncFp)
open Dregg2.Circuit.Emit.KimchiComposeStepFragment
  (TermData EndoBlock runVbm endoStep basePts dblA addA onCurveA jOf jDbl jAdd jNeg)
open Dregg2.Circuit.Emit.KimchiVerify
  (varBaseMulConstraints completeAddConstraints endoMulConstraints endomulScalarConstraints)
open Dregg2.Circuit.Emit.PastaCurve (jacEqM scMulM)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaPoseidon (rcsN)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — the shape. -/

/-- The assembly's size. Every field is a quantity upstream fixes; the committed instance in §10
sets them against the `verify_one` line items in the header. -/
structure StepShape where
  /-- transcript absorb blocks; each swallows TWO field elements (`rate = 2`). -/
  absorbs : Nat
  /-- squeezed scalar challenges (one permutation each). -/
  chals : Nat
  /-- `EndoMulScalar` rows per challenge; each eats 8 crumbs = 16 bits (`bits_per_row = 16`). -/
  emsRows : Nat
  /-- `var_base_mul` terms in the commitment MSM. -/
  msmTerms : Nat
  /-- 5-bit chunks per MSM term (`bits_per_chunk = 5`); `26` is upstream's 128-bit `scale_fast2`. -/
  msmChunks : Nat
  /-- `Scalar_challenge.endo` scalar multiplications in the IPA/commitment fold. -/
  ipaRounds : Nat
  /-- 4-bit `endo_mul` blocks per round (`32` is upstream's 128-bit `endo`). -/
  ipaBlocks : Nat
  /-- rounds of the deferred `b(ζ)` product (`Step_bp_vec = N16`). -/
  bRounds : Nat
  /-- evaluation columns folded by `combined_inner_product`
  (`NUM_COMMITMENTS_WITHOUT_DEGREE_BOUND = N45`, + `sg_old` padding = 47). -/
  cipEvals : Nat
  /-- the public-input width (`PRIMARY_LEN`). -/
  pubWords : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Sponge blocks = absorb blocks then squeeze blocks. -/
def StepShape.blocks (s : StepShape) : Nat := s.absorbs + s.chals
/-- Bits a challenge carries (`emsRows` rows × 8 crumbs × 2 bits). -/
def StepShape.chalBits (s : StepShape) : Nat := 16 * s.emsRows
/-- Which challenge MSM term `i` consumes (upstream re-uses ξ across the fold, so sharing is the
faithful shape and it merges the two chains' final counter cells into ONE σ class). -/
def StepShape.msmChal (s : StepShape) (i : Nat) : Nat := i % s.chals
/-- Which challenge IPA round `r` consumes. -/
def StepShape.ipaChal (s : StepShape) (r : Nat) : Nat := (s.msmTerms + r) % s.chals

/-! ## §2 — the variable space.

Public words are `external 0 .. pubWords-1` (Snarky's own numbering, which `place` reproduces). The
circuit's OWN variables start at `AUX`, so `placeChecked`'s H1 (silent public/aux absorption) cannot
fire and its H2 (an inert public word) is the real gate on the closing rung. Ids are laid out in
disjoint REGIONS whose bases are functions of the shape; §9 pins the distinct-variable count, so a
collision (which MERGES two σ classes and shrinks the count) goes red. -/

/-- The lowest `external` id the circuit allocates for itself; equals `PRIMARY_LEN` for the committed
shape, so `placeChecked`'s dead gap `pubWords ≤ i < AUX` is empty. -/
def AUX : Nat := 67

/-- Circuit variable `k`. -/
def xv (k : Nat) : PVar := .external (AUX + k)

/-- Sponge state lane `j` entering block `b` (`b = 0..blocks`). -/
def vSt (_s : StepShape) (b j : Nat) : PVar := xv (3 * b + j)
def nSt (s : StepShape) : Nat := 3 * (s.blocks + 1)

/-- Post-absorb lane `j ∈ {0,1}` of absorb block `b`. -/
def vPost (s : StepShape) (b j : Nat) : PVar := xv (nSt s + 2 * b + j)
/-- The transcript word absorbed at lane `j` of block `b`. -/
def vMsg (s : StepShape) (b j : Nat) : PVar := xv (nSt s + 2 * s.absorbs + 2 * b + j)

def baseN (s : StepShape) : Nat := nSt s + 4 * s.absorbs
/-- Challenge `c`'s `n` accumulator after `k` `EndoMulScalar` rows. `vN c emsRows` is THE CHALLENGE
VALUE — the variable three gate types share. -/
def vN (s : StepShape) (c k : Nat) : PVar := xv (baseN s + c * (s.emsRows + 1) + k)
def nN (s : StepShape) : Nat := s.chals * (s.emsRows + 1)
def baseA (s : StepShape) : Nat := baseN s + nN s
def vA (s : StepShape) (c k : Nat) : PVar := xv (baseA s + c * (s.emsRows + 1) + k)
def baseB (s : StepShape) : Nat := baseA s + nN s
def vB (s : StepShape) (c k : Nat) : PVar := xv (baseB s + c * (s.emsRows + 1) + k)
def baseHi (s : StepShape) : Nat := baseB s + nN s
/-- The high part of challenge `c`'s squeeze decomposition. -/
def vHi (s : StepShape) (c : Nat) : PVar := xv (baseHi s + c)

def baseMsm (s : StepShape) : Nat := baseHi s + s.chals
def mpx (s : StepShape) (p : Nat) : PVar := xv (baseMsm s + 2 * p)
def mpy (s : StepShape) (p : Nat) : PVar := xv (baseMsm s + 2 * p + 1)
/-- MSM term `i`'s base point. -/
def pT (s : StepShape) (i : Nat) : Nat := i * (s.msmChunks + 2)
/-- MSM term `i`'s accumulator at chunk boundary `j` (`j = 0..msmChunks`). -/
def pAcc (s : StepShape) (i j : Nat) : Nat := i * (s.msmChunks + 2) + 1 + j
/-- The running MSM sum after add `a`. -/
def pSum (s : StepShape) (a : Nat) : Nat := s.msmTerms * (s.msmChunks + 2) + a
def nMsmPts (s : StepShape) : Nat := s.msmTerms * (s.msmChunks + 2) + s.msmTerms

def baseSN (s : StepShape) : Nat := baseMsm s + 2 * nMsmPts s
/-- MSM term `i`'s scalar counter at chunk boundary `j`. At `j = msmChunks` it IS the term's
challenge variable — the cross-sub-circuit wire. -/
def vSN (s : StepShape) (i j : Nat) : PVar :=
  if j == s.msmChunks then vN s (s.msmChal i) s.emsRows else xv (baseSN s + i * s.msmChunks + j)

def baseIpa (s : StepShape) : Nat := baseSN s + s.msmTerms * s.msmChunks
def ipx (s : StepShape) (p : Nat) : PVar := xv (baseIpa s + 2 * p)
def ipy (s : StepShape) (p : Nat) : PVar := xv (baseIpa s + 2 * p + 1)
/-- IPA round `r`'s `endo_mul` base point. -/
def qT (s : StepShape) (r : Nat) : Nat := r * (s.ipaBlocks + 2)
/-- IPA round `r`'s accumulator after `e` blocks (`e = 0..ipaBlocks`). -/
def qAcc (s : StepShape) (r e : Nat) : Nat := r * (s.ipaBlocks + 2) + 1 + e
/-- The running IPA fold sum after add `a`. -/
def qSum (s : StepShape) (a : Nat) : Nat := s.ipaRounds * (s.ipaBlocks + 2) + a
def nIpaPts (s : StepShape) : Nat := s.ipaRounds * (s.ipaBlocks + 2) + s.ipaRounds

def baseQN (s : StepShape) : Nat := baseIpa s + 2 * nIpaPts s
/-- IPA round `r`'s endo scalar counter after `e` blocks; at `e = ipaBlocks` it IS the round's
challenge variable. -/
def vQN (s : StepShape) (r e : Nat) : PVar :=
  if e == s.ipaBlocks then vN s (s.ipaChal r) s.emsRows
  else xv (baseQN s + r * s.ipaBlocks + e)

def baseDef (s : StepShape) : Nat := baseQN s + s.ipaRounds * s.ipaBlocks
/-- `ζ^{2^k}` in the deferred product (`k = 0..bRounds`). -/
def vZ (s : StepShape) (k : Nat) : PVar := xv (baseDef s + k)
/-- The factor `1 + u_k · ζ^{2^{bRounds−1−k}}`. -/
def vFac (s : StepShape) (k : Nat) : PVar := xv (baseDef s + s.bRounds + 1 + k)
/-- The running product after `k` factors; `vAcc bRounds` is `b(ζ)`. -/
def vAcc (s : StepShape) (k : Nat) : PVar := xv (baseDef s + 2 * s.bRounds + 1 + k)

def baseCip (s : StepShape) : Nat := baseDef s + 3 * s.bRounds + 2
/-- The claimed evaluation of column `k` at `ζ`. -/
def vEz (s : StepShape) (k : Nat) : PVar := xv (baseCip s + k)
/-- The claimed evaluation of column `k` at `ζω`. -/
def vEw (s : StepShape) (k : Nat) : PVar := xv (baseCip s + s.cipEvals + k)
/-- `r · evₖ(ζω)`. -/
def vDk (s : StepShape) (k : Nat) : PVar := xv (baseCip s + 2 * s.cipEvals + k)
/-- `cₖ = evₖ(ζ) + r · evₖ(ζω)` — the k-th coefficient of the ξ-weighted sum. -/
def vCk (s : StepShape) (k : Nat) : PVar := xv (baseCip s + 3 * s.cipEvals + k)
/-- The Horner intermediate `accᵢ · ξ`. -/
def vTk (s : StepShape) (i : Nat) : PVar := xv (baseCip s + 4 * s.cipEvals + i)
/-- The Horner accumulator after `i` steps; `vCa cipEvals` IS `combined_inner_product`. -/
def vCa (s : StepShape) (i : Nat) : PVar := xv (baseCip s + 5 * s.cipEvals + i)
/-- One past the last circuit variable id. -/
def nVars (s : StepShape) : Nat := baseCip s + 6 * s.cipEvals + 1

/-- The challenge that plays ξ (the polynomial-combination challenge) in `combined_inner_product`. -/
def StepShape.xiChal (s : StepShape) : Nat := s.chals - 1
/-- The challenge that plays `r` (the evaluation-point combiner). -/
def StepShape.rChal (s : StepShape) : Nat := s.chals - 2

/-! ## §3 — the row-schedule primitives. -/

/-- One circuit row: gate `kind`, the `K_PERMUTS = 7` permutation-column variables (`none` = unwired
⇒ `place` self-wires), the `coeffs`, and the ADVICE `(col, value)` placements for every column no
variable owns (including permutation columns deliberately left unwired). -/
structure SRow where
  kind : KGateType
  perm : List (Option PVar)
  coeffs : List Int := []
  advice : List (Nat × Int) := []
  /-- `true` only for the standalone `Zero` σ-only probes. -/
  probe : Bool := false
  deriving Repr, Inhabited

def noPerm : List (Option PVar) := List.replicate K_PERMUTS none

/-- A σ-ONLY PROBE. -/
def probeRow (wired : Bool) (a b : PVar) : SRow :=
  { kind := .zero
  , perm := if wired then [some a, some b, none, none, none, none, none] else noPerm
  , probe := true }

/-- The DOUBLE generic gate: half 1 is `c₀w₀+c₁w₁+c₂w₂+c₃w₀w₁+c₄ = 0` over cols 0,1,2; half 2 is the
same with `coeffs[5..9]` over cols 3,4,5 (`generic.rs:283-314`, read-only — `check_single(0,0)` then
`check_single(GENERIC_COEFFS, GENERIC_REGISTERS)`; the public term applies to half 1 only). -/
def genericRow (v0 v1 v2 v3 v4 v5 : Option PVar) (c : List Int) : SRow :=
  { kind := .generic, perm := [v0, v1, v2, v3, v4, v5, none], coeffs := c }

/-- `w₂ = w₀ + w₁`. -/ def cAdd : List Int := [1, 1, -1, 0, 0]
/-- `w₂ = w₀ · w₁`. -/ def cMul : List Int := [0, 0, -1, 1, 0]
/-- `w₂ = 1 + w₀·w₁`. -/ def cMulPlus1 : List Int := [0, 0, -1, 1, 1]
/-- `w₀ = w₁`. -/ def cEq : List Int := [1, -1, 0, 0, 0]
/-- `w₀ = k`. -/ def cConst (k : Int) : List Int := [1, 0, 0, 0, -k]
/-- `w₀ = w₂ + 2^bits·w₁` — the challenge decomposition. -/
def cSplit (bits : Nat) : List Int := [1, -((2 ^ bits : Nat) : Int), -1, 0, 0]
/-- An unused generic half. -/ def cNil : List Int := [0, 0, 0, 0, 0]

/-! ## §4 — R1, the TRANSCRIPT SPONGE.

Rate 2 into lanes 0,1, capacity lane 2 (`PastaPoseidon.Ref.absorbFrom`: `n = rate` triggers `perm`
then `absorbAt _ 0`). One absorb block:

    Generic  w₀=stᵦ[0] w₁=msg₀ w₂=postᵦ[0]  |  w₃=stᵦ[1] w₄=msg₁ w₅=postᵦ[1]
    Poseidon ×11, row j coeffs `poseidonRowCoeffs j`; row 0's cols 0,1,2 WIRED to
             (postᵦ[0], postᵦ[1], stᵦ[2]) — the capacity lane passes through untouched
    Zero     cols 0,1,2 WIRED to stᵦ₊₁[0..2] = the permutation output

A squeeze block is the same without the absorb row. The `Poseidon` gate at row `j` reads the NEXT
row's cols 0,1,2 as its output state, which is why the closing `Zero` row exists and why the state
chains across the eleven rows through the gate reference rather than through σ. -/

/-- The 56 states of one permutation, `s(0) = st` through `s(55)`, ONE round per step. -/
def permStates (st : List Nat) : List (List Nat) :=
  (List.range 55).foldl
    (fun acc i =>
      acc ++ [Dregg2.Circuit.Emit.PastaPoseidon.Ref.round (rcsN.getD i []) (acc.getLastD st)])
    [st]

/-- Lane `j` of round state `k`. -/
def stLane (ss : List (List Nat)) (k j : Nat) : Int := ((ss.getD k []).getD j 0 : Int)

/-- The eleven `Poseidon` rows + the closing `Zero` row of ONE permutation. `round_to_cols` is
`STATE_ORDER = [0,2,3,4,1]` (`KimchiRenderPoseidon`, read-only): `s(5r)` at 0,1,2 · `s(5r+4)` at
3,4,5 · `s(5r+1)` at 6,7,8 · `s(5r+2)` at 9,10,11 · `s(5r+3)` at 12,13,14. -/
def permBlockRows (i0 i1 i2 o0 o1 o2 : PVar) (ss : List (List Nat)) : List SRow :=
  (List.range 11).map (fun r =>
    ({ kind := .poseidon
     , perm := if r == 0 then [some i0, some i1, some i2, none, none, none, none] else noPerm
     , coeffs := poseidonRowCoeffs r
     , advice :=
         (if r == 0 then [] else (List.range 3).map (fun j => (j, stLane ss (5 * r) j)))
         ++ (List.range 3).map (fun j => (3 + j, stLane ss (5 * r + 4) j))
         ++ (List.range 3).map (fun j => (6 + j, stLane ss (5 * r + 1) j))
         ++ (List.range 3).map (fun j => (9 + j, stLane ss (5 * r + 2) j))
         ++ (List.range 3).map (fun j => (12 + j, stLane ss (5 * r + 3) j)) } : SRow))
  ++ [ { kind := .zero, perm := [some o0, some o1, some o2, none, none, none, none] } ]

/-- The transcript word absorbed at lane `j` of block `b` — a deterministic fixture standing for a
commitment coordinate of the previous proof. -/
def msgVal (b j : Nat) : Nat := (7 + 1000003 * (2 * b + j)) % pN

/-- The sponge's evaluated trajectory: `states ! b` is the state ENTERING block `b`, `perms ! b` is
block `b`'s 56 round states. -/
structure SpongeData where
  states : List (List Nat)
  perms : List (List (List Nat))
  deriving Repr, Inhabited

def runSponge (s : StepShape) : SpongeData :=
  (List.range s.blocks).foldl
    (fun d b =>
      let pre := d.states.getLastD [0, 0, 0]
      let post :=
        if b < s.absorbs then
          [ (pre.getD 0 0 + msgVal b 0) % pN, (pre.getD 1 0 + msgVal b 1) % pN, pre.getD 2 0 ]
        else pre
      let ss := permStates post
      { states := d.states ++ [ss.getLastD post], perms := d.perms ++ [ss] })
    { states := [[0, 0, 0]], perms := [] }

/-- **R1's rows.** -/
def transcriptRows (s : StepShape) (d : SpongeData) (wired : Bool) : List SRow :=
  [ genericRow (some (vSt s 0 0)) none none (some (vSt s 0 1)) none none (cConst 0 ++ cConst 0)
  , genericRow (some (vSt s 0 2)) none none none none none (cConst 0 ++ cNil) ]
  ++ (List.range s.blocks).flatMap (fun b =>
      (if b < s.absorbs then
         [ genericRow (some (vSt s b 0)) (some (vMsg s b 0)) (some (vPost s b 0))
                      (some (vSt s b 1)) (some (vMsg s b 1)) (some (vPost s b 1))
                      (cAdd ++ cAdd) ]
       else [])
      ++ (if b < s.absorbs then
            permBlockRows (vPost s b 0) (vPost s b 1) (vSt s b 2)
                          (vSt s (b+1) 0) (vSt s (b+1) 1) (vSt s (b+1) 2) (d.perms.getD b [])
          else
            permBlockRows (vSt s b 0) (vSt s b 1) (vSt s b 2)
                          (vSt s (b+1) 0) (vSt s (b+1) 1) (vSt s (b+1) 2) (d.perms.getD b []))
      ++ (if b + 1 == s.absorbs || s.absorbs ≤ b then
            [probeRow wired (vSt s (b+1) 0) (vSt s (b+1) 1)] else []))

/-! ## §5 — R2, CHALLENGE DERIVATION (`to_field_checked`).

Squeeze `c` is state lane 0 after block `absorbs + c`. Its low `chalBits` bits are the scalar
challenge. One `EndoMulScalar` row eats 8 crumbs and folds `n ↦ 4n + xⱼ`, `a ↦ 2a + c(xⱼ)`,
`b ↦ 2b + d(xⱼ)` from `n₀=0, a₀=2, b₀=2` (`endomul_scalar.rs:227-288`, read-only via
`KimchiRenderEndoMulScalar`). Column order `[n0, n8, a0, b0, a8, b8, x₀..x₇, 0]`, so cols 0..5 are
all permutation columns and the chain hops row→row through σ; col 6 holds crumb `x₀`, unwired. -/

def chalOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat :=
  ((d.states.getD (s.absorbs + c + 1) []).getD 0 0) % 2 ^ s.chalBits
def hiOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat :=
  ((d.states.getD (s.absorbs + c + 1) []).getD 0 0) / 2 ^ s.chalBits

/-- The `8·emsRows` base-4 crumbs of a challenge, MSB-first. -/
def crumbsOf (s : StepShape) (v : Nat) : List Nat :=
  (List.range (8 * s.emsRows)).map (fun j => v / 4 ^ (8 * s.emsRows - 1 - j) % 4)

/-- The `(n,a,b)` accumulator triples at every ROW boundary (every 8 crumbs), `k = 0..emsRows`. -/
def emsAccs (s : StepShape) (v : Nat) : List (Nat × Nat × Nat) :=
  let all := (crumbsOf s v).foldl
    (fun acc x =>
      let cur := acc.getLastD (0, 2, 2)
      acc ++ [((4 * cur.1 + x) % pN, (2 * cur.2.1 + cFuncFp x) % pN,
               (2 * cur.2.2 + dFuncFp x) % pN)])
    [(0, 2, 2)]
  (List.range (s.emsRows + 1)).map (fun k => all.getD (8 * k) (0, 2, 2))

/-- **R2's rows** for challenge `c`. -/
def challengeRows (s : StepShape) (d : SpongeData) (wired : Bool) (c : Nat) : List SRow :=
  let cr := crumbsOf s (chalOf s d c)
  [ genericRow (some (vN s c 0)) none none (some (vA s c 0)) none none (cConst 0 ++ cConst 2)
  , genericRow (some (vB s c 0)) none none none none none (cConst 2 ++ cNil) ]
  ++ (List.range s.emsRows).map (fun k =>
      ({ kind := .endoMulScalar
       , perm := [ some (vN s c k), some (vN s c (k+1)), some (vA s c k), some (vB s c k)
                 , some (vA s c (k+1)), some (vB s c (k+1)), none ]
       , advice := (List.range 8).map (fun j => (6 + j, (cr.getD (8 * k + j) 0 : Int)))
                   ++ [(14, 0)] } : SRow))
  ++ [ genericRow (some (vSt s (s.absorbs + c + 1) 0)) (some (vHi s c))
                  (some (vN s c s.emsRows)) none none none (cSplit s.chalBits ++ cNil)
     , probeRow wired (vN s c s.emsRows) (vA s c s.emsRows) ]

/-! ## §6 — R3, the COMMITMENT MSM (`multiscale_known` / `ft_comm`).

`runVbm` (read-only) runs `accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, `nₖ₊₁ = 2nₖ+bₖ`, so with `n₀ = 0` the
final counter IS the scalar — and that cell is wired to the CHALLENGE variable, not a fresh one. -/

/-- The `5·msmChunks` bits of `v`, MSB-first. -/
def bitsOf (s : StepShape) (v : Nat) : List Nat :=
  (List.range (5 * s.msmChunks)).map (fun k => v / 2 ^ (5 * s.msmChunks - 1 - k) % 2)
/-- The `4·ipaBlocks` bits of `v`, MSB-first. -/
def endoBitsOf (s : StepShape) (v : Nat) : List Nat :=
  (List.range (4 * s.ipaBlocks)).map (fun k => v / 2 ^ (4 * s.ipaBlocks - 1 - k) % 2)

structure MsmData where
  terms : List TermData
  bits : List (List Nat)
  sums : List (Nat × Nat)
  addCells : List (List Nat)
  deriving Repr, Inhabited

def runMsm (s : StepShape) (d : SpongeData) : MsmData :=
  let bases := basePts (s.msmTerms + s.ipaRounds + 2)
  let bs := (List.range s.msmTerms).map (fun i => bitsOf s (chalOf s d (s.msmChal i)))
  let tds := (List.range s.msmTerms).map (fun i =>
    let T := bases.getD i (0, 0)
    runVbm T (dblA T) (bs.getD i []))
  let pts := (List.range s.msmTerms).map (fun i => (tds.getD i default).accs.getLastD (0, 0))
  let st := (List.range (s.msmTerms - 1)).foldl
    (fun (acc : List (Nat × Nat) × List (List Nat)) a =>
      let l := if a == 0 then pts.getD 0 (0, 0) else acc.1.getLastD (0, 0)
      let r := pts.getD (a + 1) (0, 0)
      let cells := completeAddWitness l.1 l.2 r.1 r.2
      (acc.1 ++ [(cells.getD 4 0, cells.getD 5 0)], acc.2 ++ [cells]))
    ([], [])
  { terms := tds, bits := bs, sums := st.1, addCells := st.2 }

/-- The two rows of MSM term `i`'s chunk `j`.
CURR `w₀=xT w₁=yT w₂=x₀ w₃=y₀ w₄=n w₅=n' w₆=Ø w₇..w₁₄ = x₁y₁..x₄y₄`;
NEXT `w₀=x₅ w₁=y₅ w₂..w₆=b₀..b₄ w₇..w₁₁=s₀..s₄`. -/
def msmChunkRows (s : StepShape) (m : MsmData) (i j : Nat) : List SRow :=
  let td := m.terms.getD i default
  let bits := m.bits.getD i []
  let ax : Nat → Int := fun k => ((td.accs.getD k (0, 0)).1 : Int)
  let ay : Nat → Int := fun k => ((td.accs.getD k (0, 0)).2 : Int)
  let bt : Nat → Int := fun k => (td.slopes.getD k 0 : Int)
  let bi : Nat → Int := fun k => (bits.getD k 0 : Int)
  [ { kind := .varBaseMul
    , perm := [ some (mpx s (pT s i)), some (mpy s (pT s i))
              , some (mpx s (pAcc s i j)), some (mpy s (pAcc s i j))
              , some (vSN s i j), some (vSN s i (j+1)), none ]
    , advice := [ (7, ax (5*j+1)), (8, ay (5*j+1)), (9, ax (5*j+2)), (10, ay (5*j+2))
                , (11, ax (5*j+3)), (12, ay (5*j+3)), (13, ax (5*j+4)), (14, ay (5*j+4)) ] }
  , { kind := .zero
    , perm := [ some (mpx s (pAcc s i (j+1))), some (mpy s (pAcc s i (j+1)))
              , none, none, none, none, none ]
    , advice := [ (2, bi (5*j)), (3, bi (5*j+1)), (4, bi (5*j+2)), (5, bi (5*j+3)), (6, bi (5*j+4))
                , (7, bt (5*j)), (8, bt (5*j+1)), (9, bt (5*j+2)), (10, bt (5*j+3))
                , (11, bt (5*j+4)) ] } ]

/-- The `a`-th `complete_add` of the MSM chain: `Rₐ = Lₐ + Pₐ₊₁`, `L₀ = P₀`, `Lₐ = Rₐ₋₁`. -/
def msmAddRow (s : StepShape) (m : MsmData) (a : Nat) : SRow :=
  let lp := if a == 0 then pAcc s 0 s.msmChunks else pSum s (a - 1)
  let rp := pAcc s (a + 1) s.msmChunks
  let c := m.addCells.getD a []
  { kind := .completeAdd
  , perm := [ some (mpx s lp), some (mpy s lp), some (mpx s rp), some (mpy s rp)
            , some (mpx s (pSum s a)), some (mpy s (pSum s a)), none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- **R3's rows.** -/
def msmRows (s : StepShape) (m : MsmData) (wired : Bool) : List SRow :=
  ((List.range s.msmChunks).flatMap (msmChunkRows s m 0))
  ++ [probeRow wired (mpx s (pAcc s 0 s.msmChunks)) (mpy s (pAcc s 0 s.msmChunks))]
  ++ (List.range (s.msmTerms - 1)).flatMap (fun a =>
       let i := a + 1
       ((List.range s.msmChunks).flatMap (msmChunkRows s m i))
       ++ [probeRow wired (mpx s (pAcc s i s.msmChunks)) (mpy s (pAcc s i s.msmChunks))]
       ++ [msmAddRow s m a]
       ++ [probeRow wired (mpx s (pSum s a)) (mpy s (pSum s a))])

/-! ## §7 — R4, the IPA / commitment FOLD (`Scalar_challenge.endo`).

`endo_mul` chains by ROW OVERLAP, not by σ: row `r+1` is simultaneously block `r`'s `Next`
(`w'₄=xs w'₅=ys w'₆=n'`) and block `r+1`'s `Curr` (`w₄=xp w₅=yp w₆=n`) — the SAME three cells. The
base point at cols 0,1 IS a σ class of `ipaBlocks` cells, and the FINAL scalar counter (on the tail
`Zero` row, col 6) is the round's CHALLENGE variable. -/

structure IpaData where
  accs : List (List (Nat × Nat))
  blks : List (List EndoBlock)
  ns : List (List Nat)
  bases : List (Nat × Nat)
  sums : List (Nat × Nat)
  addCells : List (List Nat)
  deriving Repr, Inhabited

def runIpa (s : StepShape) (d : SpongeData) : IpaData :=
  let allB := basePts (s.msmTerms + s.ipaRounds + 2)
  let bases := (List.range s.ipaRounds).map (fun r => allB.getD (s.msmTerms + r) (0, 0))
  let rounds := (List.range s.ipaRounds).map (fun r =>
    let T := bases.getD r (0, 0)
    let bits := endoBitsOf s (chalOf s d (s.ipaChal r))
    (List.range s.ipaBlocks).foldl
      (fun (st : List (Nat × Nat) × List EndoBlock × List Nat) e =>
        let cur := st.1.getLastD (0, 0)
        let b := endoStep T.1 T.2 cur.1 cur.2
          (bits.getD (4*e) 0) (bits.getD (4*e+1) 0) (bits.getD (4*e+2) 0) (bits.getD (4*e+3) 0)
        (st.1 ++ [(b.xs, b.ys)], st.2.1 ++ [b],
         st.2.2 ++ [16 * st.2.2.getLastD 0 + 8*b.b1 + 4*b.b2 + 2*b.b3 + b.b4]))
      ([dblA T], [], [0]))
  let pts := rounds.map (fun r => r.1.getLastD (0, 0))
  let st := (List.range (s.ipaRounds - 1)).foldl
    (fun (acc : List (Nat × Nat) × List (List Nat)) a =>
      let l := if a == 0 then pts.getD 0 (0, 0) else acc.1.getLastD (0, 0)
      let r := pts.getD (a + 1) (0, 0)
      let cells := completeAddWitness l.1 l.2 r.1 r.2
      (acc.1 ++ [(cells.getD 4 0, cells.getD 5 0)], acc.2 ++ [cells]))
    ([], [])
  { accs := rounds.map (·.1), blks := rounds.map (·.2.1), ns := rounds.map (·.2.2)
  , bases := bases, sums := st.1, addCells := st.2 }

def ipaRoundRows (s : StepShape) (v : IpaData) (r : Nat) : List SRow :=
  (List.range s.ipaBlocks).map (fun e =>
    let b := (v.blks.getD r []).getD e default
    ({ kind := .endoMul
     , perm := [ some (ipx s (qT s r)), some (ipy s (qT s r)), none, none
               , some (ipx s (qAcc s r e)), some (ipy s (qAcc s r e)), some (vQN s r e) ]
     , advice := [ (2, (b.inv : Int)), (3, 0), (7, (b.xr : Int)), (8, (b.yr : Int))
                 , (9, (b.s1 : Int)), (10, (b.s3 : Int)), (11, (b.b1 : Int)), (12, (b.b2 : Int))
                 , (13, (b.b3 : Int)), (14, (b.b4 : Int)) ] } : SRow))
  ++ [ { kind := .zero
       , perm := [ none, none, none, none, some (ipx s (qAcc s r s.ipaBlocks))
                 , some (ipy s (qAcc s r s.ipaBlocks)), some (vQN s r s.ipaBlocks) ] } ]

def ipaAddRow (s : StepShape) (v : IpaData) (a : Nat) : SRow :=
  let lp := if a == 0 then qAcc s 0 s.ipaBlocks else qSum s (a - 1)
  let rp := qAcc s (a + 1) s.ipaBlocks
  let c := v.addCells.getD a []
  { kind := .completeAdd
  , perm := [ some (ipx s lp), some (ipy s lp), some (ipx s rp), some (ipy s rp)
            , some (ipx s (qSum s a)), some (ipy s (qSum s a)), none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- **R4's rows.** -/
def ipaRows (s : StepShape) (v : IpaData) (wired : Bool) : List SRow :=
  ipaRoundRows s v 0
  ++ [probeRow wired (ipx s (qAcc s 0 s.ipaBlocks)) (ipy s (qAcc s 0 s.ipaBlocks))]
  ++ (List.range (s.ipaRounds - 1)).flatMap (fun a =>
       let r := a + 1
       ipaRoundRows s v r
       ++ [probeRow wired (ipx s (qAcc s r s.ipaBlocks)) (ipy s (qAcc s r s.ipaBlocks))]
       ++ [ipaAddRow s v a]
       ++ [probeRow wired (ipx s (qSum s a)) (ipy s (qSum s a))])

/-! ## §8 — R5, the DEFERRED `b(ζ)` and the CLOSING public ties.

`b(ζ) = ∏_k (1 + u_k · ζ^{2^{bRounds−1−k}})` — `Wrap.challenge_polynomial` (`wrap.ml:15-17`), the
product `KimchiVerify.bEvalSq` folds. `ζ` is challenge 0 and `u_k` is challenge `k+1`, so the
deferred rung READS R2's outputs rather than being a private arithmetic island. -/

structure DefData where
  zs : List Nat
  facs : List Nat
  accs : List Nat
  /-- the claimed evaluations at ζ and ζω (the `cipEvals` poly columns). -/
  ez : List Nat
  ew : List Nat
  dk : List Nat
  ck : List Nat
  tk : List Nat
  ca : List Nat
  deriving Repr, Inhabited

/-- Claimed evaluation of column `k` at point `pt ∈ {0,1}` — a deterministic fixture standing for a
column of the previous proof's `PointEvaluations`. -/
def evVal (k pt : Nat) : Nat := (11 + 2000003 * (2 * k + pt) + 7 * k * k) % pN

def runDef (s : StepShape) (d : SpongeData) : DefData :=
  let zs := (List.range s.bRounds).foldl
    (fun acc _ => let x := acc.getLastD 0; acc ++ [fMul x x]) [chalOf s d 0]
  let st := (List.range s.bRounds).foldl
    (fun (acc : List Nat × List Nat) k =>
      let f := fAdd 1 (fMul (chalOf s d (k + 1)) (zs.getD (s.bRounds - 1 - k) 0))
      (acc.1 ++ [f], acc.2 ++ [fMul (acc.2.getLastD 1) f]))
    ([], [1])
  let xi := chalOf s d s.xiChal
  let rr := chalOf s d s.rChal
  let ez := (List.range s.cipEvals).map (fun k => evVal k 0)
  let ew := (List.range s.cipEvals).map (fun k => evVal k 1)
  let dk := (List.range s.cipEvals).map (fun k => fMul rr (ew.getD k 0))
  let ck := (List.range s.cipEvals).map (fun k => fAdd (ez.getD k 0) (dk.getD k 0))
  -- Horner from the TOP: `accᵢ₊₁ = accᵢ·ξ + c_{n−1−i}` closes to `Σ_k ξ^k · c_k`, which IS
  -- `KimchiVerify.combinedInnerProduct` (pinned in §12).
  let hz := (List.range s.cipEvals).foldl
    (fun (acc : List Nat × List Nat) i =>
      let t := fMul (acc.2.getLastD 0) xi
      (acc.1 ++ [t], acc.2 ++ [fAdd t (ck.getD (s.cipEvals - 1 - i) 0)]))
    ([], [0])
  { zs := zs, facs := st.1, accs := st.2
  , ez := ez, ew := ew, dk := dk, ck := ck, tk := hz.1, ca := hz.2 }

/-- **R5a's rows.** -/
def deferredRows (s : StepShape) (wired : Bool) : List SRow :=
  [ genericRow (some (vAcc s 0)) none none none none none (cConst 1 ++ cNil)
  , genericRow (some (vZ s 0)) (some (vN s 0 s.emsRows)) none none none none (cEq ++ cNil) ]
  ++ (List.range s.bRounds).map (fun k =>
      genericRow (some (vZ s k)) (some (vZ s k)) (some (vZ s (k+1))) none none none (cMul ++ cNil))
  ++ (List.range s.bRounds).map (fun k =>
      genericRow (some (vN s (k+1) s.emsRows)) (some (vZ s (s.bRounds - 1 - k))) (some (vFac s k))
                 (some (vAcc s k)) (some (vFac s k)) (some (vAcc s (k+1))) (cMulPlus1 ++ cMul))
  ++ [ probeRow wired (vAcc s s.bRounds) (vZ s s.bRounds) ]

/-- **R5a', `combined_inner_product`** — `Common.combined_evaluation` (`common.ml:258-…`), the
`2 × cipEvals` `mul_and_add`s. `cip = Σ_k ξ^k · (evₖ(ζ) + r · evₖ(ζω))`, assembled as a Horner fold
from the top over `Generic` rows, two per evaluation column:

    A(k)  half1  w₀=r      w₁=evₖ(ζω)  w₂=dₖ      dₖ = r · evₖ(ζω)
          half2  w₃=evₖ(ζ) w₄=dₖ       w₅=cₖ      cₖ = evₖ(ζ) + dₖ
    B(i)  half1  w₀=accᵢ   w₁=ξ        w₂=tᵢ      tᵢ = accᵢ · ξ
          half2  w₃=tᵢ     w₄=c_{n−1−i} w₅=accᵢ₊₁ accᵢ₊₁ = tᵢ + c_{n−1−i}

ξ and `r` are CHALLENGE variables, so this rung reads R2's outputs through σ as well. -/
def cipRows (s : StepShape) (wired : Bool) : List SRow :=
  [ genericRow (some (vCa s 0)) none none none none none (cConst 0 ++ cNil) ]
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [ genericRow (some (vN s s.rChal s.emsRows)) (some (vEw s k)) (some (vDk s k))
                   (some (vEz s k)) (some (vDk s k)) (some (vCk s k)) (cMul ++ cAdd) ])
  ++ (List.range s.cipEvals).flatMap (fun i =>
      [ genericRow (some (vCa s i)) (some (vN s s.xiChal s.emsRows)) (some (vTk s i))
                   (some (vTk s i)) (some (vCk s (s.cipEvals - 1 - i))) (some (vCa s (i+1)))
                   (cMul ++ cAdd) ])
  ++ [ probeRow wired (vCa s s.cipEvals) (vCk s 0) ]

/-- The circuit variables EXPOSED as the public output — `pubWords` of them, drawn from every
sub-circuit so a public tie reaches all five. -/
def exposedVars (s : StepShape) : List PVar :=
  ([ vAcc s s.bRounds, vCa s s.cipEvals, vZ s s.bRounds
   , vSt s s.blocks 0, vSt s s.blocks 1, vSt s s.blocks 2
   , mpx s (pSum s (s.msmTerms - 2)), mpy s (pSum s (s.msmTerms - 2))
   , ipx s (qSum s (s.ipaRounds - 2)), ipy s (qSum s (s.ipaRounds - 2)) ]
   ++ (List.range s.chals).map (fun c => vN s c s.emsRows)
   ++ (List.range (s.bRounds + 1)).map (fun k => vAcc s k)
   ++ (List.range (s.bRounds + 1)).map (fun k => vZ s k)
   ++ (List.range (s.blocks + 1)).map (fun b => vSt s b 0)).take s.pubWords

/-- **R5b's rows**: every public word tied to a computed circuit variable, two per `Generic` row
(`w₀ = w₁` in each half). Every one of `pubWords` public words is READ here — exactly what
`placeChecked`'s `inertPublicWord` refusal demands. -/
def closingRows (s : StepShape) : List SRow :=
  let ev := exposedVars s
  (List.range ((s.pubWords + 1) / 2)).map (fun r =>
    if 2 * r + 1 < s.pubWords then
      genericRow (some (ev.getD (2*r) (xv 0))) (some (.external (2*r))) none
                 (some (ev.getD (2*r+1) (xv 0))) (some (.external (2*r+1))) none (cEq ++ cEq)
    else
      genericRow (some (ev.getD (2*r) (xv 0))) (some (.external (2*r))) none none none none
                 (cEq ++ cNil))

/-! ## §9 — the whole assembly: rows, environment, placement, witness. -/

/-- Everything the schedule and the environment read, evaluated ONCE. -/
structure StepData where
  sh : StepShape
  sp : SpongeData
  msm : MsmData
  ipa : IpaData
  df : DefData
  deriving Repr, Inhabited

def mkStep (s : StepShape) : StepData :=
  let sp := runSponge s
  { sh := s, sp := sp, msm := runMsm s sp, ipa := runIpa s sp, df := runDef s sp }

/-- **THE ROW SCHEDULE**, in the order `verify_one` runs it. -/
def stepRows (t : StepData) (wired : Bool) : List SRow :=
  let s := t.sh
  transcriptRows s t.sp wired
  ++ (List.range s.chals).flatMap (challengeRows s t.sp wired)
  ++ msmRows s t.msm wired
  ++ ipaRows s t.ipa wired
  ++ deferredRows s wired
  ++ cipRows s wired
  ++ closingRows s

/-- The CIRCUIT's variable → value assignment (public words are added by `stepEnv`). -/
def circuitEnv (t : StepData) : VarEnv :=
  let s := t.sh
  (List.range (s.blocks + 1)).flatMap (fun b =>
    let st := t.sp.states.getD b []
    (List.range 3).map (fun j => (vSt s b j, (st.getD j 0 : Int))))
  ++ (List.range s.absorbs).flatMap (fun b =>
      let pre := t.sp.states.getD b []
      (List.range 2).map (fun j =>
        (vPost s b j, (((pre.getD j 0 + msgVal b j) % pN : Nat) : Int))))
  ++ (List.range s.absorbs).flatMap (fun b =>
      (List.range 2).map (fun j => (vMsg s b j, (msgVal b j : Int))))
  ++ (List.range s.chals).flatMap (fun c =>
      let accs := emsAccs s (chalOf s t.sp c)
      (List.range (s.emsRows + 1)).flatMap (fun k =>
        let a := accs.getD k (0, 2, 2)
        [ (vN s c k, (a.1 : Int)), (vA s c k, (a.2.1 : Int)), (vB s c k, (a.2.2 : Int)) ])
      ++ [ (vHi s c, (hiOf s t.sp c : Int)) ])
  ++ (List.range s.msmTerms).flatMap (fun i =>
      let td := t.msm.terms.getD i default
      [ (mpx s (pT s i), (td.T.1 : Int)), (mpy s (pT s i), (td.T.2 : Int)) ]
      ++ (List.range (s.msmChunks + 1)).flatMap (fun j =>
          let a := td.accs.getD (5 * j) (0, 0)
          [ (mpx s (pAcc s i j), (a.1 : Int)), (mpy s (pAcc s i j), (a.2 : Int)) ])
      ++ (List.range s.msmChunks).map (fun j => (vSN s i j, (td.ns.getD (5 * j) 0 : Int))))
  ++ (List.range (s.msmTerms - 1)).flatMap (fun a =>
      let p := t.msm.sums.getD a (0, 0)
      [ (mpx s (pSum s a), (p.1 : Int)), (mpy s (pSum s a), (p.2 : Int)) ])
  ++ (List.range s.ipaRounds).flatMap (fun r =>
      let T := t.ipa.bases.getD r (0, 0)
      [ (ipx s (qT s r), (T.1 : Int)), (ipy s (qT s r), (T.2 : Int)) ]
      ++ (List.range (s.ipaBlocks + 1)).flatMap (fun e =>
          let a := (t.ipa.accs.getD r []).getD e (0, 0)
          [ (ipx s (qAcc s r e), (a.1 : Int)), (ipy s (qAcc s r e), (a.2 : Int)) ])
      ++ (List.range s.ipaBlocks).map (fun e =>
          (vQN s r e, ((t.ipa.ns.getD r []).getD e 0 : Int))))
  ++ (List.range (s.ipaRounds - 1)).flatMap (fun a =>
      let p := t.ipa.sums.getD a (0, 0)
      [ (ipx s (qSum s a), (p.1 : Int)), (ipy s (qSum s a), (p.2 : Int)) ])
  ++ (List.range (s.bRounds + 1)).map (fun k => (vZ s k, (t.df.zs.getD k 0 : Int)))
  ++ (List.range s.bRounds).map (fun k => (vFac s k, (t.df.facs.getD k 0 : Int)))
  ++ (List.range (s.bRounds + 1)).map (fun k => (vAcc s k, (t.df.accs.getD k 0 : Int)))
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [ (vEz s k, (t.df.ez.getD k 0 : Int)), (vEw s k, (t.df.ew.getD k 0 : Int))
      , (vDk s k, (t.df.dk.getD k 0 : Int)), (vCk s k, (t.df.ck.getD k 0 : Int))
      , (vTk s k, (t.df.tk.getD k 0 : Int)) ])
  ++ (List.range (s.cipEvals + 1)).map (fun i => (vCa s i, (t.df.ca.getD i 0 : Int)))

/-- The full environment: the circuit's variables, then the `pubWords` public words, whose values
are READ OUT of the circuit env at the exposed variables — so a public word and the variable the
closing row ties it to hold ONE value by construction, exactly as a copy class does. -/
def stepEnv (t : StepData) : VarEnv :=
  let ce := circuitEnv t
  let ix := envIndex ce
  ce ++ (List.range t.sh.pubWords).map (fun i =>
    ((.external i : PVar), envLookupAt ix ((exposedVars t.sh).getD i (xv 0))))

/-- The public vector the verifier is handed, in order. -/
def stepPublic (t : StepData) : List Int :=
  let ix := envIndex (circuitEnv t)
  (List.range t.sh.pubWords).map (fun i =>
    envLookupAt ix ((exposedVars t.sh).getD i (xv 0)))

def stepGates (rows : List SRow) : List PGate :=
  rows.map (fun r => { kind := r.kind, permVars := r.perm, coeffs := r.coeffs })

/-- The composed 15 × `(pubSize + nRows)` witness grid. The `pubSize` public rows carry the public
word at col 0 (`prover.rs:270`: the prover's public vector IS witness column 0, rows `0..n`); the
circuit rows start at `pubSize` (`compute_witness`, `transaction.rs:3854-3872`). Built with the
ROW-INDEXED front ends (`envIndex`/`gateVarWitnessAt`), which is what keeps the assembly linear
rather than quadratic in the row count. -/
def stepWitness (t : StepData) (pubSize : Nat) (rows : List SRow) : List (List Int) :=
  let ix := envIndex (stepEnv t)
  let n := rows.length
  compose 15 (pubSize + n)
    (((List.range pubSize).map (fun i => ((⟨i, 0⟩ : Cell), envLookupAt ix (.external i))))
     :: (rows.zip (List.range n)).map (fun ri =>
          gateVarWitnessAt ix (pubSize + ri.2)
            { kind := ri.1.kind, permVars := ri.1.perm, coeffs := ri.1.coeffs }
          ++ ri.1.advice.map (fun cv => ((⟨pubSize + ri.2, cv.1⟩ : Cell), cv.2))))

/-- Read circuit row `r` out of the ASSEMBLED column-major grid (all 15 columns). -/
def gridRow (w : List (List Int)) (r : Nat) : List Nat :=
  (List.range 15).map (fun c => (gridAt w ⟨r, c⟩).toNat)

/-- **THE FAIL-CLOSED PLACEMENT.** `placeChecked`, never `place`: `auxOverlapsPublic` /
`referenceInGap` / `inertPublicWord` REFUSE rather than reinterpret. A refusal yields the empty
placement, which every downstream `#guard` then fails loudly. -/
def placedOf (pubSize : Nat) (gs : List PGate) : List PlacedGate :=
  match placeChecked ⟨pubSize, AUX⟩ gs with
  | .ok p => p
  | .error _ => []

/-- Did the placement refuse, and why. -/
def refusalOf (pubSize : Nat) (gs : List PGate) : Option PlaceRefusal :=
  match placeChecked ⟨pubSize, AUX⟩ gs with
  | .ok _ => none
  | .error e => some e

/-! ## §10 — the RUNGS.

`Rung` names how far up the assembly a circuit reaches. Rungs 1–4 are placed at `pubSize = 0`
(their public output is not yet tied); rung 5 IS the closing rung and is placed at `pubSize =
pubWords` through `placeChecked`. Each rung is a superset of the one below, so a regression cannot
hide behind a smaller circuit. -/

inductive Rung where
  | transcript | challenges | msm | ipa | full
  deriving Repr, DecidableEq, Inhabited

def Rung.tag : Rung → String
  | .transcript => "r1_transcript" | .challenges => "r2_challenges" | .msm => "r3_msm"
  | .ipa => "r4_ipa" | .full => "r5_full"

/-- Rung `k`'s rows. -/
def rungRows (t : StepData) (k : Rung) (wired : Bool) : List SRow :=
  let s := t.sh
  let a := transcriptRows s t.sp wired
  let b := (List.range s.chals).flatMap (challengeRows s t.sp wired)
  let c := msmRows s t.msm wired
  let d := ipaRows s t.ipa wired
  match k with
  | .transcript => a
  | .challenges => a ++ b
  | .msm => a ++ b ++ c
  | .ipa => a ++ b ++ c ++ d
  | .full => a ++ b ++ c ++ d ++ deferredRows s wired ++ closingRows s

/-- Rung `k`'s public-input size: 0 below the closing rung, `pubWords` at it. -/
def rungPub (s : StepShape) : Rung → Nat
  | .full => s.pubWords
  | _ => 0

/-- Rung `k`'s absolute probe rows, in schedule order. -/
def rungProbeRows (t : StepData) (k : Rung) : List Nat :=
  let rows := rungRows t k true
  let p := rungPub t.sh k
  ((rows.zip (List.range rows.length)).filter (fun ri => ri.1.probe)).map (fun ri => p + ri.2)

/-! ### The renderer.

Same JSON the pickles harnesses parse, plus two fields the earlier ones did not need:
`public_input` (a `pubSize > 0` circuit is not runnable without it — `kimchi/src/verifier.rs:816`
rejects a length mismatch outright, so omitting it would force the harness to re-derive the public
input in Rust, which is witness authoring) and `probe_rows`, the absolute rows of the σ-only probes.
`probe_rows` travels WITH the circuit so the harness aims its tampers at what the Lean schedule
actually emitted rather than at a hand-copied constant that a schedule drift would silently
invalidate. -/

private def q (s : String) : String := "\"" ++ s ++ "\""
private def renderCell (c : Cell) : String := "[" ++ toString c.row ++ "," ++ toString c.col ++ "]"
private def renderWires (ws : List Cell) : String :=
  "[" ++ String.intercalate "," (ws.map renderCell) ++ "]"
private def renderIntList (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map (fun i => q (toString i))) ++ "]"
private def renderNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
private def renderGate (g : PlacedGate) : String :=
  "{" ++ q "typ" ++ ":" ++ toString g.kind.ordinal ++ ","
       ++ q "wires" ++ ":" ++ renderWires g.wires ++ ","
       ++ q "coeffs" ++ ":" ++ renderIntList g.coeffs ++ "}"

/-- A provable circuit with its public vector and its probe rows. -/
def renderStepCircuit (name : String) (pubSize numRows : Nat) (gs : List PlacedGate)
    (w : List (List Int)) (pub : List Int) (probes : List Nat) : String :=
  "{" ++ q "name" ++ ":" ++ q name ++ ","
       ++ q "public_input_size" ++ ":" ++ toString pubSize ++ ","
       ++ q "public_input" ++ ":" ++ renderIntList pub ++ ","
       ++ q "num_rows" ++ ":" ++ toString numRows ++ ","
       ++ q "probe_rows" ++ ":" ++ renderNatList probes ++ ","
       ++ q "gates" ++ ":[" ++ String.intercalate "," (gs.map renderGate) ++ "],"
       ++ q "witness" ++ ":[" ++ String.intercalate "," (w.map renderIntList) ++ "]}"

/-- Rung `k`'s emitted JSON (WIRED or UNWIRED control). -/
def rungJson (t : StepData) (k : Rung) (wired : Bool) (name : String) : String :=
  let rows := rungRows t k wired
  let p := rungPub t.sh k
  renderStepCircuit name p (p + rows.length)
    (placedOf p (stepGates rows)) (stepWitness t p rows)
    (if p == 0 then [] else stepPublic t) (rungProbeRows t k)

/-! ## §11 — the committed shape, sized against the `verify_one` line items. -/

/-- **THE COMMITTED SHAPE.** Sized from the header's `verify_one` cost table:
`absorbs = 26` covers the 52 field elements of `sg_old`(4) + `x_hat`(2) + `w_comm`(30) + `z_comm`(2)
+ `t_comm`(14); `chals = 23` is β, γ, α, ζ, ξ, r, u, c + the 15 `bullet_reduce` squeezes;
`msmTerms = 38` × `msmChunks = 26` (128-bit `scale_fast2`) = 1976 rows ≈ the x_hat MSM's measured
1972; `ipaRounds = 76` × `ipaBlocks = 32` covers the 46 fold `endo`s + the 30 `bullet_reduce`
`endo`/`endo_inv`s; `bRounds = 16` is `Step_bp_vec = N16`; `pubWords = 67` is Step's `PRIMARY_LEN`. -/
def shapeStep : StepShape :=
  { absorbs := 71, chals := 23, emsRows := 8
  , msmTerms := 38, msmChunks := 26
  , ipaRounds := 76, ipaBlocks := 32
  , bRounds := 16, cipEvals := 47, pubWords := 67 }

/-- A small shape for the fast in-CI pins (the committed one is emitted by the driver). -/
def shapeSmoke : StepShape :=
  { absorbs := 2, chals := 5, emsRows := 8
  , msmTerms := 3, msmChunks := 26
  , ipaRounds := 3, ipaBlocks := 32
  , bRounds := 3, cipEvals := 7, pubWords := 12 }

/-! ## §12 — the in-CI pins, on the SMOKE instance (`#guard`, interpreter-reduced).

The committed step-scale instance is emitted and PROVED by the harness; these pins run in `lake
build` and cover every structural property the harness cannot see. Nullary `def`s so the interpreter
evaluates the chains ONCE. -/

def tS : StepData := mkStep shapeSmoke
def rowsS : List SRow := rungRows tS .full true
def rowsUS : List SRow := rungRows tS .full false
def nRowsS : Nat := rowsS.length
def pubS : Nat := shapeSmoke.pubWords
def gatesS : List PGate := stepGates rowsS
def gatesUS : List PGate := stepGates rowsUS
def placedS : List PlacedGate := placedOf pubS gatesS
def placedUS : List PlacedGate := placedOf pubS gatesUS
def posS : List (PVar × Cell) := circuitPositions pubS gatesS
def posUS : List (PVar × Cell) := circuitPositions pubS gatesUS
def pairsS : List (Cell × Cell) := permPairs posS
def pairsUS : List (Cell × Cell) := permPairs posUS
def witS : List (List Int) := stepWitness tS pubS rowsS
def totalRowsS : Nat := pubS + nRowsS

-- ── Structure ────────────────────────────────────────────────────────────────────────────────
#guard shapeSmoke.blocks == shapeSmoke.absorbs + shapeSmoke.chals
#guard placedS.length == totalRowsS
#guard placedUS.length == totalRowsS
#guard (placedS.map (fun g => g.wires.length)).all (· == 7)
#guard witS.length == 15
#guard (witS.map (·.length)).all (· == totalRowsS)

-- ⚑ THE PLACEMENT DID NOT REFUSE. `placeChecked` is the fail-closed door: `auxOverlapsPublic`
-- cannot fire (AUX = 67 ≥ pubWords), `referenceInGap` cannot (every circuit id is ≥ AUX), and
-- `inertPublicWord` is the LIVE gate — it fires unless the closing rows read all `pubWords` words.
#guard refusalOf pubS gatesS == none
#guard inertPublicWords pubS gatesS == []
-- …and it CAN refuse: declare a wider public input than the closing rows read and word `pubWords`
-- is reported inert rather than silently pinned (the `PRIMARY_LEN` 67-vs-40 shape, in miniature).
#guard match refusalOf (pubS + 3) gatesS with
       | some (.inertPublicWord i) => i == pubS | _ => false

-- ⚑ SEVEN GATE TYPES in one circuit — the census. Eleven `Poseidon` rows per sponge block, which
-- is upstream's own run length (`sponge_inputs.ml:47-64` / `plonk_constraint_system.ml:1450-1530`,
-- and MEASURED in Mina's `step-zkapp-proved` blob: every `Poseidon` run there is exactly 11).
#guard (placedS.filter (fun g => g.kind == KGateType.poseidon)).length == 11 * shapeSmoke.blocks
#guard (placedS.filter (fun g => g.kind == KGateType.endoMulScalar)).length
        == shapeSmoke.chals * shapeSmoke.emsRows
#guard (placedS.filter (fun g => g.kind == KGateType.varBaseMul)).length
        == shapeSmoke.msmTerms * shapeSmoke.msmChunks
#guard (placedS.filter (fun g => g.kind == KGateType.endoMul)).length
        == shapeSmoke.ipaRounds * shapeSmoke.ipaBlocks
#guard (placedS.filter (fun g => g.kind == KGateType.completeAdd)).length
        == (shapeSmoke.msmTerms - 1) + (shapeSmoke.ipaRounds - 1)
-- Generic = the pubWords public rows `place` emits + the circuit's own generic rows.
#guard (placedS.filter (fun g => g.kind == KGateType.generic)).length ≥ pubS

-- The public rows ARE kimchi's `Pub` gates (`constraints.rs:420-423` errors `IncorrectPublic`
-- on anything else; `generic.rs:297-304` then reads the row as `w₀[r] − pᵣ = 0`).
#guard ((placedS.take pubS).map (fun g => (g.kind.ordinal, g.coeffs))).all
        (· == (1, ([1, 0, 0, 0, 0] : List Int)))

-- ── The copy-permutation, ON THE EMITTED OBJECT ───────────────────────────────────────────────
-- ⚑ σ IS A PERMUTATION of all `7 · totalRows` cells, WITH `pubSize > 0`.
#guard sortCells (allWires placedS) == sortCells (allCells totalRowsS)
#guard sortCells (allWires placedUS) == sortCells (allCells totalRowsS)

-- ⚑ THE COMPOSED GRID SATISFIES σ, against `place`'s ACTUAL permutation.
#guard pairsS.all (fun pr => gridAt witS pr.1 == gridAt witS pr.2)
#guard pairsUS.all (fun pr => gridAt witS pr.1 == gridAt witS pr.2)

-- ⚑ THE PUBLIC VECTOR IS witness column 0's prefix (`prover.rs:270`) — a fixture that got this
-- wrong would force the harness to re-derive the public input in Rust, i.e. author the witness.
#guard (witS.headD []).take pubS == stepPublic tS
#guard (stepPublic tS).length == pubS
#guard (exposedVars shapeSmoke).length == pubS
-- …and the exposed variables are DISTINCT, so 67 public words tie 67 different circuit values.
#guard ((exposedVars shapeSmoke).map varIx).dedup.length == pubS

-- ── The CROSS-SUB-CIRCUIT WIRES (the claim this file exists to make) ───────────────────────────
-- ⚑ ONE VARIABLE, THREE GATE TYPES. Challenge `c`'s value cell is in the `EndoMulScalar` chain
-- (col 1 of its last row), in the `Generic` decomposition row, and — for the terms/rounds that
-- consume it — in a `VarBaseMul` row (col 5) and an `EndoMul` tail `Zero` row (col 6). So the σ
-- class of `vN c emsRows` is genuinely cross-gate and cross-sub-circuit.
#guard (classCells posS (vN shapeSmoke 0 shapeSmoke.emsRows)).length ≥ 4
#guard (classCells posS (vN shapeSmoke 1 shapeSmoke.emsRows)).length ≥ 4
-- ⚑ THE SPONGE STATE CROSSES BLOCKS. Block b's output lane 0 is read by block b+1's absorb row
-- (or its permutation row 0) — a cross-row class no `KimchiRenderPoseidon` rung had.
#guard (classCells posS (vSt shapeSmoke 1 0)).length ≥ 2
#guard (classCells posS (vSt shapeSmoke 2 2)).length ≥ 2
-- ⚑ THE ENDO ROW-OVERLAP: a mid-chain endo accumulator is ONE cell (block e's `Next` col 4 IS
-- block e+1's `Curr` col 4), so σ self-wires it and two `EndoMul` gates read that one cell.
#guard (classCells posS (ipx shapeSmoke (qAcc shapeSmoke 0 3))).length == 1
-- Cross-ROW σ pairs — the cross-gate wiring count; removing the probes costs some of them.
#guard (pairsS.filter (fun pr => pr.1.row != pr.2.row)).length
        > (pairsUS.filter (fun pr => pr.1.row != pr.2.row)).length

-- ⚑ THE WIRED/UNWIRED DIFFERENCE IS EXACTLY THE PROBES: every probe cell is in a σ cycle in the
-- WIRED circuit and self-wired (in NO cycle) in the UNWIRED one.
#guard (rungProbeRows tS .full).all (fun r => permLookup pairsS ⟨r, 0⟩ != (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .full).all (fun r => permLookup pairsS ⟨r, 1⟩ != (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .full).all (fun r => permLookup pairsUS ⟨r, 0⟩ == (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .full).all (fun r => permLookup pairsUS ⟨r, 1⟩ == (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .full).length ≥ 10

-- ⚑ IT CAN GO RED. Desync ONE mid-chain probe cell and the σ check FAILS, so the `= true` above
-- is a gate rather than a tautology. (`toGrid` is first-wins, so the prepended override lands.)
#guard
  (let probe := (rungProbeRows tS .full).getD ((rungProbeRows tS .full).length / 2) 0
   let ix := envIndex (stepEnv tS)
   let broken := Dregg2.Circuit.Emit.WitnessBuilder.toGrid 15 totalRowsS
     (((⟨probe, 0⟩ : Cell), (7 : Int))
      :: ((List.range pubS).map (fun i => ((⟨i, 0⟩ : Cell), envLookupAt ix (.external i))))
      ++ ((rowsS.zip (List.range nRowsS)).flatMap (fun ri =>
           gateVarWitnessAt ix (pubS + ri.2)
             { kind := ri.1.kind, permVars := ri.1.perm, coeffs := ri.1.coeffs }
           ++ ri.1.advice.map (fun cv => ((⟨pubS + ri.2, cv.1⟩ : Cell), cv.2)))))
   (pairsS.all (fun pr => gridAt broken pr.1 == gridAt broken pr.2)) == false)

-- ── The GATE constraints, evaluated ON THE ASSEMBLED GRID ─────────────────────────────────────
-- ⚑ NON-VACUITY IN LEAN, per gate type: every emitted row satisfies the SAME constraint bodies the
-- real proof uses (`KimchiVerify`, read-only), over `ZMod pN`, read out of the COMPOSED grid. A
-- placement bug that never reaches the grid cannot hide from these.
def rowKindAt (r : Nat) : KGateType := (rowsS.getD (r - pubS) default).kind

#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.varBaseMul)).all
  (fun i => (varBaseMulConstraints (R := ZMod pN)
      ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))
      ((gridRow witS (pubS + i + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.completeAdd)).all
  (fun i => (completeAddConstraints (R := ZMod pN)
      ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.endoMul)).all
  (fun i => (endoMulConstraints (R := ZMod pN) (KimchiRenderEndoMul.endo : ZMod pN)
      ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))
      ((gridRow witS (pubS + i + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

-- ── The SEMANTICS ─────────────────────────────────────────────────────────────────────────────
-- ⚑ THE SPONGE IS THE REAL SPONGE. Each block's output equals `PastaPoseidon.Ref.perm` of its
-- input — the same reference whose `Ref.hash` reproduces the o1js `Poseidon.hash` gold KATs.
#guard (List.range shapeSmoke.blocks).all (fun b =>
  let pre := tS.sp.states.getD b []
  let post := if b < shapeSmoke.absorbs then
      [ (pre.getD 0 0 + msgVal b 0) % pN, (pre.getD 1 0 + msgVal b 1) % pN, pre.getD 2 0 ]
    else pre
  tS.sp.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)

-- ⚑ THE CHALLENGE CHAIN RECONSTRUCTS ITS CHALLENGE: the `EndoMulScalar` folds' final `n₈` IS the
-- low-128-bit squeeze, and the decomposition row's identity `squeeze = n₈ + 2¹²⁸·hi` holds.
#guard (List.range shapeSmoke.chals).all (fun c =>
  ((emsAccs shapeSmoke (chalOf shapeSmoke tS.sp c)).getLastD (0,2,2)).1
    == chalOf shapeSmoke tS.sp c)
#guard (List.range shapeSmoke.chals).all (fun c =>
  (tS.sp.states.getD (shapeSmoke.absorbs + c + 1) []).getD 0 0
    == chalOf shapeSmoke tS.sp c + 2 ^ shapeSmoke.chalBits * hiOf shapeSmoke tS.sp c)
-- ⚑ …and every emitted `EndoMulScalar` ROW satisfies the gate's own eleven constraints on the
-- ASSEMBLED grid (`endomulScalarConstraints`, read-only), with the three polynomial constants.
#guard
  (let cA : ZMod pN := (KimchiRenderEndoMulScalar.cA : ZMod pN)
   let cB : ZMod pN := (KimchiRenderEndoMulScalar.cB : ZMod pN)
   let cC : ZMod pN := (KimchiRenderEndoMulScalar.cC : ZMod pN)
   ((List.range nRowsS).filter
      (fun i => (rowsS.getD i default).kind == KGateType.endoMulScalar)).all
    (fun i => (endomulScalarConstraints (R := ZMod pN) cA cB cC
        ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0))))

-- ⚑ THE MSM SCALAR IS THE CHALLENGE. Term `i`'s var_base_mul counter chain closes on the value the
-- `EndoMulScalar` chain decoded — the σ wire, checked as an arithmetic identity too.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (tS.msm.terms.getD i default).ns.getLastD 0 == chalOf shapeSmoke tS.sp (shapeSmoke.msmChal i))
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (tS.ipa.ns.getD r []).getLastD 0 == chalOf shapeSmoke tS.sp (shapeSmoke.ipaChal r))

-- ⚑ EVERY var_base_mul BIT STEP is `accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, checked with `PastaCurve`'s
-- INDEPENDENT Jacobian double/add (a different formula family from the affine `stepVbm` that
-- produced the witness), compared without inversion by `jacEqM`.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  let td := tS.msm.terms.getD i default
  let bits := tS.msm.bits.getD i []
  (List.range (5 * shapeSmoke.msmChunks)).all (fun k =>
    let a := td.accs.getD k (0, 0)
    let a' := td.accs.getD (k + 1) (0, 0)
    let q := if bits.getD k 0 == 1 then jOf td.T else jNeg (jOf td.T)
    jacEqM pN (jOf a') (jAdd (jDbl (jOf a)) q)))

-- ⚑ THE SCALAR CELL IS TIED TO THE POINT: with `acc₀ = [2]T` the chain closes to
-- `acc_final = [2^{5C} + 2n + 1]·T`, `n` the value in the last chunk's `n'` cell — checked against
-- `PastaCurve.scMulM`, an independent 255-bit double-and-add.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  let td := tS.msm.terms.getD i default
  match scMulM pN (2 ^ (5 * shapeSmoke.msmChunks) + 2 * td.ns.getLastD 0 + 1) (jOf td.T) with
  | none => false
  | some R => jacEqM pN (jOf (td.accs.getLastD (0, 0))) R)

-- ⚑ EVERY endo_mul BLOCK is `accₑ₊₁ = [2]([2]accₑ + Q₁) + Q₂` with `Qₖ = ±φ^{b}(T)` — the
-- endomorphism selection included — same independent Jacobian oracle.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  let T := tS.ipa.bases.getD r (0, 0)
  (List.range shapeSmoke.ipaBlocks).all (fun e =>
    let b := (tS.ipa.blks.getD r []).getD e default
    let a := (tS.ipa.accs.getD r []).getD e (0, 0)
    let a' := (tS.ipa.accs.getD r []).getD (e + 1) (0, 0)
    let q1r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b1 T.1, T.2)
    let q2r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b3 T.1, T.2)
    let q1 := if b.b2 == 1 then jOf q1r else jNeg (jOf q1r)
    let q2 := if b.b4 == 1 then jOf q2r else jNeg (jOf q2r)
    jacEqM pN (jOf a') (jAdd (jDbl (jAdd (jDbl (jOf a)) q1)) q2)))

-- ⚑ THE ACCUMULATOR CHAINS REALLY SUM THE TERMS (Jacobian fold of all addends).
#guard
  (let pts := (List.range shapeSmoke.msmTerms).map (fun i =>
        (tS.msm.terms.getD i default).accs.getLastD (0, 0))
   let tot := (pts.drop 1).foldl (fun acc p => jAdd acc (jOf p)) (jOf (pts.getD 0 (0, 0)))
   jacEqM pN (jOf (tS.msm.sums.getLastD (0, 0))) tot)
#guard
  (let pts := (List.range shapeSmoke.ipaRounds).map (fun r =>
        (tS.ipa.accs.getD r []).getLastD (0, 0))
   let tot := (pts.drop 1).foldl (fun acc p => jAdd acc (jOf p)) (jOf (pts.getD 0 (0, 0)))
   jacEqM pN (jOf (tS.ipa.sums.getLastD (0, 0))) tot)

-- Every add is the distinct-x `add_fast` case (`inf = 0`, `same_x = 0`), so leaving col 6 unwired
-- at 0 is correct and no add silently lands on the point at infinity.
#guard tS.msm.addCells.all (fun c => c.getD 6 0 == 0 && c.getD 7 0 == 0)
#guard tS.ipa.addCells.all (fun c => c.getD 6 0 == 0 && c.getD 7 0 == 0)
-- Every point in every chain is on the Pallas curve.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  ((tS.msm.terms.getD i default).accs).all onCurveA)
#guard tS.msm.sums.all onCurveA
#guard tS.ipa.sums.all onCurveA
#guard (List.range shapeSmoke.ipaRounds).all (fun r => (tS.ipa.accs.getD r []).all onCurveA)
-- The chains are non-degenerate: both bit values occur, so both slope signs / both endo branches
-- are exercised in every chain.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (tS.msm.bits.getD i []).contains 0 && (tS.msm.bits.getD i []).contains 1)

-- ⚑ THE DEFERRED `b(ζ)` IS THE CHALLENGE POLYNOMIAL: the assembled product equals the direct fold
-- `∏ (1 + u_k · ζ^{2^{bRounds−1−k}})`, and `ζ` IS challenge 0.
#guard tS.df.zs.getD 0 0 == chalOf shapeSmoke tS.sp 0
#guard (List.range shapeSmoke.bRounds).all (fun k =>
  tS.df.zs.getD (k + 1) 0 == fMul (tS.df.zs.getD k 0) (tS.df.zs.getD k 0))
#guard tS.df.accs.getLastD 0
        == (List.range shapeSmoke.bRounds).foldl
             (fun acc k => fMul acc
               (fAdd 1 (fMul (chalOf shapeSmoke tS.sp (k + 1))
                             (tS.df.zs.getD (shapeSmoke.bRounds - 1 - k) 0)))) 1
-- …and it is NOT the trivial product (a degenerate `b` would make the rung vacuous).
#guard tS.df.accs.getLastD 0 != 1

-- ⚑ THE ASSEMBLED `combined_inner_product` IS THE VERIFIER'S. The Horner chain the `Generic` rows
-- compute equals `KimchiVerify.cipR` applied to the SAME ξ, r and evaluation columns — and `cipR`
-- IS the shipped `combinedInnerProduct` (`KimchiVerify.cipR_eq`, `rfl`, for every field; the
-- CommRing mirror exists precisely so a `ZMod pN` instance can answer to it). So the deferred rung
-- answers to the READ-ONLY transcription of `verifier.rs`, not to its own definition.
#guard
  ((tS.df.ca.getLastD 0 : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.cipR
         ((chalOf shapeSmoke tS.sp shapeSmoke.xiChal : ZMod pN))
         ((chalOf shapeSmoke tS.sp shapeSmoke.rChal : ZMod pN))
         (tS.df.ez.map (fun n => (n : ZMod pN))) (tS.df.ew.map (fun n => (n : ZMod pN))))
-- …and it CAN go red: swapping ξ for r gives a different value (so the equality is discriminating,
-- not two names for zero).
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR
          ((chalOf shapeSmoke tS.sp shapeSmoke.rChal : ZMod pN))
          ((chalOf shapeSmoke tS.sp shapeSmoke.rChal : ZMod pN))
          (tS.df.ez.map (fun n => (n : ZMod pN)))
          (tS.df.ew.map (fun n => (n : ZMod pN)))) == false)
-- The two combiner challenges are distinct (a collision would make the red control vacuous).
#guard chalOf shapeSmoke tS.sp shapeSmoke.xiChal != chalOf shapeSmoke tS.sp shapeSmoke.rChal

end Dregg2.Circuit.Emit.KimchiStepMain
