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

## THE SEVEN SUB-CIRCUITS

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
  * **R6 `ft_eval0`** — `scalars_env` + the linearization CONSTANT TERM + `ft_eval0` +
    `Plonk_checks.checked`'s `perm` scalar (`step_verifier.ml:1019-1071,1131-1136`,
    `plonk_checks.ml:254-548`), compiled by §8b onto double-`Generic` rows and pinned value-for-value
    against `KimchiVerify.gateLinConst` / `ftEval0R` / the 67 constraint bodies list-by-list (§13),
    each with a red control. Its `ft_eval0` output IS the `ft` column R5's `combined_inner_product`
    folds — upstream's own `combine ~ft:ft_eval0`.
  * **R7 `absorption`** — the fr-sponge (`step_verifier.ml:950-1006`, `step_main.ml:525-567`): an
    OPT-SPONGE over the carried bulletproof challenges with a per-block `keep` MASK (the `Field.if_`
    state mux, `:998-1003`), the **43 evaluation columns absorbed at ζ and ζω** in
    `to_absorption_sequence` order, the ξ′/r′ squeezes, and `hash_messages_for_next_step_proof`.

## ⚑ THE SHAPE ORACLE — MEASURED against Mina's own compiled step circuit

o1-labs publishes Mina's compiled circuits as `*_gates.json` release blobs (kimchi's
`Circuit { public_input_size, gates }` serde form; `bridge/mina-zkapp/scripts/
mina-canonical-circuit-oracle.mjs`, whose digest reproduces the md5 in o1-labs' own asset filename).
**`step-zkapp-proved` is branch 4 — the step branch that RUNS `verify_one` on a side-loaded proof**:
PI 67, 20,023 gates, 13,778 non-Generic. Measured against this file's `shapeStep` (2026-08-01):

    gate            Mina step-zkapp-proved   r5_full   r6_ft_eval0  r7_absorption  run-lengths
    total gates            20023               6555       7024          8569
    non-Generic            13778               6183       6185          7536
    Poseidon                6292 (31.4%)       1034       1034          2266    11×572 / 11×206 ✓
    Generic                 6245 (31.2%)        372        839          1033    —
    EndoMul                 2465 (12.3%)       2432       2432          2432    32×77+1×1 / 32×76 ✓
    Zero                    2246 (11.2%)       1433       1435          1554    —
    VarBaseMul              1596  (8.0%)        988        988           988    1×1596 / 1×988    ✓
    EndoMulScalar            776  (3.9%)        184        184           184    / 8×23 — upstream
                    also runs 2×42 8×28 4×25 16×3 1×2 12×2 32×2 9×1 19×1 22×1 24×1 28×1 128×1
    CompleteAdd              403  (2.0%)        112        112           112    1×159 2×65 3×23
                    15×1 30×1 / 1×112

The RUN LENGTHS are the fidelity signal, and all six families are unchanged by R6/R7: a `Poseidon`
permutation is 11 rows (206 of them now, upstream 572), a 128-bit `Scalar_challenge.endo` is 32
`EndoMul` rows, a `var_base_mul` chunk is a lone `VarBaseMul` row followed by its `Zero`, and a
128-bit `to_field_checked` is 8 `EndoMulScalar` rows. The `EndoMul` COUNT is 2432 against upstream's
2465, i.e. the fold/`bullet_reduce` machinery is here at full size. Only SEVEN gate types appear in
any Mina step or wrap circuit — no lookup, no foreign-field, no range-check — and all seven are
emitted here.

⚑ **THE `Generic` SHORTFALL WAS MIS-ATTRIBUTED, and this is the correction.** The prior header wrote
that the `ft_eval0` / `Plonk_checks.checked` sub-circuit was "≈5,900 `Generic` rows — the single
largest remaining sub-circuit". MEASURED (2026-08-02): the constant term is **467 `Generic` rows
here** (934 operations, two per double-generic row), and upstream's own generated
`Scalars.Tick.constant_term` (`plonk_checks/scalars.ml`, 3,295 lines) carries **~2,000 arithmetic
operators** — so even Snarky's unshared emission of it is ~1,000–1,500 rows, not 5,900. The
difference between 467 and that is real and named: `gateLinConst` is the STRUCTURED six-body form,
which shares the 15 Poseidon S-boxes and one α power chain across all 67 constraints, where
`Scalars.Tick` is a fully expanded `PolishToken` tree. Same value — pinned in §13 — fewer operations.

The remaining `Generic` gap (1033 vs 6245) is therefore NOT one missing sub-circuit. It is: the zkApp
branch's own `rule.main` application logic (which is not `verify_one` at all), the per-challenge
`lowest_128_bits ~constrain_low_bits:true` range checks (#1 below), the SECOND `combine` and the
`Shifted_value` unshifts of `combined_inner_product`/`b_correct` (#4), `equal_g`, `group_map`, and
the `Boolean.all` finalisation. #4–#8 below name them.

⚑ Likewise `Poseidon` (2266 vs 6292): R7 brings the count to 206 permutations. `verify_one`'s own
sponge work is now assembled; the remaining 366 permutations are the app logic and the pieces #5
names (the real `sponge_after_index` over the plonk index, `group_map`).

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
  4. **`combined_inner_product` is HALF of upstream's.** `finalize_other_proof` computes
     `combine ~ft:ft_eval0 … + r * combine ~ft:ft_eval1 …` (`step_verifier.ml:1076-1085`): TWO
     ξ-Horner folds, one per evaluation point, r-weighted. R5 assembles ONE (at ζ), and neither the
     second fold nor `Shifted_value.Type1.to_field`'s unshift of the deferred word is here. Same for
     `b_correct`: `challenge_poly ζ` is assembled, `+ r · challenge_poly ζω` and the unshift are not.
  5. **Named and NOT assembled**, each a real sub-circuit: `group_map` (`step_verifier.ml:214-237`);
     `equal_g` and the `check_bulletproof` tail's `scale_fast` of `sg`; the real `sponge_after_index`
     (the plonk index is hashed here from 57 FIXTURE words, not from the actual commitments);
     `x_hat blinding`; `lagrange_commitment` / `public_input_commitment_dynamic`'s domain selection;
     `actual_evaluation`'s per-column chunk Horner (`combined_evals`; our columns are single-chunk,
     though `ζ^n = pow2_pow ζ 16` IS assembled in R6); the `xi_correct` boolean equality; the
     `Boolean.all [xi_correct; b_correct; …]` finalisation and its assert; dummy/`should_verify`
     muxing; and the app-logic `rule.main`.
  6. Every challenge is derived at ONE width (128 bits, 8 `EndoMulScalar` rows). Upstream also uses
     16/32/64/192/256-bit `to_field_checked` (the 1/2/4/12/16-row runs in the table).
  7. R6's `β`/`γ`/`α`/`ζ` are R2's RAW challenge variables. Upstream lifts α and ζ through
     `ScalarChallenge::to_field` (which R4's `Scalar_challenge.endo` rounds assemble) and leaves β/γ
     raw. The lift is not wired INTO R6's inputs. The real-block instance
     (`Dregg2.Bridge.StepMainFtEval0RealBlock`) supplies the genuinely lifted α and ζ, and the same
     program returns block 539508's `ft_eval0` — so the arithmetic is exercised on lifted values even
     though the assembly's own wire is not yet the lift.
  8. R6's seven coset shifts are `FT_SHIFTS` (distinct nonzero fixtures), not `TickShifts.tickShiftsFp
     16`. The Blake2b derivation is off this module's hot path; the REAL shifts are what the
     real-block instance runs, and §13's bent-shift red control shows the value depends on them.
  9. R7's opt-sponge mask is a fixed `keep` pattern (the first half of the blocks kept), standing for
     `branch_data.proofs_verified_mask` / `Vector.trim_front actual_width_mask`. The mask VARIABLE is
     in the circuit and both branches occur; what is not here is deriving it from `branch_data`.

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
import Dregg2.Bridge.MinaWrapFtEval0

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
open Dregg2.Bridge.MinaWrapFtEval0 (IDX_Z IDX_SEL IDX_W IDX_COEFF IDX_S)

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

/-! ### R6/R7 regions (§8d, §8e).

The absorption segments come FIRST and the ft program's slots LAST, because only the ft region's
size depends on a compiled program: every other base is a closed function of the shape. -/

def baseHm (s : StepShape) : Nat := baseCip s + 6 * s.cipEvals + 1
/-- One of `hash_messages_for_next_step_proof`'s 57 fixture words (app state + the 28 plonk-index
commitments as 56 coordinates). -/
def vHm (s : StepShape) (i : Nat) : PVar := xv (baseHm s + i)
def N_HM_FIX : Nat := 57

/-- Variables one sponge segment consumes: `3(nb+sq+1)` state lanes, `2·nb` post lanes, and for a
MASKED segment the `after`/`d`/`p`/`keep` mux cells. -/
def segVarCount (nb sq : Nat) : Nat := 3 * (nb + sq + 1) + 2 * nb + 9 * nb + nb

def baseSegA (s : StepShape) : Nat := baseHm s + N_HM_FIX
/-- Segment A (the opt-sponge): `2·bRounds` masked words, one squeeze. -/
def nbA (s : StepShape) : Nat := (2 * s.bRounds + 1) / 2
def baseSegB (s : StepShape) : Nat := baseSegA s + segVarCount (nbA s) 1
/-- Segment B (the fr-sponge): the digest, `ft_eval1`, `p(ζ)`, `p(ζω)` and the 43 columns at both
points, two squeezes (ξ′ and r′). -/
def nbB (s : StepShape) : Nat := (4 + 2 * (s.cipEvals - 4) + 1) / 2
def baseSegC (s : StepShape) : Nat := baseSegB s + segVarCount (nbB s) 2
/-- Segment C (`hash_messages_for_next_step_proof`), one squeeze. -/
def nbC (s : StepShape) : Nat := (61 + 2 * s.bRounds + 1) / 2
def baseFtS (s : StepShape) : Nat := baseSegC s + segVarCount (nbC s) 1

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

/-- ⚑ The column vector at ζ, with entry 3 — the `ft` column — OVERRIDDEN by R6's computed
`ft_eval0`. That is upstream's own wiring: `combine ~ft:ft_eval0 …` (`step_verifier.ml:1078-1083`)
folds `ft_eval0` into `combined_inner_product` as the fourth prefix column. The four-entry prefix is
`sg_old`×2, the public polynomial, `ft`; R6 reads only entries ≥ 4, so the override is not
circular. -/
def evZOf (ftVal : Nat) (k : Nat) : Nat := if k == 3 then ftVal else evVal k 0

def runDef (s : StepShape) (d : SpongeData) (ftVal : Nat) : DefData :=
  let zs := (List.range s.bRounds).foldl
    (fun acc _ => let x := acc.getLastD 0; acc ++ [fMul x x]) [chalOf s d 0]
  let st := (List.range s.bRounds).foldl
    (fun (acc : List Nat × List Nat) k =>
      let f := fAdd 1 (fMul (chalOf s d (k + 1)) (zs.getD (s.bRounds - 1 - k) 0))
      (acc.1 ++ [f], acc.2 ++ [fMul (acc.2.getLastD 1) f]))
    ([], [1])
  let xi := chalOf s d s.xiChal
  let rr := chalOf s d s.rChal
  let ez := (List.range s.cipEvals).map (fun k => evZOf ftVal k)
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

/-! ## §8b — the ARITHMETIC COMPILER: a straight-line program over `Generic` rows.

`ft_eval0`, `Plonk_checks.checked` and the linearization constant term are pure scalar arithmetic
over the previous proof's evaluations, and Snarky emits them as `Generic` rows
(`plonk_constraint_system.ml`'s `Basic.R1CS`/`Square`/`Boolean` all land on the double generic gate).
Rather than hand-writing several hundred rows, this compiles a STRAIGHT-LINE PROGRAM: slot `i` owns
one circuit variable, each operation is one HALF of a double-`Generic` row, and two consecutive
operations share a row.

⚑ THE PROGRAM IS CHECKED AGAINST THE VALUE LAYER, NOT TRUSTED. `KimchiVerify`'s constraint bodies —
read-only transcriptions of `proof-systems` — are evaluated at the SAME inputs in §12, **list by
list**, and the compiled program's slot values must agree elementwise. A transcription slip in any
one of the 67 constraint bodies goes red there, not silently into a proof. -/

/-- One straight-line arithmetic operation. Slot `i` is the `i`-th entry of the program. -/
inductive AOp where
  /-- ALIAS an existing circuit variable — no row, no new variable. This is how the program reaches
  the sponge's challenges and the previous proof's evaluation columns. -/
  | inp (v : PVar)
  /-- A FREE witness cell: no defining row. Only what the program asserts about it constrains it —
  the witnessed-inverse device (`KimchiVerify` §9b's `denomInv`). -/
  | wit (val : Nat)
  /-- A field constant, pinned by the row `w₀ = k`. -/
  | lit (val : Nat)
  | add (i j : Nat)
  | sub (i j : Nat)
  | mul (i j : Nat)
  /-- ASSERT slot `i` = slot `j`; the produced slot is inert. -/
  | aeq (i j : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- `w₂ = w₀ − w₁`. -/ def cSub : List Int := [1, -1, -1, 0, 0]

/-- The program builder. -/
abbrev AM := StateM (Array AOp)

def em (o : AOp) : AM Nat := do
  let st ← get
  set (st.push o)
  pure st.size

def eLit (k : Nat) : AM Nat := em (.lit k)
def eWit (k : Nat) : AM Nat := em (.wit k)
def eInp (v : PVar) : AM Nat := em (.inp v)
def eAdd (a b : Nat) : AM Nat := em (.add a b)
def eSub (a b : Nat) : AM Nat := em (.sub a b)
def eMul (a b : Nat) : AM Nat := em (.mul a b)
def eEq (a b : Nat) : AM Nat := em (.aeq a b)

/-- `x − y` over `Fp`. -/
def fSub (x y : Nat) : Nat := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fSub x y

/-- Evaluate the program. `lk` resolves `.inp` variables out of the surrounding circuit. -/
def aEval (lk : PVar → Int) (prog : Array AOp) : Array Nat :=
  prog.foldl (fun (vs : Array Nat) op =>
    vs.push (match op with
      | .inp v => (lk v).toNat % pN
      | .wit x => x % pN
      | .lit x => x % pN
      | .add i j => fAdd (vs.getD i 0) (vs.getD j 0)
      | .sub i j => fSub (vs.getD i 0) (vs.getD j 0)
      | .mul i j => fMul (vs.getD i 0) (vs.getD j 0)
      | .aeq i _ => vs.getD i 0)) #[]

/-- Slot `i`'s circuit variable. `.inp` aliases; everything else owns `xv (base + i)`. -/
def aVarAt (base : Nat) (prog : Array AOp) (i : Nat) : PVar :=
  match prog.getD i default with
  | .inp v => v
  | _ => xv (base + i)

/-- The slots that need a `Generic` half (`.inp` and `.wit` need none). -/
def aHalfSlots (prog : Array AOp) : List Nat :=
  (List.range prog.size).filter (fun i =>
    match prog.getD i default with | .inp _ => false | .wit _ => false | _ => true)

/-- Slot `i`'s half: its three permutation columns and its five coefficients. -/
def aHalf (base : Nat) (prog : Array AOp) (i : Nat) : List (Option PVar) × List Int :=
  let V := aVarAt base prog
  match prog.getD i default with
  | .lit k => ([some (V i), none, none], cConst (k : Int))
  | .add a b => ([some (V a), some (V b), some (V i)], cAdd)
  | .sub a b => ([some (V a), some (V b), some (V i)], cSub)
  | .mul a b => ([some (V a), some (V b), some (V i)], cMul)
  | .aeq a b => ([some (V a), some (V b), none], cEq)
  | _ => ([none, none, none], cNil)

/-- The program's rows: two halves per double-`Generic` row, a `cNil` tail half when odd. -/
def aRows (base : Nat) (prog : Array AOp) : List SRow :=
  let sl := aHalfSlots prog
  (List.range ((sl.length + 1) / 2)).map (fun r =>
    let h1 := aHalf base prog (sl.getD (2 * r) 0)
    let h2 := if 2 * r + 1 < sl.length then aHalf base prog (sl.getD (2 * r + 1) 0)
              else (([none, none, none] : List (Option PVar)), cNil)
    ({ kind := .generic, perm := h1.1 ++ h2.1 ++ [none], coeffs := h1.2 ++ h2.2 } : SRow))

/-- The program's contribution to the variable environment. -/
def aEnvOf (base : Nat) (prog : Array AOp) (vals : Array Nat) : VarEnv :=
  (List.range prog.size).filterMap (fun i =>
    match prog.getD i default with
    | .inp _ => none
    | _ => some (xv (base + i), (vals.getD i 0 : Int)))

/-! ## §8c — the SIX GATE CONSTRAINT BODIES, compiled.

Each mirrors a `KimchiVerify` body one-for-one, and §12 pins the compiled values against that body's
own output list. These are the factors the six selectors multiply in the linearization constant term
(`gateLinConst`, `argument.rs:201-213`). -/

/-- `x⁷` — kimchi's Poseidon S-box (`PlonkSpongeConstantsKimchi::PERM_SBOX = 7`). 4 muls. -/
def pSbox (x : Nat) : AM Nat := do
  let x2 ← eMul x x
  let x4 ← eMul x2 x2
  let x6 ← eMul x4 x2
  eMul x6 x

/-- `poseidonLaneConstraint`: `target − (rc + Σ_c mds[j][c]·sbox(source_c))`, sboxes precomputed. -/
def pLane (mdsRow : List Nat) (rc : Nat) (sb : List Nat) (target : Nat) : AM Nat := do
  let t0 ← eMul (mdsRow.getD 0 0) (sb.getD 0 0)
  let t1 ← eMul (mdsRow.getD 1 0) (sb.getD 1 0)
  let t2 ← eMul (mdsRow.getD 2 0) (sb.getD 2 0)
  let s01 ← eAdd t0 t1
  let s ← eAdd s01 t2
  let r ← eAdd rc s
  eSub target r

/-- The 15 `Poseidon` constraints (`poseidonConstraints`), in emission order. -/
def pPoseidon (mdsS : List (List Nat)) (c w wn : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let cc := fun i => c.getD i 0
  let wnn := fun i => wn.getD i 0
  let sb ← (List.range 15).foldlM (fun acc i => do let s ← pSbox (ww i); pure (acc ++ [s])) []
  let g := fun (ix : List Nat) => ix.map (fun i => sb.getD i 0)
  let s0 := g [0, 1, 2]; let s1 := g [6, 7, 8]; let s2 := g [9, 10, 11]
  let s3 := g [12, 13, 14]; let s4 := g [3, 4, 5]
  let m := fun j => mdsS.getD j []
  let spec : List (Nat × Nat × List Nat × Nat) :=
    [ (0, 0, s0, ww 6), (1, 1, s0, ww 7), (2, 2, s0, ww 8)
    , (0, 3, s1, ww 9), (1, 4, s1, ww 10), (2, 5, s1, ww 11)
    , (0, 6, s2, ww 12), (1, 7, s2, ww 13), (2, 8, s2, ww 14)
    , (0, 9, s3, ww 3), (1, 10, s3, ww 4), (2, 11, s3, ww 5)
    , (0, 12, s4, wnn 0), (1, 13, s4, wnn 1), (2, 14, s4, wnn 2) ]
  spec.foldlM (fun acc q => do let k ← pLane (m q.1) (cc q.2.1) q.2.2.1 q.2.2.2; pure (acc ++ [k])) []

/-- The 7 `CompleteAdd` constraints (`completeAddConstraints`). -/
def pCompleteAdd (one : Nat) (w : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let x1 := ww 0; let y1 := ww 1; let x2 := ww 2; let y2 := ww 3
  let x3 := ww 4; let y3 := ww 5; let inf := ww 6; let sameX := ww 7
  let s := ww 8; let infZ := ww 9; let x21Inv := ww 10
  let x21 ← eSub x2 x1
  let y21 ← eSub y2 y1
  let x1sq ← eMul x1 x1
  let nsx ← eSub one sameX
  let a ← eMul x21Inv x21
  let k0 ← eSub a nsx
  let k1 ← eMul sameX x21
  let ss ← eAdd s s
  let ssy ← eMul ss y1
  let q2 ← eAdd x1sq x1sq
  let t1a ← eSub ssy q2
  let t1 ← eSub t1a x1sq
  let p1 ← eMul sameX t1
  let x21s ← eMul x21 s
  let t2 ← eSub x21s y21
  let p2 ← eMul nsx t2
  let k2 ← eAdd p1 p2
  let sx ← eAdd x1 x2
  let sx3 ← eAdd sx x3
  let s2v ← eMul s s
  let k3 ← eSub sx3 s2v
  let d ← eSub x1 x3
  let sd ← eMul s d
  let e1 ← eSub sd y1
  let k4 ← eSub e1 y3
  let f ← eSub sameX inf
  let k5 ← eMul y21 f
  let g ← eMul y21 infZ
  let k6 ← eSub g inf
  pure [k0, k1, k2, k3, k4, k5, k6]

/-- The 21 `VarbaseMul` constraints (`varBaseMulConstraints`). -/
def pVarBaseMul (one : Nat) (w wn : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let wnn := fun i => wn.getD i 0
  let xT := ww 0; let yT := ww 1
  let accX := fun i => ([ww 2, ww 7, ww 9, ww 11, ww 13, wnn 0] : List Nat).getD i 0
  let accY := fun i => ([ww 3, ww 8, ww 10, ww 12, ww 14, wnn 1] : List Nat).getD i 0
  let bit := fun i => ([wnn 2, wnn 3, wnn 4, wnn 5, wnn 6] : List Nat).getD i 0
  let sl := fun i => ([wnn 7, wnn 8, wnn 9, wnn 10, wnn 11] : List Nat).getD i 0
  let nPrev := ww 4; let nNext := ww 5
  let acc ← (List.range 5).foldlM (fun a i => do let aa ← eAdd a a; eAdd (bit i) aa) nPrev
  let dec ← eSub nNext acc
  let rest ← (List.range 5).foldlM (fun out i => do
      let b := bit i; let s := sl i
      let ix := accX i; let iy := accY i
      let ox := accX (i + 1); let oy := accY (i + 1)
      let b2 ← eAdd b b
      let bSign ← eSub b2 one
      let ssq ← eMul s s
      let rxa ← eSub ssq ix
      let rx ← eSub rxa xT
      let t ← eSub ix rx
      let iy2 ← eAdd iy iy
      let ts ← eMul t s
      let u ← eSub iy2 ts
      let bb ← eMul b b
      let k0 ← eSub bb b
      let ixT ← eSub ix xT
      let l1 ← eMul ixT s
      let by' ← eMul bSign yT
      let r1 ← eSub iy by'
      let k1 ← eSub l1 r1
      let uu ← eMul u u
      let tt ← eMul t t
      let oxT ← eSub ox xT
      let q ← eAdd oxT ssq
      let ttq ← eMul tt q
      let k2 ← eSub uu ttq
      let oyiy ← eAdd oy iy
      let l3 ← eMul oyiy t
      let ixox ← eSub ix ox
      let r3 ← eMul ixox u
      let k3 ← eSub l3 r3
      pure (out ++ [k0, k1, k2, k3])) []
  pure (dec :: rest)

/-- The 11 DEPLOYED `EndosclMul` constraints (`endoMulConstraints … |>.take 11`, `proof-systems`
0.3.0's `CONSTRAINTS = 11` — the 12th distinct-point witness is NOT in the deployed constant term,
`gateLinConst`'s own `.take 11`). -/
def pEndoMul (one endo : Nat) (w wn : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let wnn := fun i => wn.getD i 0
  let xt := ww 0; let yt := ww 1
  let xp := ww 4; let yp := ww 5; let n := ww 6
  let xr := ww 7; let yr := ww 8; let s1 := ww 9; let s3 := ww 10
  let b1 := ww 11; let b2 := ww 12; let b3 := ww 13; let b4 := ww 14
  let xs := wnn 4; let ys := wnn 5; let nNext := wnn 6
  let em1 ← eSub endo one
  let t1 ← eMul b1 em1
  let u1 ← eAdd one t1
  let xq1 ← eMul u1 xt
  let t3 ← eMul b3 em1
  let u3 ← eAdd one t3
  let xq2 ← eMul u3 xt
  let b22 ← eAdd b2 b2
  let v2 ← eSub b22 one
  let yq1 ← eMul v2 yt
  let b42 ← eAdd b4 b4
  let v4 ← eSub b42 one
  let yq2 ← eMul v4 yt
  let s1sq ← eMul s1 s1
  let s3sq ← eMul s3 s3
  let n2 ← eAdd n n
  let d1 ← eAdd n2 b1
  let d1a ← eAdd d1 d1
  let d2 ← eAdd d1a b2
  let d2a ← eAdd d2 d2
  let d3 ← eAdd d2a b3
  let d3a ← eAdd d3 d3
  let d4 ← eAdd d3a b4
  let nC ← eSub d4 nNext
  let xpxr ← eSub xp xr
  let xrxs ← eSub xr xs
  let ysyr ← eAdd ys yr
  let yryp ← eAdd yr yp
  let k0 ← do let t ← eMul b1 b1; eSub t b1
  let k1 ← do let t ← eMul b2 b2; eSub t b2
  let k2 ← do let t ← eMul b3 b3; eSub t b3
  let k3 ← do let t ← eMul b4 b4; eSub t b4
  let k4 ← do let a ← eSub xq1 xp; let l ← eMul a s1; let r ← eSub yq1 yp; eSub l r
  let k5 ← do
    let xp2 ← eAdd xp xp
    let a ← eSub xp2 s1sq
    let a2 ← eAdd a xq1
    let m1 ← eMul xpxr s1
    let m2 ← eAdd m1 yryp
    let l ← eMul a2 m2
    let yp2 ← eAdd yp yp
    let r ← eMul yp2 xpxr
    eSub l r
  let k6 ← do
    let l ← eMul yryp yryp
    let p ← eMul xpxr xpxr
    let a ← eSub s1sq xq1
    let a2 ← eAdd a xr
    let r ← eMul p a2
    eSub l r
  let k7 ← do let a ← eSub xq2 xr; let l ← eMul a s3; let r ← eSub yq2 yr; eSub l r
  let k8 ← do
    let xr2 ← eAdd xr xr
    let a ← eSub xr2 s3sq
    let a2 ← eAdd a xq2
    let m1 ← eMul xrxs s3
    let m2 ← eAdd m1 ysyr
    let l ← eMul a2 m2
    let yr2 ← eAdd yr yr
    let r ← eMul yr2 xrxs
    eSub l r
  let k9 ← do
    let l ← eMul ysyr ysyr
    let p ← eMul xrxs xrxs
    let a ← eSub s3sq xq2
    let a2 ← eAdd a xs
    let r ← eMul p a2
    eSub l r
  pure [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, nC]

/-- The 11 `EndomulScalar` constraints (`endomulScalarConstraints`). `cA/cB/cC` are the witnessed
quotients `11/6, −5/2, 2/3`, and `negOne/three/six/eleven` are the small literals of `c`, `d` and
`crumb`. -/
def pEmScalar (cA cB cC negOne three six eleven : Nat) (w : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let n0 := ww 0; let n8 := ww 1; let a0 := ww 2; let b0 := ww 3
  let a8 := ww 4; let b8 := ww 5
  let x := fun i => ww (6 + i)
  let cf : Nat → AM Nat := fun t => do
    let m1 ← eMul cC t
    let s1 ← eAdd m1 cB
    let m2 ← eMul s1 t
    let s2 ← eAdd m2 cA
    eMul s2 t
  let cfs ← (List.range 8).foldlM (fun acc i => do let v ← cf (x i); pure (acc ++ [v])) []
  let dfs ← (List.range 8).foldlM (fun acc i => do
      let t := x i
      let m1 ← eMul negOne t
      let s1 ← eAdd m1 three
      let m2 ← eMul s1 t
      let s2 ← eAdd m2 negOne
      let v ← eAdd (cfs.getD i 0) s2
      pure (acc ++ [v])) []
  let n8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← eAdd acc acc
      let a4 ← eAdd a2 a2
      eAdd a4 (x i)) n0
  let a8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← eAdd acc acc
      eAdd a2 (cfs.getD i 0)) a0
  let b8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← eAdd acc acc
      eAdd a2 (dfs.getD i 0)) b0
  let c0 ← eSub n8e n8
  let c1 ← eSub a8e a8
  let c2 ← eSub b8e b8
  let cr ← (List.range 8).foldlM (fun acc i => do
      let t := x i
      let a ← eSub t six
      let b ← eMul a t
      let c ← eAdd b eleven
      let d ← eMul c t
      let e ← eSub d six
      let v ← eMul e t
      pure (acc ++ [v])) []
  pure ([c0, c1, c2] ++ cr)

/-- `genericGateConstraint` — the double generic gate's own linearization factor. -/
def pGenericGate (genSel alpha : Nat) (c w : List Nat) : AM Nat := do
  let cc := fun i => c.getD i 0
  let ww := fun i => w.getD i 0
  let t0 ← eMul (cc 0) (ww 0)
  let t1 ← eMul (cc 1) (ww 1)
  let t2 ← eMul (cc 2) (ww 2)
  let w01 ← eMul (ww 0) (ww 1)
  let t3 ← eMul (cc 3) w01
  let s0 ← eAdd t0 t1
  let s1 ← eAdd s0 t2
  let s2 ← eAdd s1 t3
  let k1 ← eAdd s2 (cc 4)
  let u0 ← eMul (cc 5) (ww 3)
  let u1 ← eMul (cc 6) (ww 4)
  let u2 ← eMul (cc 7) (ww 5)
  let w34 ← eMul (ww 3) (ww 4)
  let u3 ← eMul (cc 8) w34
  let r0 ← eAdd u0 u1
  let r1 ← eAdd r0 u2
  let r2 ← eAdd r1 u3
  let k2 ← eAdd r2 (cc 9)
  let ak2 ← eMul alpha k2
  let sum ← eAdd k1 ak2
  eMul genSel sum

/-- `alphaCombine α cs = Σᵢ αⁱ·csᵢ`, Horner-free (the powers are shared with `ft_eval0`'s `α^21..23`
so the whole rung pays for one power chain). -/
def pAlphaCombine (apow : List Nat) (cs : List Nat) : AM Nat := do
  match cs with
  | [] => eLit 0
  | c0 :: rest =>
      (List.range rest.length).foldlM (fun acc i => do
        let t ← eMul (apow.getD (i + 1) 0) (rest.getD i 0)
        eAdd acc t) c0

/-! ## §8d — R6, `ft_eval0` + `Plonk_checks.checked`, with `scalars_env`.

`step_verifier.ml:1019-1071,1131-1136`. The rung compiles, in order:

  * **`scalars_env`** (`plonk_checks.ml:254-408`) — `ω^{n−1}` as a WITNESSED inverse (`ω·ω⁻¹ = 1`
    checked in-circuit, so `ω^{n−1}` is derived rather than asserted), `ω^{n−2}`, `ω^{n−3}`,
    `zk_polynomial`, `ζ^n − 1` by `log2n` squarings, and the α power chain `α⁰..α²³`.
  * **the linearization constant term** — `gateLinConst`: all six gate bodies of §8c behind their
    selectors, α-combined. This is `Sc.constant_term env` (`plonk_checks.ml:459`).
  * **`ft_eval0`** (`plonk_checks.ml:420-460`) — the permutation numerator fold over the 6 σ evals,
    minus `p(ζ)`, minus the denominator fold over the 7 coset shifts, plus `numerator·denomInv` with
    `denom·denomInv = 1` CHECKED (the same witnessed-inverse device, no `Field` instance needed),
    minus the constant term.
  * **`Plonk_checks.checked`** (`plonk_checks.ml:516-548`) — `derive_plonk`'s `perm` scalar
    `−(fold over e.s of (γ + β·s + w) from z(ζω)·β·α²¹·zkp)`, asserted equal to the deferred value.

⚑ IT READS THE ASSEMBLY, not a private island: `ζ/α/β/γ` are R2's challenge variables and the 43
evaluation columns are R5's `vEz`/`vEw` — so the whole rung hangs off σ classes that R1–R5 created.
And its OUTPUT is tied to `vEz 3`, the `ft` entry of the `combined_inner_product` column vector,
which is exactly `combine ~ft:ft_eval0` at `step_verifier.ml:1078-1083`. -/

/-- The four-entry prefix of the C8 column vector (`sg_old`×2, the public polynomial, `ft`);
`MinaWrapFtEval0`'s own slicing, and `IDX_Z`/`IDX_W`/`IDX_S`/`IDX_COEFF`/`IDX_SEL` index AFTER it. -/
def EV_PREFIX : Nat := 4
/-- Column `k` of the 43-column evaluation vector at ζ. -/
def vColZ (s : StepShape) (k : Nat) : PVar := vEz s (EV_PREFIX + k)
/-- …and at ζω. -/
def vColW (s : StepShape) (k : Nat) : PVar := vEw s (EV_PREFIX + k)

/-- Which challenge plays ζ / α / β / γ in the deferred scalar arithmetic. -/
def StepShape.zetaChal (_s : StepShape) : Nat := 0
def StepShape.alphaChal (_s : StepShape) : Nat := 1
def StepShape.betaChal (_s : StepShape) : Nat := 2
def StepShape.gammaChal (_s : StepShape) : Nat := 3

/-- The wire the ft program reads: each field is a SOURCE OP, so the same program compiles against
the assembled circuit's variables (`.inp`) and against a real block's field values (`.lit`). -/
structure FtWire where
  ez : Nat → AOp
  ew : Nat → AOp
  zeta : AOp
  alpha : AOp
  beta : AOp
  gamma : AOp
  pZeta : AOp

/-- The config the ft program bakes in as constants: the domain, the seven coset shifts, the MDS,
the endomorphism coefficient and the three `EndomulScalar` quotients — plus the two witnessed
values the circuit CHECKS rather than trusts. -/
structure FtCfg where
  log2n : Nat
  omega : Nat
  omegaInv : Nat
  shifts : List Nat
  mds9 : List Nat
  endo : Nat
  cA : Nat
  cB : Nat
  cC : Nat
  denomInv : Nat
  permClaimed : Nat
  deriving Repr, Inhabited

/-- The slots the rung's rows and pins refer to. -/
structure FtSlots where
  ftEval0 : Nat
  linConst : Nat
  zkp : Nat
  perm : Nat
  zetaN : Nat
  omInv3 : Nat
  deriving Repr, Inhabited

/-- **The ft program.** Returns the named output slots. -/
def ftBuild (W : FtWire) (C : FtCfg) : AM FtSlots := do
  -- ── small literals and the config constants ───────────────────────────────────────────────
  let one ← eLit 1
  let negOne ← eLit (pN - 1)
  let three ← eLit 3
  let six ← eLit 6
  let eleven ← eLit 11
  let omega ← eLit C.omega
  let omInv ← eLit C.omegaInv
  let endo ← eLit C.endo
  let cA ← eLit C.cA
  let cB ← eLit C.cB
  let cC ← eLit C.cC
  let shiftS ← (List.range 7).foldlM
    (fun acc i => do let v ← eLit (C.shifts.getD i 0); pure (acc ++ [v])) []
  let mdsS ← (List.range 3).foldlM (fun acc j => do
      let row ← (List.range 3).foldlM
        (fun r i => do let v ← eLit (C.mds9.getD (3 * j + i) 0); pure (r ++ [v])) []
      pure (acc ++ [row])) []
  -- ── scalars_env ───────────────────────────────────────────────────────────────────────────
  -- ⚑ ω^{n−1} = ω⁻¹ is DERIVED: `ω·ω⁻¹ = 1` is a row, so a wrong inverse cannot be witnessed.
  let chk ← eMul omega omInv
  let _ ← eEq chk one
  let omInv2 ← eMul omInv omInv
  let omInv3 ← eMul omInv2 omInv
  let zeta ← em W.zeta
  let alpha ← em W.alpha
  let beta ← em W.beta
  let gamma ← em W.gamma
  let zm3 ← eSub zeta omInv3
  let zm2 ← eSub zeta omInv2
  let zm1 ← eSub zeta omInv
  let zkpA ← eMul zm3 zm2
  let zkp ← eMul zkpA zm1
  let zetaN ← (List.range C.log2n).foldlM (fun acc _ => eMul acc acc) zeta
  let zeta1m1 ← eSub zetaN one
  let apow ← (List.range 23).foldlM (fun acc _ => do
      let p ← eMul (acc.getLastD one) alpha; pure (acc ++ [p])) [one]
  let a0 := apow.getD 21 0
  let a1 := apow.getD 22 0
  let a2 := apow.getD 23 0
  -- ── the wire columns ──────────────────────────────────────────────────────────────────────
  let ez ← (List.range 43).foldlM (fun acc k => do let v ← em (W.ez k); pure (acc ++ [v])) []
  let ew ← (List.range 43).foldlM (fun acc k => do let v ← em (W.ew k); pure (acc ++ [v])) []
  let coeff := (List.range 15).map (fun i => ez.getD (IDX_COEFF + i) 0)
  let wv := (List.range 15).map (fun i => ez.getD (IDX_W + i) 0)
  let wn := (List.range 15).map (fun i => ew.getD (IDX_W + i) 0)
  let sv := (List.range 6).map (fun i => ez.getD (IDX_S + i) 0)
  let zZeta := ez.getD IDX_Z 0
  let zZetaW := ew.getD IDX_Z 0
  let genSel := ez.getD (IDX_SEL + 0) 0
  let posSel := ez.getD (IDX_SEL + 1) 0
  let caddSel := ez.getD (IDX_SEL + 2) 0
  let mulSel := ez.getD (IDX_SEL + 3) 0
  let emulSel := ez.getD (IDX_SEL + 4) 0
  let emsSel := ez.getD (IDX_SEL + 5) 0
  -- ── gateLinConst: the six bodies behind their selectors ───────────────────────────────────
  let gG ← pGenericGate genSel alpha coeff wv
  let cPos ← pPoseidon mdsS coeff wv wn
  let aPos ← pAlphaCombine apow cPos
  let gPos ← eMul posSel aPos
  let cAdd' ← pCompleteAdd one wv
  let aAdd ← pAlphaCombine apow cAdd'
  let gAdd ← eMul caddSel aAdd
  let cMulG ← pVarBaseMul one wv wn
  let aMul ← pAlphaCombine apow cMulG
  let gMul ← eMul mulSel aMul
  let cEmul ← pEndoMul one endo wv wn
  let aEmul ← pAlphaCombine apow cEmul
  let gEmul ← eMul emulSel aEmul
  let cEms ← pEmScalar cA cB cC negOne three six eleven wv
  let aEms ← pAlphaCombine apow cEms
  let gEms ← eMul emsSel aEms
  let l1 ← eAdd gG gPos
  let l2 ← eAdd l1 gAdd
  let l3 ← eAdd l2 gMul
  let l4 ← eAdd l3 gEmul
  let lct ← eAdd l4 gEms
  -- ── ft_eval0 (`ftEval0R`, term for term) ──────────────────────────────────────────────────
  let w6g ← eAdd (wv.getD 6 0) gamma
  let i1 ← eMul w6g zZetaW
  let i2 ← eMul i1 a0
  let init ← eMul i2 zkp
  let numerFold ← (List.range 6).foldlM (fun x i => do
      let bs ← eMul beta (sv.getD i 0)
      let bw ← eAdd bs (wv.getD i 0)
      let bwg ← eAdd bw gamma
      eMul x bwg) init
  let afterPub ← eSub numerFold (← em W.pZeta)
  let dInit0 ← eMul a0 zkp
  let dInit ← eMul dInit0 zZeta
  let bz ← eMul beta zeta
  let denomFold ← (List.range 7).foldlM (fun x i => do
      let bzs ← eMul bz (shiftS.getD i 0)
      let gb ← eAdd gamma bzs
      let gbw ← eAdd gb (wv.getD i 0)
      eMul x gbw) dInit
  let afterDenom ← eSub afterPub denomFold
  let n1a ← eMul zeta1m1 a1
  let n1 ← eMul n1a zm3
  let n2a ← eMul zeta1m1 a2
  let zm1c ← eSub zeta one
  let n2 ← eMul n2a zm1c
  let nsum ← eAdd n1 n2
  let oneMz ← eSub one zZeta
  let numerator ← eMul nsum oneMz
  let denom ← eMul zm3 zm1c
  let dinv ← eWit C.denomInv
  let dchk ← eMul denom dinv
  let _ ← eEq dchk one
  let nd ← eMul numerator dinv
  let afterZk ← eAdd afterDenom nd
  let ftEval0 ← eSub afterZk lct
  -- ── Plonk_checks.checked: derive_plonk's `perm` scalar, asserted against the deferred word ──
  let p0 ← eMul zZetaW beta
  let p1 ← eMul p0 a0
  let pInit ← eMul p1 zkp
  let pFold ← (List.range 6).foldlM (fun x i => do
      let bs ← eMul beta (sv.getD i 0)
      let gb ← eAdd gamma bs
      let gbw ← eAdd gb (wv.getD i 0)
      eMul x gbw) pInit
  let perm ← eMul negOne pFold
  let permClaimed ← eWit C.permClaimed
  let _ ← eEq perm permClaimed
  pure { ftEval0 := ftEval0, linConst := lct, zkp := zkp, perm := perm
       , zetaN := zetaN, omInv3 := omInv3 }

/-- The compiled program plus its named slots. -/
structure FtProg where
  prog : Array AOp
  slots : FtSlots
  deriving Repr, Inhabited

def ftProgOf (W : FtWire) (C : FtCfg) : FtProg :=
  let r := (ftBuild W C).run #[]
  { prog := r.2, slots := r.1 }

/-! ### The committed ft config and wire, for the ASSEMBLED instance. -/

/-- The step domain: `Common.Max_degree.step_log2 = 16` (`plonk_checks.ml` `srs_length_log2`). -/
def FT_LOG2N : Nat := 16
def FT_N : Nat := 2 ^ FT_LOG2N
/-- The `2^16`-th root of unity of `Fp`, DERIVED (`MinaWrapFtEval0.rootOfUnity`, read-only). -/
def FT_OMEGA : Nat := (Dregg2.Bridge.MinaWrapFtEval0.rootOfUnity pN FT_LOG2N).val
def FT_OMEGA_INV : Nat := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv FT_OMEGA
/-- `env.endo_coefficient()` on the STEP side: the BASE endomorphism eigenvalue `5^((p−1)/3)`, NOT
the scalar-challenge endo (`MinaWrapFtEval0Weld` §6's `stepEndoCoefficient`; the conflation of the
two cube roots is the defect that file closed). -/
def FT_ENDO : Nat :=
  (Dregg2.Bridge.MinaWrapFtEval0.powFast ((5 : Nat) : ZMod pN) ((pN - 1) / 3)).val
/-- The three `EndomulScalar` quotients `11/6, −5/2, 2/3` (`quotientConsts`, read-only). -/
def FT_QUOT : Nat × Nat × Nat :=
  match Dregg2.Bridge.MinaWrapFtEval0.quotientConsts pN with
  | some (a, b, c) => (a.val, b.val, c.val)
  | none => (0, 0, 0)
/-- Seven distinct nonzero coset shifts. The real Tick shifts are `TickShifts.tickShiftsFp 16`; the
assembled instance's shifts are its own (the Blake2b derivation is off this module's hot path), and
the real ones are exercised in the real-block pin. -/
def FT_SHIFTS : List Nat := (List.range 7).map (fun i => (1 + 7919 * (i + 1) * (i + 3)) % pN)
/-- The linearization's `Constants::mds` IS `Vesta::sponge_params().mds = fp_kimchi` (`curve.rs:63`),
i.e. K3's own `PastaPoseidon.mdsN` — the same nine constants the sponge rung R1 permutes with. -/
def FT_MDS9 : List Nat := Dregg2.Circuit.Emit.PastaPoseidon.mdsN.flatten

/-- The ft program's `.inp` lookup: the challenges and the 43 columns, straight from the chains. It
does NOT read column 3, so the `ft` override below is not circular. -/
def ftInputEnv (s : StepShape) (d : SpongeData) : VarEnv :=
  (List.range s.chals).map (fun c => (vN s c s.emsRows, (chalOf s d c : Int)))
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [(vEz s k, (evVal k 0 : Int)), (vEw s k, (evVal k 1 : Int))])

def ftWireOf (s : StepShape) : FtWire :=
  { ez := fun k => .inp (vColZ s k)
  , ew := fun k => .inp (vColW s k)
  , zeta := .inp (vN s s.zetaChal s.emsRows)
  , alpha := .inp (vN s s.alphaChal s.emsRows)
  , beta := .inp (vN s s.betaChal s.emsRows)
  , gamma := .inp (vN s s.gammaChal s.emsRows)
  , pZeta := .inp (vEz s 2) }

/-- The two witnessed values, computed from the wire: `denomInv` and the deferred `perm` scalar.
Both are CHECKED by a row (`denom·denomInv = 1`, `perm_actual = perm_claimed`), so a wrong witness
is a refusal rather than an accept. Computed by running the program once with placeholders. -/
def ftCfgRaw (dInv pC : Nat) : FtCfg :=
  { log2n := FT_LOG2N, omega := FT_OMEGA, omegaInv := FT_OMEGA_INV
  , shifts := FT_SHIFTS, mds9 := FT_MDS9, endo := FT_ENDO
  , cA := FT_QUOT.1, cB := FT_QUOT.2.1, cC := FT_QUOT.2.2
  , denomInv := dInv, permClaimed := pC }

/-- Everything R6 needs, evaluated ONCE. -/
structure FtData where
  fp : FtProg
  vals : Array Nat
  /-- The witnessed inverse of `(ζ − ω^{n−3})(ζ − 1)`, checked by a row. -/
  denomInv : Nat
  /-- The deferred `perm` scalar `Plonk_checks.checked` compares against, checked by a row. -/
  permClaimed : Nat
  deriving Repr, Inhabited

/-- Run the program twice: once to read off `denom` and the actual `perm` scalar, then once with the
witnesses those force. The second run is the emitted one. -/
def runFt (s : StepShape) (d : SpongeData) : FtData :=
  let W := ftWireOf s
  let lk := envLookupAt (envIndex (ftInputEnv s d))
  let p0 := ftProgOf W (ftCfgRaw 1 0)
  let v0 := aEval lk p0.prog
  -- `denom` is the slot the `dchk` multiplication reads; recompute it directly from ζ and ω^{n−3}.
  let zeta := (lk (vN s s.zetaChal s.emsRows)).toNat % pN
  let omInv3 := v0.getD p0.slots.omInv3 0
  let denom := fMul (fSub zeta omInv3) (fSub zeta 1)
  let dInv := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv denom
  let pC := v0.getD p0.slots.perm 0
  let p1 := ftProgOf W (ftCfgRaw dInv pC)
  { fp := p1, vals := aEval lk p1.prog, denomInv := dInv, permClaimed := pC }

/-- **R6's rows**: the compiled program, the tie of its `ft_eval0` output to the `ft` column of the
`combined_inner_product` vector, and the σ-only probes. -/
def ftRows (s : StepShape) (f : FtData) (wired : Bool) : List SRow :=
  let base := baseFtS s
  let V := aVarAt base f.fp.prog
  aRows base f.fp.prog
  ++ [ genericRow (some (V f.fp.slots.ftEval0)) (some (vEz s 3)) none none none none (cEq ++ cNil)
     , probeRow wired (V f.fp.slots.ftEval0) (V f.fp.slots.linConst)
     , probeRow wired (V f.fp.slots.perm) (V f.fp.slots.zkp) ]

/-! ## §8e — R7, the EVALUATION ABSORPTION + opt-sponge masking.

`step_verifier.ml:950-1006`, `step_main.ml:525-567`. Three sponge SEGMENTS, each a fresh `[0,0,0]`
state, `absorb` blocks of two words (`rate = 2`), then bare squeeze permutations:

  * **A — the opt-sponge** over the carried bulletproof challenges, with a per-block `keep` MASK.
    Upstream's own trick (`:985-1003`) absorbs unconditionally and then MUXES the state
    (`Array.map2_exn sponge.state state_before ~f:(Field.if_ b)`); this compiles that mux as
    `outⱼ = beforeⱼ + keep·(afterⱼ − beforeⱼ)`, three lanes, three `Generic` halves each. That is
    the `branch_data.proofs_verified_mask` path, and it is the piece the sponge rung R1 had no
    shape for.
  * **B — the fr-sponge**: the challenge digest, `ft_eval1`, `p(ζ)`, `p(ζω)`, then **the 43 columns
    at ζ and ζω interleaved** (`to_absorption_sequence`), then TWO squeezes for ξ′ and r′.
  * **C — `hash_messages_for_next_step_proof`**: the app state, the 28 plonk-index commitments (56
    coordinates), the two challenge-polynomial commitments and the unpadded bulletproof challenges,
    then one squeeze.

⚑ EVERY ABSORBED WORD IS AN ASSEMBLY VARIABLE where upstream's is: segment A absorbs R2's
challenges, segment B absorbs R5's evaluation columns (the SAME variables R6 reads) and R6's
`ft_eval1`/`p(ζ)` entries, and segment C absorbs R3's and R4's fold outputs. -/

/-- One segment's schedule. -/
structure SegSpec where
  /-- absorbed words: the variable and its value, padded to an even length. -/
  ws : List (PVar × Nat)
  /-- squeeze permutations after the absorb blocks. -/
  squeezes : Nat
  /-- per absorb-block `keep` mask: `some (var, val)` masks, `none` does not. -/
  masked : Bool
  deriving Inhabited

def SegSpec.nb (g : SegSpec) : Nat := (g.ws.length + 1) / 2
def SegSpec.blocks (g : SegSpec) : Nat := g.nb + g.squeezes

/-- A segment's evaluated trajectory. -/
structure SegData where
  /-- the state ENTERING each block, `blocks + 1` of them. -/
  states : List (List Nat)
  /-- the 56 round states of each block's permutation. -/
  perms : List (List (List Nat))
  /-- the un-muxed permutation output of each absorb block. -/
  afters : List (List Nat)
  deriving Repr, Inhabited

/-- `keep` for absorb block `b` of a masked segment: the first half of the blocks are the ACTUAL
previous proof's challenges (`Vector.trim_front actual_width_mask`), the rest are masked out. -/
def segKeep (nb b : Nat) : Nat := if 2 * b < nb then 1 else 0

def runSeg (g : SegSpec) : SegData :=
  (List.range g.blocks).foldl
    (fun d b =>
      let pre := d.states.getLastD [0, 0, 0]
      let post :=
        if b < g.nb then
          [ fAdd (pre.getD 0 0) ((g.ws.getD (2 * b) (xv 0, 0)).2)
          , fAdd (pre.getD 1 0) ((g.ws.getD (2 * b + 1) (xv 0, 0)).2)
          , pre.getD 2 0 ]
        else pre
      let ss := permStates post
      let after := ss.getLastD post
      let next :=
        if b < g.nb && g.masked && segKeep g.nb b == 0 then pre else after
      { states := d.states ++ [next], perms := d.perms ++ [ss]
      , afters := d.afters ++ [after] })
    { states := [[0, 0, 0]], perms := [], afters := [] }

/-- Segment variable regions, all relative to one base. -/
def sgSt (base _nb _sq b j : Nat) : PVar := xv (base + 3 * b + j)
def sgPost (base nb sq b j : Nat) : PVar := xv (base + 3 * (nb + sq + 1) + 2 * b + j)
def sgAfter (base nb sq b j : Nat) : PVar :=
  xv (base + 3 * (nb + sq + 1) + 2 * nb + 3 * b + j)
def sgD (base nb sq b j : Nat) : PVar :=
  xv (base + 3 * (nb + sq + 1) + 5 * nb + 3 * b + j)
def sgP (base nb sq b j : Nat) : PVar :=
  xv (base + 3 * (nb + sq + 1) + 8 * nb + 3 * b + j)
/-- The per-block `keep` mask variable. -/
def sgKeep (base nb sq b : Nat) : PVar := xv (base + 3 * (nb + sq + 1) + 11 * nb + b)

/-- **One segment's rows.** -/
def segRows (base : Nat) (g : SegSpec) (d : SegData) (wired : Bool) : List SRow :=
  let nb := g.nb
  let sq := g.squeezes
  [ genericRow (some (sgSt base nb sq 0 0)) none none (some (sgSt base nb sq 0 1)) none none
      (cConst 0 ++ cConst 0)
  , genericRow (some (sgSt base nb sq 0 2)) none none none none none (cConst 0 ++ cNil) ]
  ++ (List.range g.blocks).flatMap (fun b =>
      if b < nb then
        let out : Nat → PVar :=
          if g.masked then (fun j => sgAfter base nb sq b j)
          else (fun j => sgSt base nb sq (b + 1) j)
        [ genericRow (some (sgSt base nb sq b 0)) (some (g.ws.getD (2 * b) (xv 0, 0)).1)
                     (some (sgPost base nb sq b 0))
                     (some (sgSt base nb sq b 1)) (some (g.ws.getD (2 * b + 1) (xv 0, 0)).1)
                     (some (sgPost base nb sq b 1)) (cAdd ++ cAdd) ]
        ++ permBlockRows (sgPost base nb sq b 0) (sgPost base nb sq b 1) (sgSt base nb sq b 2)
             (out 0) (out 1) (out 2) (d.perms.getD b [])
        ++ (if g.masked then
              -- the `Field.if_` mux: outⱼ = beforeⱼ + keep·(afterⱼ − beforeⱼ)
              (List.range 3).map (fun j =>
                genericRow (some (sgAfter base nb sq b j)) (some (sgSt base nb sq b j))
                           (some (sgD base nb sq b j))
                           (some (sgKeep base nb sq b)) (some (sgD base nb sq b j))
                           (some (sgP base nb sq b j)) (cSub ++ cMul))
              ++ [ genericRow (some (sgSt base nb sq b 0)) (some (sgP base nb sq b 0))
                              (some (sgSt base nb sq (b + 1) 0))
                              (some (sgSt base nb sq b 1)) (some (sgP base nb sq b 1))
                              (some (sgSt base nb sq (b + 1) 1)) (cAdd ++ cAdd)
                 , genericRow (some (sgSt base nb sq b 2)) (some (sgP base nb sq b 2))
                              (some (sgSt base nb sq (b + 1) 2)) none none none (cAdd ++ cNil) ]
            else [])
        ++ (if b + 1 == nb then [probeRow wired (sgSt base nb sq (b + 1) 0)
                                              (sgSt base nb sq (b + 1) 1)] else [])
      else
        permBlockRows (sgSt base nb sq b 0) (sgSt base nb sq b 1) (sgSt base nb sq b 2)
          (sgSt base nb sq (b + 1) 0) (sgSt base nb sq (b + 1) 1) (sgSt base nb sq (b + 1) 2)
          (d.perms.getD b [])
        ++ [probeRow wired (sgSt base nb sq (b + 1) 0) (sgSt base nb sq (b + 1) 1)])

/-- A segment's environment. -/
def segEnv (base : Nat) (g : SegSpec) (d : SegData) : VarEnv :=
  let nb := g.nb
  let sq := g.squeezes
  (List.range (g.blocks + 1)).flatMap (fun b =>
    (List.range 3).map (fun j => (sgSt base nb sq b j, ((d.states.getD b []).getD j 0 : Int))))
  ++ (List.range nb).flatMap (fun b =>
      let pre := d.states.getD b []
      (List.range 2).map (fun j =>
        (sgPost base nb sq b j,
         (fAdd (pre.getD j 0) ((g.ws.getD (2 * b + j) (xv 0, 0)).2) : Int))))
  ++ (if g.masked then
        (List.range nb).flatMap (fun b =>
          let pre := d.states.getD b []
          let aft := d.afters.getD b []
          let k := segKeep nb b
          [(sgKeep base nb sq b, (k : Int))]
          ++ (List.range 3).flatMap (fun j =>
              let dv := fSub (aft.getD j 0) (pre.getD j 0)
              [ (sgAfter base nb sq b j, (aft.getD j 0 : Int))
              , (sgD base nb sq b j, (dv : Int))
              , (sgP base nb sq b j, (fMul k dv : Int)) ]))
      else [])

/-- The three segments' shapes, from the committed `StepShape`. -/
def StepShape.frCols (s : StepShape) : Nat := s.cipEvals - EV_PREFIX
/-- Carried bulletproof challenges: two previous proofs × `bRounds` each. -/
def StepShape.optWords (s : StepShape) : Nat := 2 * s.bRounds
/-- `hash_messages_for_next_step_proof`'s field elements: the app state, the 28 plonk-index
commitments as 56 coordinates, the two challenge-polynomial commitments (4 coordinates), and the
unpadded bulletproof challenges. -/
def StepShape.hmWords (s : StepShape) : Nat := 61 + 2 * s.bRounds

def optSpec (s : StepShape) (d : SpongeData) : SegSpec :=
  { ws := (List.range s.optWords).map (fun i =>
      let c := i % s.chals
      (vN s c s.emsRows, chalOf s d c))
  , squeezes := 1, masked := true }

def frSpec (s : StepShape) (dg : PVar × Nat) (ftVal : Nat) : SegSpec :=
  { ws := [ dg, (vEw s 3, evVal 3 1), (vEz s 2, evZOf ftVal 2), (vEw s 2, evVal 2 1) ]
      ++ (List.range s.frCols).flatMap (fun k =>
          [ (vColZ s k, evZOf ftVal (EV_PREFIX + k))
          , (vColW s k, evVal (EV_PREFIX + k) 1) ])
  , squeezes := 2, masked := false }

/-- A deterministic fixture standing for one of the plonk-index / app-state words. -/
def hmVal (i : Nat) : Nat := (13 + 3000017 * i + 5 * i * i) % pN

def hmSpec (s : StepShape) (t : MsmData) (v : IpaData) (d : SpongeData) : SegSpec :=
  { ws := (List.range 57).map (fun i => (vHm s i, hmVal i))
      ++ [ (mpx s (pSum s (s.msmTerms - 2)), (t.sums.getLastD (0, 0)).1)
         , (mpy s (pSum s (s.msmTerms - 2)), (t.sums.getLastD (0, 0)).2)
         , (ipx s (qSum s (s.ipaRounds - 2)), (v.sums.getLastD (0, 0)).1)
         , (ipy s (qSum s (s.ipaRounds - 2)), (v.sums.getLastD (0, 0)).2) ]
      ++ (List.range (2 * s.bRounds)).map (fun i =>
          let c := i % s.chals
          (vN s c s.emsRows, chalOf s d c))
  , squeezes := 1, masked := false }

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
  ft : FtData
  df : DefData
  segA : SegData
  segB : SegData
  segC : SegData
  specA : SegSpec
  specB : SegSpec
  specC : SegSpec
  deriving Inhabited

/-- R6's `ft_eval0`, as a value. -/
def FtData.out (f : FtData) : Nat := f.vals.getD f.fp.slots.ftEval0 0

def mkStep (s : StepShape) : StepData :=
  let sp := runSponge s
  let msm := runMsm s sp
  let ipa := runIpa s sp
  -- ⚑ R6 first: `ft_eval0` is the `ft` column R5's `combined_inner_product` folds.
  let ft := runFt s sp
  let ftv := ft.out
  let specA := optSpec s sp
  let segA := runSeg specA
  let dg : PVar × Nat :=
    (sgSt (baseSegA s) (nbA s) 1 specA.blocks 0,
     (segA.states.getLastD []).getD 0 0)
  let specB := frSpec s dg ftv
  let specC := hmSpec s msm ipa sp
  { sh := s, sp := sp, msm := msm, ipa := ipa, ft := ft, df := runDef s sp ftv
  , segA := segA, segB := runSeg specB, segC := runSeg specC
  , specA := specA, specB := specB, specC := specC }

/-- **R7's rows** — the three sponge segments of §8e. -/
def absRows (t : StepData) (wired : Bool) : List SRow :=
  let s := t.sh
  segRows (baseSegA s) t.specA t.segA wired
  ++ segRows (baseSegB s) t.specB t.segB wired
  ++ segRows (baseSegC s) t.specC t.segC wired

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
  ++ ftRows s t.ft wired
  ++ absRows t wired

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
  -- R6: the compiled ft program's slots.
  ++ aEnvOf (baseFtS s) t.ft.fp.prog t.ft.vals
  -- R7: the three sponge segments and the fixture words of `hash_messages_for_next_step_proof`.
  ++ (List.range N_HM_FIX).map (fun i => (vHm s i, (hmVal i : Int)))
  ++ segEnv (baseSegA s) t.specA t.segA
  ++ segEnv (baseSegB s) t.specB t.segB
  ++ segEnv (baseSegC s) t.specC t.segC

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
  | transcript | challenges | msm | ipa | full | ftEval0 | absorb
  deriving Repr, DecidableEq, Inhabited

def Rung.tag : Rung → String
  | .transcript => "r1_transcript" | .challenges => "r2_challenges" | .msm => "r3_msm"
  | .ipa => "r4_ipa" | .full => "r5_full" | .ftEval0 => "r6_ft_eval0"
  | .absorb => "r7_absorption"

/-- Rung `k`'s rows. -/
def rungRows (t : StepData) (k : Rung) (wired : Bool) : List SRow :=
  let s := t.sh
  let a := transcriptRows s t.sp wired
  let b := (List.range s.chals).flatMap (challengeRows s t.sp wired)
  let c := msmRows s t.msm wired
  let d := ipaRows s t.ipa wired
  let e := deferredRows s wired ++ cipRows s wired ++ closingRows s
  let f := ftRows s t.ft wired
  match k with
  | .transcript => a
  | .challenges => a ++ b
  | .msm => a ++ b ++ c
  | .ipa => a ++ b ++ c ++ d
  | .full => a ++ b ++ c ++ d ++ e
  | .ftEval0 => a ++ b ++ c ++ d ++ e ++ f
  | .absorb => a ++ b ++ c ++ d ++ e ++ f ++ absRows t wired

/-- Rung `k`'s public-input size: 0 below the closing rung, `pubWords` at and above it. -/
def rungPub (s : StepShape) : Rung → Nat
  | .transcript | .challenges | .msm | .ipa => 0
  | _ => s.pubWords

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

/-- A small shape for the fast in-CI pins (the committed one is emitted by the driver).

⚑ `cipEvals` is **47 at both scales** and is no longer free: R6 slices the previous proof's 43
evaluation columns out of it (`EV_PREFIX = 4` + 43), and R7 absorbs those same 43 at two points. A
shape with fewer columns is not a smaller `verify_one`, it is a different one. -/
def shapeSmoke : StepShape :=
  { absorbs := 2, chals := 5, emsRows := 8
  , msmTerms := 3, msmChunks := 26
  , ipaRounds := 3, ipaBlocks := 32
  , bRounds := 3, cipEvals := 47, pubWords := 12 }

/-! ## §12 — the in-CI pins, on the SMOKE instance (`#guard`, interpreter-reduced).

The committed step-scale instance is emitted and PROVED by the harness; these pins run in `lake
build` and cover every structural property the harness cannot see. Nullary `def`s so the interpreter
evaluates the chains ONCE. -/

def tS : StepData := mkStep shapeSmoke
def rowsS : List SRow := rungRows tS .absorb true
def rowsUS : List SRow := rungRows tS .absorb false
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
-- FOUR sponges now: R1's transcript sponge and R7's three absorption segments.
#guard (placedS.filter (fun g => g.kind == KGateType.poseidon)).length
        == 11 * (shapeSmoke.blocks + tS.specA.blocks + tS.specB.blocks + tS.specC.blocks)
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
#guard (rungProbeRows tS .absorb).all (fun r => permLookup pairsS ⟨r, 0⟩ != (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .absorb).all (fun r => permLookup pairsS ⟨r, 1⟩ != (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .absorb).all (fun r => permLookup pairsUS ⟨r, 0⟩ == (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .absorb).all (fun r => permLookup pairsUS ⟨r, 1⟩ == (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .absorb).length ≥ 10

-- ⚑ IT CAN GO RED. Desync ONE mid-chain probe cell and the σ check FAILS, so the `= true` above
-- is a gate rather than a tautology. (`toGrid` is first-wins, so the prepended override lands.)
#guard
  (let probe := (rungProbeRows tS .absorb).getD ((rungProbeRows tS .absorb).length / 2) 0
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

/-! ## §13 — R6: the COMPILED `ft_eval0` against dregg's own verified value layer.

The compiler of §8b is a compiler, not an oracle: every value it produces is pinned here against the
READ-ONLY `KimchiVerify` body it claims to compute, on the SAME inputs, and each pin carries a red
control that bites. The 67 gate constraints are compared **list by list**, so a slip in one body of
one gate cannot be absorbed by the sum. -/

/-- The ft program's slot values at the smoke instance. -/
def ftS : FtData := tS.ft
def ftVal (i : Nat) : Nat := ftS.vals.getD i 0
/-- The ft program's inputs, resolved the way the program resolves them. -/
def ftLkS : PVar → Int := envLookupAt (envIndex (ftInputEnv shapeSmoke tS.sp))
def ftInp (v : PVar) : Nat := (ftLkS v).toNat % pN
def zetaS : Nat := ftInp (vN shapeSmoke shapeSmoke.zetaChal shapeSmoke.emsRows)
def alphaS : Nat := ftInp (vN shapeSmoke shapeSmoke.alphaChal shapeSmoke.emsRows)
def betaS : Nat := ftInp (vN shapeSmoke shapeSmoke.betaChal shapeSmoke.emsRows)
def gammaS : Nat := ftInp (vN shapeSmoke shapeSmoke.gammaChal shapeSmoke.emsRows)
/-- The 43 columns, as the `GateEvals` slicing sees them. -/
def colZ (k : Nat) : ZMod pN := ((evZOf ftS.out (EV_PREFIX + k) : Nat) : ZMod pN)
def colW (k : Nat) : ZMod pN := ((evVal (EV_PREFIX + k) 1 : Nat) : ZMod pN)
def wZ : List (ZMod pN) := (List.range 15).map (fun i => colZ (IDX_W + i))
def wW : List (ZMod pN) := (List.range 15).map (fun i => colW (IDX_W + i))
def coeffZ : List (ZMod pN) := (List.range 15).map (fun i => colZ (IDX_COEFF + i))
def sZ : List (ZMod pN) := (List.range 6).map (fun i => colZ (IDX_S + i))
def mdsS3 : List (List (ZMod pN)) :=
  (List.range 3).map (fun j => (List.range 3).map (fun i => ((FT_MDS9.getD (3 * j + i) 0 : Nat) : ZMod pN)))

/-- The `GateEvals` the linearization constant term is evaluated against — assembled from the SAME
column variables the circuit reads. -/
def gS : Dregg2.Circuit.Emit.KimchiVerify.GateEvals (ZMod pN) :=
  { alpha := (alphaS : ZMod pN), endo := ((FT_ENDO : Nat) : ZMod pN), mds := mdsS3
    coeff := coeffZ, w := wZ, wNext := wW
    cA := ((FT_QUOT.1 : Nat) : ZMod pN), cB := ((FT_QUOT.2.1 : Nat) : ZMod pN)
    cC := ((FT_QUOT.2.2 : Nat) : ZMod pN)
    genSel := colZ (IDX_SEL + 0), posSel := colZ (IDX_SEL + 1)
    caddSel := colZ (IDX_SEL + 2), mulSel := colZ (IDX_SEL + 3)
    emulSel := colZ (IDX_SEL + 4), emulScalarSel := colZ (IDX_SEL + 5) }

-- ⚑ THE CONFIG IS REAL, not decorative. ω is a primitive `2^16`-th root of unity (so `ω^{n−1}` IS
-- the witnessed inverse the circuit derives), the three `EndomulScalar` quotients are the genuine
-- ones, and the endo coefficient is a cube root of unity distinct from 1.
#guard Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) FT_N == (1 : ZMod pN)
#guard Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N / 2) != (1 : ZMod pN)
#guard fMul FT_OMEGA FT_OMEGA_INV == 1
#guard Dregg2.Circuit.Emit.KimchiVerify.endomulScalarConstsOk
        ((FT_QUOT.1 : Nat) : ZMod pN) ((FT_QUOT.2.1 : Nat) : ZMod pN)
        ((FT_QUOT.2.2 : Nat) : ZMod pN)
#guard ((FT_ENDO : Nat) : ZMod pN) ^ 3 == (1 : ZMod pN)
#guard ((FT_ENDO : Nat) : ZMod pN) != (1 : ZMod pN)
#guard FT_MDS9.length == 9
-- ⚑ ALL SIX GATE SELECTORS FIRE. Without this every body but `generic` is multiplied by zero and
-- the six transcriptions rest on a source reading — the exact hazard `MinaWrapFtEval0Weld` §1b
-- named when it found the first fixture with a nonzero `emulSel`.
#guard (List.range 6).all (fun i => colZ (IDX_SEL + i) != 0)

-- ⚑ ω^{n−1}, ω^{n−2}, ω^{n−3} ARE the circuit's derived inverse powers — the reason the rung spends
-- ONE witnessed inverse instead of a 48-row exponentiation, and the reason `zkPoly` is exact.
#guard ((FT_OMEGA_INV : Nat) : ZMod pN)
        == Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N - 1)
#guard ((ftVal ftS.fp.slots.omInv3 : Nat) : ZMod pN)
        == Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N - 3)
-- …and `ζ^n` really is the `log2n`-fold squaring, and `zkPoly` the shipped one.
#guard ((ftVal ftS.fp.slots.zetaN : Nat) : ZMod pN)
        == Dregg2.Bridge.MinaWrapFtEval0.powFast ((zetaS : Nat) : ZMod pN) FT_N
#guard ((ftVal ftS.fp.slots.zkp : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.zkPolyR FT_N
             ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)

-- ⚑ **THE LINEARIZATION CONSTANT TERM.** The compiled six-body sum IS `KimchiVerify.gateLinConst`
-- of the same `GateEvals` — the value `MinaWrapFtEval0Weld` reproduces byte-for-byte on devnet
-- block 539508's Step side (`lct_true = 20345…173047`) and on its Wrap side (`LCT`).
#guard ((ftVal ftS.fp.slots.linConst : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS
-- …and IT BITES: bend ONE input — the `endomul` selector — and the constant term moves.
#guard (((ftVal ftS.fp.slots.linConst : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.gateLinConst
              { gS with emulSel := gS.emulSel + 1 }) == false
-- …and the endo really is load-bearing (the `endoMulConstraints` reader; the cube-root conflation
-- `MinaWrapFtEval0Weld` closed would show HERE).
#guard (((ftVal ftS.fp.slots.linConst : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.gateLinConst
              { gS with endo := gS.endo + 1 }) == false

-- ⚑ **`ft_eval0`.** The compiled fold IS `KimchiVerify.ftEval0R` — the CommRing mirror that is the
-- shipped `ftEval0` for every field (`ftEval0R_eq`, `rfl`) — at the SAME domain, challenges,
-- columns, shifts and constant term, with the witnessed inverse the circuit checks.
#guard
  ((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))
-- ⚑ …and the pin BITES at every leg that could silently drift. β for γ:
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((gammaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))) == false
-- …a bent coset shift (the leg `MinaWrapFtEval0Weld` §6b exhibits on the real block):
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ ((FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN))).set 1
                  (((FT_SHIFTS.getD 1 0 : Nat) : ZMod pN) + 1))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))) == false
-- …and a constant term off by one (so the `gateLinConst` leg is not decoration inside the fold):
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS + 1)
         (((ftS.denomInv : Nat) : ZMod pN))) == false

-- ⚑ THE WITNESSED INVERSE IS THE GENUINE ONE — and the circuit checks it, so a prover who supplies
-- another value is refused by the `denom·denomInv = 1` row rather than believed.
#guard (((zetaS : Nat) : ZMod pN)
          - Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N - 3))
        * (((zetaS : Nat) : ZMod pN) - 1) * ((ftS.denomInv : Nat) : ZMod pN) == (1 : ZMod pN)

-- ⚑ `Plonk_checks.checked` — `derive_plonk`'s `perm` scalar, compiled, against a direct fold of the
-- same six σ evaluations. `checked` asserts exactly this equality against the deferred word, and the
-- rung emits that assertion as a row.
#guard
  ((ftVal ftS.fp.slots.perm : Nat) : ZMod pN)
    == -((List.range 6).foldl
           (fun acc i => acc * (((gammaS : Nat) : ZMod pN)
             + ((betaS : Nat) : ZMod pN) * sZ.getD i 0 + wZ.getD i 0))
           (colW IDX_Z * ((betaS : Nat) : ZMod pN) * (((alphaS : Nat) : ZMod pN) ^ 21)
             * ((ftVal ftS.fp.slots.zkp : Nat) : ZMod pN)))
#guard (((ftVal ftS.fp.slots.perm : Nat) : ZMod pN) == 0) == false

-- ⚑ THE OUTPUT IS WIRED INTO R5's `combined_inner_product`: `ft_eval0` IS the `ft` column the C8
-- fold consumes (`combine ~ft:ft_eval0`, `step_verifier.ml:1078-1083`), so the two rungs share a
-- variable rather than agreeing by construction in Lean only.
#guard tS.df.ez.getD 3 0 == ftS.out
#guard evZOf ftS.out 3 == ftS.out
#guard evZOf ftS.out 3 != evVal 3 0

/-! ### §13a — the SIXTY-SEVEN CONSTRAINT BODIES, list by list.

The pins above check the SUM. These check each compiled body against the `KimchiVerify` list it
mirrors, elementwise, so a compensating pair of slips cannot pass. Each of the six is run through
`aEval` a second time in isolation (the same `ftLkS`), which is why the slot indices below are the
ones the isolated program returns. -/

/-- Compile one body in isolation and read its constraint slots' values. -/
def bodyVals (b : AM (List Nat)) : List (ZMod pN) :=
  let r := b.run #[]
  let vs := aEval ftLkS r.2
  r.1.map (fun i => ((vs.getD i 0 : Nat) : ZMod pN))

/-- The slots every body shares, emitted once at the head of an isolated program. -/
structure WireSlots where
  one : Nat
  negOne : Nat
  three : Nat
  six : Nat
  eleven : Nat
  endo : Nat
  cA : Nat
  cB : Nat
  cC : Nat
  mdsS : List (List Nat)
  coeff : List Nat
  w : List Nat
  wNext : List Nat
  deriving Inhabited

def wireSlots (endoV : Nat) : AM WireSlots := do
  let one ← eLit 1
  let negOne ← eLit (pN - 1)
  let three ← eLit 3
  let six ← eLit 6
  let eleven ← eLit 11
  let endo ← eLit endoV
  let cA ← eLit FT_QUOT.1
  let cB ← eLit FT_QUOT.2.1
  let cC ← eLit FT_QUOT.2.2
  let mdsS ← (List.range 3).foldlM (fun acc j => do
      let row ← (List.range 3).foldlM
        (fun r i => do let v ← eLit (FT_MDS9.getD (3 * j + i) 0); pure (r ++ [v])) []
      pure (acc ++ [row])) []
  let ez ← (List.range 43).foldlM
    (fun acc i => do let v ← eInp (vColZ shapeSmoke i); pure (acc ++ [v])) []
  let ew ← (List.range 43).foldlM
    (fun acc i => do let v ← eInp (vColW shapeSmoke i); pure (acc ++ [v])) []
  pure { one, negOne, three, six, eleven, endo, cA, cB, cC, mdsS
       , coeff := (List.range 15).map (fun i => ez.getD (IDX_COEFF + i) 0)
       , w := (List.range 15).map (fun i => ez.getD (IDX_W + i) 0)
       , wNext := (List.range 15).map (fun i => ew.getD (IDX_W + i) 0) }

def bodyCompleteAdd : AM (List Nat) := do
  let q ← wireSlots FT_ENDO; pCompleteAdd q.one q.w
def bodyVarBaseMul : AM (List Nat) := do
  let q ← wireSlots FT_ENDO; pVarBaseMul q.one q.w q.wNext
def bodyEndoMul (endoV : Nat) : AM (List Nat) := do
  let q ← wireSlots endoV; pEndoMul q.one q.endo q.w q.wNext
def bodyEmScalar : AM (List Nat) := do
  let q ← wireSlots FT_ENDO
  pEmScalar q.cA q.cB q.cC q.negOne q.three q.six q.eleven q.w
def bodyPoseidon : AM (List Nat) := do
  let q ← wireSlots FT_ENDO; pPoseidon q.mdsS q.coeff q.w q.wNext

#guard bodyVals bodyCompleteAdd
        == Dregg2.Circuit.Emit.KimchiVerify.completeAddConstraints wZ
#guard bodyVals bodyVarBaseMul
        == Dregg2.Circuit.Emit.KimchiVerify.varBaseMulConstraints wZ wW
#guard bodyVals (bodyEndoMul FT_ENDO)
        == (Dregg2.Circuit.Emit.KimchiVerify.endoMulConstraints
              ((FT_ENDO : Nat) : ZMod pN) wZ wW).take 11
#guard bodyVals bodyEmScalar
        == Dregg2.Circuit.Emit.KimchiVerify.endomulScalarConstraints
             ((FT_QUOT.1 : Nat) : ZMod pN) ((FT_QUOT.2.1 : Nat) : ZMod pN)
             ((FT_QUOT.2.2 : Nat) : ZMod pN) wZ
#guard bodyVals bodyPoseidon
        == Dregg2.Circuit.Emit.KimchiVerify.poseidonConstraints mdsS3 coeffZ wZ wW
-- …and the list-by-list pins BITE: a bent `endo` moves the `EndosclMul` list.
#guard (bodyVals (bodyEndoMul (FT_ENDO + 1))
         == (Dregg2.Circuit.Emit.KimchiVerify.endoMulConstraints
               ((FT_ENDO : Nat) : ZMod pN) wZ wW).take 11) == false
-- …and none of the five lists is all-zero (a body that vanished would match a wrong transcription).
#guard (Dregg2.Circuit.Emit.KimchiVerify.varBaseMulConstraints wZ wW).any (fun z => z != 0)
#guard (Dregg2.Circuit.Emit.KimchiVerify.poseidonConstraints mdsS3 coeffZ wZ wW).any (fun z => z != 0)

/-! ## §14 — R7: the EVALUATION ABSORPTION.

The three segments' arithmetic, against `PastaPoseidon.Ref.perm` — the same reference whose
`Ref.hash` reproduces the o1js `Poseidon.hash` gold KATs, and the same one R1's sponge answers to. -/

#guard tS.specB.ws.length == 4 + 2 * (shapeSmoke.cipEvals - EV_PREFIX)
#guard tS.specB.ws.length == 90
#guard tS.specA.ws.length == 2 * shapeSmoke.bRounds
#guard tS.specC.ws.length == shapeSmoke.hmWords
#guard tS.specA.nb == nbA shapeSmoke
#guard tS.specB.nb == nbB shapeSmoke
#guard tS.specC.nb == nbC shapeSmoke

-- ⚑ EVERY SEGMENT IS THE REAL SPONGE: each block's output is `Ref.perm` of its absorbed input,
-- EXCEPT where the opt-sponge MASK discards it — and that exception is exactly the masked blocks.
#guard (List.range tS.specB.blocks).all (fun b =>
  let pre := tS.segB.states.getD b []
  let post := if b < tS.specB.nb then
      [ fAdd (pre.getD 0 0) ((tS.specB.ws.getD (2 * b) (xv 0, 0)).2)
      , fAdd (pre.getD 1 0) ((tS.specB.ws.getD (2 * b + 1) (xv 0, 0)).2), pre.getD 2 0 ]
    else pre
  tS.segB.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)
#guard (List.range tS.specC.blocks).all (fun b =>
  let pre := tS.segC.states.getD b []
  let post := if b < tS.specC.nb then
      [ fAdd (pre.getD 0 0) ((tS.specC.ws.getD (2 * b) (xv 0, 0)).2)
      , fAdd (pre.getD 1 0) ((tS.specC.ws.getD (2 * b + 1) (xv 0, 0)).2), pre.getD 2 0 ]
    else pre
  tS.segC.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)

-- ⚑ THE MASK IS A MASK, BOTH WAYS. A `keep = 1` block advances to the permutation output; a
-- `keep = 0` block leaves the state EXACTLY where it was — `Field.if_` on all three lanes
-- (`step_verifier.ml:998-1003`). Both branches occur, so neither is untested.
#guard (List.range tS.specA.nb).all (fun b =>
  if segKeep tS.specA.nb b == 1
  then tS.segA.states.getD (b + 1) [] == tS.segA.afters.getD b []
  else tS.segA.states.getD (b + 1) [] == tS.segA.states.getD b [])
#guard (List.range tS.specA.nb).any (fun b => segKeep tS.specA.nb b == 1)
#guard (List.range tS.specA.nb).any (fun b => segKeep tS.specA.nb b == 0)
-- …and a masked-out block's DISCARDED permutation output is genuinely different from the state it
-- keeps, so the mux is deciding something.
#guard (List.range tS.specA.nb).all (fun b =>
  segKeep tS.specA.nb b == 1 || tS.segA.afters.getD b [] != tS.segA.states.getD b [])

-- ⚑ SEGMENT B ABSORBS R5's AND R6's OWN VARIABLES: the digest of segment A, `ft_eval1`, the two
-- public-polynomial evaluations, then the 43 columns at ζ and ζω INTERLEAVED
-- (`to_absorption_sequence`, `step_verifier.ml:967-1005`) — the same `vEz`/`vEw` the C8 fold and the
-- `ft_eval0` rung read. Not a private stream.
#guard (tS.specB.ws.getD 0 (xv 0, 0)).1
        == sgSt (baseSegA shapeSmoke) (nbA shapeSmoke) 1 tS.specA.blocks 0
#guard (tS.specB.ws.getD 0 (xv 0, 0)).2 == (tS.segA.states.getLastD []).getD 0 0
#guard (tS.specB.ws.getD 1 (xv 0, 0)).1 == vEw shapeSmoke 3
#guard (List.range shapeSmoke.frCols).all (fun k =>
  (tS.specB.ws.getD (4 + 2 * k) (xv 0, 0)).1 == vColZ shapeSmoke k
  && (tS.specB.ws.getD (5 + 2 * k) (xv 0, 0)).1 == vColW shapeSmoke k)
-- …and segment A absorbs R2's challenges, segment C R3's and R4's fold outputs.
#guard (List.range tS.specA.ws.length).all (fun i =>
  (tS.specA.ws.getD i (xv 0, 0)).1 == vN shapeSmoke (i % shapeSmoke.chals) shapeSmoke.emsRows)
#guard (tS.specC.ws.getD N_HM_FIX (xv 0, 0)).1
        == mpx shapeSmoke (pSum shapeSmoke (shapeSmoke.msmTerms - 2))
#guard (tS.specC.ws.getD (N_HM_FIX + 2) (xv 0, 0)).1
        == ipx shapeSmoke (qSum shapeSmoke (shapeSmoke.ipaRounds - 2))

-- ⚑ THE SPONGE IS NOT DEGENERATE: the three digests differ from each other and from zero, so a
-- sponge that silently absorbed nothing would show.
#guard (tS.segA.states.getLastD []).getD 0 0 != 0
#guard (tS.segB.states.getLastD []).getD 0 0 != 0
#guard (tS.segC.states.getLastD []).getD 0 0 != 0
#guard (tS.segA.states.getLastD []).getD 0 0 != (tS.segB.states.getLastD []).getD 0 0
#guard (tS.segB.states.getLastD []).getD 0 0 != (tS.segC.states.getLastD []).getD 0 0

/-! ## §15 — the LADDER is monotone and the new rungs really add their sub-circuit. -/

#guard (rungRows tS .full true).length < (rungRows tS .ftEval0 true).length
#guard (rungRows tS .ftEval0 true).length < (rungRows tS .absorb true).length
-- R6 is `Generic`-only (it is scalar arithmetic; every other gate family is unchanged by it).
#guard ((rungRows tS .ftEval0 true).drop (rungRows tS .full true).length).all
        (fun r => r.kind == KGateType.generic || r.kind == KGateType.zero)
-- R7 adds `Poseidon` and nothing else new: 11 rows per permutation, upstream's own run length.
#guard ((rungRows tS .absorb true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * (shapeSmoke.blocks + tS.specA.blocks + tS.specB.blocks + tS.specC.blocks)
#guard ((rungRows tS .full true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * shapeSmoke.blocks
-- …and the compiled ft program is a real program, not a stub.
#guard ftS.fp.prog.size ≥ 900
#guard (aHalfSlots ftS.fp.prog).length ≥ 700

end Dregg2.Circuit.Emit.KimchiStepMain
