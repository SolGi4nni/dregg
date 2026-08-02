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
  * **R5 `deferred` + `xi` + `cip` + `closing`** — two of `finalize_other_proof`'s deferred words:
    `b(ζ) = ∏(1 + uᵢ·ζ^{2^{k−1−i}})` (`Wrap.challenge_polynomial`, `wrap.ml:15-17`; the product
    `KimchiVerify.bEvalSq` folds) and `combined_inner_product = Σ_k ξ^k·(evₖ(ζ) + r·evₖ(ζω))`
    (`Common.combined_evaluation`, the `2 × cipEvals` `mul_and_add`s; pinned against
    `KimchiVerify.combinedInnerProduct`, transcribed READ-ONLY from `verifier.rs`) — both as
    `Generic` chains over the CHALLENGE variables. ⚑ Its ξ is §8g's chain 0: a full
    `to_field_checked` of the STATEMENT's ξ word (`let xi = scalar xi`, `step_verifier.ml:1012`),
    the word R8's `xi_correct` ties to the fr-sponge. Then the closing tie of every one of the
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
  * **R7 `absorption`** — the fr-sponge (`step_verifier.ml:950-1013`, `step_main.ml:525-567`): an
    OPT-SPONGE over the carried bulletproof challenges with a per-block `keep` MASK (the `Field.if_`
    state mux, `:998-1003`), the **43 evaluation columns absorbed at ζ and ζω** in
    `to_absorption_sequence` order, the ξ′/r′ squeezes, `hash_messages_for_next_step_proof`, and
    ⚑ §8g's chain 1 — `to_field_checked` of the SECOND squeeze, which IS the `r` the C8 fold and
    `b_correct` multiply by (`let r = scalar (Scalar_challenge.create r_actual)`, `:1013`).
  * **R8 `finalize`** — ⚑ `finalize_other_proof`'s TAIL, the rung at which the deferred values stop
    being computed and start BINDING (`step_verifier.ml:1076-1147`, `step_main.ml:121,522`): the
    second challenge polynomial at `ζω = domain#generator·ζ` so `b_actual = challenge_poly ζ +
    r·challenge_poly ζω`; the **three `Shifted_value.Type1.to_field` unshifts** of the statement's
    `combined_inner_product`, `b` and `plonk.perm` (Type1 over **`Fp`** — the value's own field, see
    §8f); `xi_correct` against the fr-sponge's own squeeze; and `Boolean.all [xi_correct; b_correct;
    combined_inner_product_correct; plonk_checks_passed]` behind the `should_verify` mux, ASSERTED.
    The four statement words are the **first four public words**, so a prover who claims a different
    deferred value is refused rather than believed.

## ⚑ THE SHAPE ORACLE — MEASURED against Mina's own compiled step circuit

o1-labs publishes Mina's compiled circuits as `*_gates.json` release blobs (kimchi's
`Circuit { public_input_size, gates }` serde form; `bridge/mina-zkapp/scripts/
mina-canonical-circuit-oracle.mjs`, whose digest reproduces the md5 in o1-labs' own asset filename).
**`step-zkapp-proved` is branch 4 — the step branch that RUNS `verify_one` on a side-loaded proof**:
PI 67, 20,023 gates, 13,778 non-Generic. Measured against this file's `shapeStep` (2026-08-02):

    gate         Mina step-zkapp-proved  r5_full  r6_ft_eval0  r7_absorb  r8_finalize  run-lengths
    total gates         20023              6602      7071        8616        8681
    non-Generic         13778              6206      6208        7559        7562
    Poseidon             6292 (31.4%)      1034      1034        2266        2266   11×572 / 11×206 ✓
    Generic              6245 (31.2%)       396       863        1057        1119   —
    EndoMul              2465 (12.3%)      2432      2432        2432        2432   32×77+1×1 / 32×76 ✓
    Zero                 2246 (11.2%)      1456      1458        1577        1580   —
    VarBaseMul           1596  (8.0%)       988       988         988         988   1×1596 / 1×988    ✓
    EndoMulScalar         776  (3.9%)       184       184         184         184   / 8×23 — upstream
                    also runs 2×42 8×28 4×25 16×3 1×2 12×2 32×2 9×1 19×1 22×1 24×1 28×1 128×1
    CompleteAdd           403  (2.0%)       112       112         112         112   1×159 2×65 3×23
                    15×1 30×1 / 1×112

The RUN LENGTHS are the fidelity signal, and all six families are unchanged by R6/R7/R8: a `Poseidon`
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

The remaining `Generic` gap (1119 vs 6245) is therefore NOT one missing sub-circuit. It is: the zkApp
branch's own `rule.main` application logic (which is not `verify_one` at all), the per-challenge
`lowest_128_bits ~constrain_low_bits:true` range checks (#1 below), the `sg_evals` prefix of the two
`combine`s (#4), `equal_g`, `group_map`, `x_hat blinding` and the domain selection. #1–#11 below name
them. ⚑ R8 spends 62 `Generic` rows on `finalize_other_proof`'s tail and 24 of the +86 since
2026-08-01 are R2's endo lift — cheap rows that RETIRE two named simplifications rather than add
scale, which is the trade this file is supposed to be making.

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
  4. ⚑ **RETIRED 2026-08-02, and the ORIGINAL CLAIM WAS WRONG.** This entry read "`combined_inner_
     product` is HALF of upstream's — R5 assembles ONE ξ-Horner fold (at ζ)". READ AT SOURCE, R5's
     `cipRows` folds `cₖ = evₖ(ζ) + r·evₖ(ζω)` and then Horners over ξ, i.e.
     `Σₖ ξᵏ(ez_k + r·ew_k)` — which IS `combine(ζ) + r·combine(ζω)` term-for-term, and IS
     `KimchiVerify.cipR`'s own body. The r-weighted second fold was never absent; it was folded per
     COLUMN instead of per POINT. What WAS absent is now R8: `b_correct`'s `+ r·challenge_poly ζω`
     leg and the `Shifted_value.Type1.to_field` unshifts. **Still open:** the `sg_evals` prefix
     entries (`vEz 0/1`, `vEw 0/1`) are `evVal` fixtures where upstream puts the b-polynomial of the
     CARRIED old bulletproof challenges, masked by `Vector.trim_front actual_width_mask` — so the
     two `combine`s' first two v-entries are not yet computed from the carried challenges.
  5. **Named and NOT assembled**, each a real sub-circuit: `group_map` (`step_verifier.ml:214-237`);
     `equal_g` and the `check_bulletproof` tail's `scale_fast` of `sg`; the real `sponge_after_index`
     (the plonk index is hashed here from 57 FIXTURE words, not from the actual commitments);
     `x_hat blinding`; `lagrange_commitment` / `public_input_commitment_dynamic`'s domain selection;
     `actual_evaluation`'s per-column chunk Horner (`combined_evals`; our columns are single-chunk,
     though `ζ^n = pow2_pow ζ 16` IS assembled in R6); `Evals.validate_feature_flags`; and the
     app-logic `rule.main`. (`xi_correct`, the `Boolean.all` finalisation and its assert, and the
     `should_verify` mux left this list on 2026-08-02 — they are R8.)
  6. Every challenge is derived at ONE width (128 bits, 8 `EndoMulScalar` rows). Upstream also uses
     16/32/64/192/256-bit `to_field_checked` (the 1/2/4/12/16-row runs in the table).
  7. ⚑ **RETIRED 2026-08-02.** `to_field_checked` is the `EndoMulScalar` chain, then
     `Field.Assert.equal n scalar`, then **`Field.(scale a endo + b)`** (`scalar_challenge.ml:125-129`)
     — R2 emitted the first two and stopped. It now emits the third: ONE `Generic` row per challenge
     turning the chain's own `a₈`/`b₈` cells into `vLift c`, pinned in §16 against
     `KimchiVerify.endoMap ENDO_R` with the `FT_ENDO`-for-`endo_r` cube-root conflation as its red
     control. `plonk.zeta`/`plonk.alpha` (R6), the deferred ξ/r (R5's `combined_inner_product`) and
     every bulletproof challenge (R5's and R8's `challenge_polynomial`) now read the LIFTED value;
     β/γ stay raw, which is upstream's own split (`map_challenges ~f:Fn.id ~scalar`).
  8. ⚑ **RETIRED 2026-08-02.** R6's seven coset shifts were `FT_SHIFTS`, distinct nonzero fixtures.
     `FT_SHIFTS` is now **`TickShifts.tickShiftsFp 16`** — the `Shifts::new` Blake2b→field
     construction (`permutation.rs:149-197`), `#guard`-pinned in `Dregg2/Bridge/TickShifts.lean`
     byte-exact against o1-labs' own `Shifts::new(Radix2EvaluationDomain::<Fp>::new(2^16))` output.
     §13 re-states the identity at the point of use, checks the structure the derivation guarantees
     (`shifts[0] = 1`, six distinct QNRs outside the domain), and carries the RED CONTROL that makes
     it a retirement rather than a rename: `FT_SHIFTS_WERE_FIXTURES` gives a DIFFERENT `ft_eval0` at
     the same wire, as does a one-unit bend in any derived shift.
  9. R7's opt-sponge mask is a fixed `keep` pattern (the first half of the blocks kept), standing for
     `branch_data.proofs_verified_mask` / `Vector.trim_front actual_width_mask`. The mask VARIABLE is
     in the circuit and both branches occur; what is not here is deriving it from `branch_data`.
     ⚑ The missing piece is small and named: `branch_data` is ONE field element packing
     `4·domain_log2 + pack(mask)` (`branch_data.ml:95-101`), so retiring this is a statement word,
     an unpack row, booleanity + prefix-mask rows (`Proofs_verified.Prefix_mask`), and aliasing
     `sgKeep` to the two mask bits. It is not blocked on a sub-circuit that does not exist.
 10. ⚑ **RETIRED 2026-08-02 — the fr-sponge now FEEDS the fold, not merely gets checked against it.**
     This entry read: "the ξ/r the C8 fold multiplies by are R1's transcript challenges, not
     `endoMap` of R7's squeeze… R8's `xi_correct` binds the STATEMENT's ξ to the fr-sponge squeeze
     but does not yet make that word the fold's own multiplier." §8g is that multiplier. READ AT
     SOURCE (`step_verifier.ml:1006-1013`), upstream is a TWO-STEP, and the two multipliers have
     DIFFERENT provenance: `xi = scalar xi` lifts the STATEMENT's ξ word (the one `xi_correct` ties
     to the first squeeze), while `r = scalar (Scalar_challenge.create r_actual)` lifts the SECOND
     squeeze directly and has no statement word at all. Both are now real `to_field_checked` chains
     — 8 `EndoMulScalar` rows, the tie to their source, the endo lift — and `cipRows`/`b_correct`
     multiply by their outputs. The red control BITES: bending either squeeze by one moves
     `combined_inner_product` and `b_actual`, which it could not do before (§12a, §16b).
     ⚠ THE HONEST RESIDUE, pinned in §15: ξ's source is a statement word so its chain rides with R5
     and binds from `r5_full` up; `r`'s source is an R7 variable, so at r5/r6 — sub-circuits strictly
     below the fr-sponge — the fold's `r` is a free witness, and it binds at r7/r8. That is the
     ladder position `vEz 3` (R6's `ft_eval0`) and the four statement words already occupy.
 11. R8's `verified` bit (the kimchi `verify` result the mux ANDs with `finalized`) is a witnessed
     boolean, booleanity-constrained and nothing else. ⚑ **NOT RETIRABLE WITHOUT A SUB-CIRCUIT THAT
     DOES NOT EXIST.** `verified` is `Step_verifier.verify` (`step_main.ml:88-107`) — the whole wrap
     kimchi verifier: `check_bulletproof` (`equal_g`, the `scale_fast` of `sg`, the IPA fold), the
     `x_hat`/`ft_comm` commitment MSMs against REAL commitments, `group_map`, and
     `sponge_after_index` over the actual plonk index. Those are #3 and #5's named-and-not-assembled
     list. Deriving the bit from anything less would be a value that LOOKS derived; the honest state
     is the witness plus this sentence.

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
import Dregg2.Bridge.TickShifts

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

/-! ### The `to_field_checked` OUTPUT (`scalar_challenge.ml:125-129`).

`to_field_checked` is the `EndoMulScalar` chain, then `Field.Assert.equal n scalar`, then
**`Field.(scale a endo + b)`** — the endomorphism LIFT of the prechallenge. R2 emitted the first two
and stopped; these are the variables of the third, so `vLift c` IS `ScalarChallenge::to_field`
(`KimchiVerify.endoMap ENDO_R`) of the squeeze and the chain's `a₈`/`b₈` cells become load-bearing
rather than merely constrained. -/
def baseLift (s : StepShape) : Nat := baseHi s + s.chals
/-- `a₈ · endo_r` — the lift's product half. -/
def vLiftT (s : StepShape) (c : Nat) : PVar := xv (baseLift s + c)
/-- ⚑ **The LIFTED challenge** `a₈·endo_r + b₈`. This is what `plonk.zeta`/`plonk.alpha`, the
deferred `ξ`/`r` and every bulletproof challenge ARE upstream; the raw `vN c emsRows` is the
prechallenge the curve gadgets consume. -/
def vLift (s : StepShape) (c : Nat) : PVar := xv (baseLift s + s.chals + c)
/-- `Endo.Wrap_inner_curve.scalar`, pinned by one `Generic` row and shared by every lift. -/
def vEndoR (s : StepShape) : PVar := xv (baseLift s + 2 * s.chals)

def baseMsm (s : StepShape) : Nat := baseLift s + 2 * s.chals + 1
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

/-! ### The STATEMENT words R8 binds (§8f).

Upstream these are the Wrap proof-state's `Deferred_values` — `combined_inner_product`, `b` and
`plonk.perm` in `Shifted_value.Type1` form, and the `Scalar_challenge` `xi` — carried in the step
circuit's statement and CHECKED against what the circuit recomputes. They are exposed as the first
four public words, so a prover who supplies a different deferred value is refused by R8's
`Boolean.all` assert rather than believed. ⚠ In rungs r5–r7 (below the rung that checks them) they
are statement inputs and nothing else; r8 is the rung that binds them. -/
def baseStmt (s : StepShape) : Nat := baseSegC s + segVarCount (nbC s) 1
/-- `combined_inner_product`, `Shifted_value.Type1`. -/
def vCipShift (s : StepShape) : PVar := xv (baseStmt s)
/-- `b`, `Shifted_value.Type1`. -/
def vBShift (s : StepShape) : PVar := xv (baseStmt s + 1)
/-- `plonk.perm`, `Shifted_value.Type1` (`Plonk_checks.checked` compares the SHIFTED words). -/
def vPermShift (s : StepShape) : PVar := xv (baseStmt s + 2)
/-- `xi`'s RAW prechallenge — `xi_correct` compares it against the fr-sponge's own squeeze, and
§8g's chain `0` LIFTS it into the multiplier the C8 fold uses. -/
def vXiStmt (s : StepShape) : PVar := xv (baseStmt s + 3)
def N_STMT : Nat := 4

/-! ### The DEFERRED challenges ξ and r (§8g) — the fold's own multipliers.

`step_verifier.ml:1006-1013`, verbatim:

    let squeeze () = squeeze_challenge sponge in
    let xi_actual = squeeze () in
    let r_actual  = squeeze () in
    let xi_correct = Field.equal xi_actual (match xi with { inner = xi } -> xi) in
    let xi = scalar xi in
    let r  = scalar (Import.Scalar_challenge.create r_actual) in

so the ξ the C8 fold multiplies by is `to_field_checked` of **the statement's ξ word** — the word
`xi_correct` ties to the fr-sponge's FIRST squeeze — and the `r` it (and `b_correct`) multiplies by
is `to_field_checked` of the fr-sponge's **SECOND squeeze**, with no statement word at all. Each
gets its own `to_field_checked` chain; chain `0` is ξ and chain `1` is r. ⚑ This is the retirement
of the module header's simplification #10: before it, both were R1 transcript challenges and the
fr-sponge squeeze fed NOTHING but `xi_correct`. -/
def N_DEFC : Nat := 2
/-- One deferred chain's variable block: `n/a/b` at every `EndoMulScalar` row boundary, the
`lowest_128_bits` high part, and the lift's two cells. -/
def defcStride (s : StepShape) : Nat := 3 * (s.emsRows + 1) + 3
def baseDefC (s : StepShape) : Nat := baseStmt s + N_STMT
def vDN (s : StepShape) (c k : Nat) : PVar := xv (baseDefC s + c * defcStride s + k)
def vDA (s : StepShape) (c k : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + (s.emsRows + 1) + k)
def vDB (s : StepShape) (c k : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 2 * (s.emsRows + 1) + k)
/-- The discarded high part. Chain `0` has none — its source is already a `Challenge.t`. -/
def vDHi (s : StepShape) (c : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 3 * (s.emsRows + 1))
def vDLiftT (s : StepShape) (c : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 3 * (s.emsRows + 1) + 1)
/-- ⚑ **THE FOLD'S OWN MULTIPLIER.** `vDLift 0` is ξ and `vDLift 1` is r: the variables `cipRows`
Horners over and scales its `evₖ(ζω)` leg by, and the one `b_correct` weights `challenge_poly ζω`
with. Nothing else in the assembly plays those two roles. -/
def vDLift (s : StepShape) (c : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 3 * (s.emsRows + 1) + 2)

def baseFtS (s : StepShape) : Nat := baseDefC s + N_DEFC * defcStride s

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

/-- ⚑ `Endo.Wrap_inner_curve.scalar` (`endo.ml:7`) — the SCALAR-challenge endomorphism of `Fp`, the
constant `to_field_checked` scales `a₈` by. NOT `FT_ENDO`, which is the BASE endomorphism
`5^((p−1)/3)` the linearization reads; conflating the two cube roots is the defect
`MinaWrapFtEval0Weld` closed, and §16's red control shows it here. -/
def ENDO_R : Nat :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

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

/-- The `(a₈, b₈)` accumulators and the LIFT `a₈·endo_r + b₈` of a 128-bit prechallenge. -/
def liftVal (s : StepShape) (v : Nat) : Nat :=
  let a := (emsAccs s v).getD s.emsRows (0, 2, 2)
  fAdd (fMul a.2.1 ENDO_R) a.2.2
def liftTVal (s : StepShape) (v : Nat) : Nat :=
  fMul ((emsAccs s v).getD s.emsRows (0, 2, 2)).2.1 ENDO_R
/-- …of transcript challenge `c`. -/
def liftOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat := liftVal s (chalOf s d c)
def liftTOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat := liftTVal s (chalOf s d c)

/-- The one row that pins `endo_r`, emitted once ahead of the challenge chains. Every
`to_field_checked` chain in the assembly — R2's `chals` and §8g's two deferred ones — shares it. -/
def endoConstRow (s : StepShape) : List SRow :=
  [ genericRow (some (vEndoR s)) none none none none none (cConst (ENDO_R : Int) ++ cNil) ]

/-- One `to_field_checked` chain's variable block, so the SAME row emitter serves R2's transcript
challenges and §8g's deferred ξ/r. -/
structure ChalVars where
  n : Nat → PVar
  a : Nat → PVar
  b : Nat → PVar
  hi : PVar
  liftT : PVar
  lift : PVar

def r2Vars (s : StepShape) (c : Nat) : ChalVars :=
  { n := vN s c, a := vA s c, b := vB s c, hi := vHi s c
  , liftT := vLiftT s c, lift := vLift s c }
def defcVars (s : StepShape) (c : Nat) : ChalVars :=
  { n := vDN s c, a := vDA s c, b := vDB s c, hi := vDHi s c
  , liftT := vDLiftT s c, lift := vDLift s c }

/-- **`to_field_checked`'s rows** over a 128-bit prechallenge `v` (`scalar_challenge.ml:12-129`):
`n₀=0, a₀=2, b₀=2` pinned by `Generic` rows, `emsRows` chained `EndoMulScalar` rows, the tie of the
chain's reconstructed `n₈` back to its SOURCE, and the closing lift `Field.(scale a endo + b)`.

`split = true` — the source is a FULL field element (a sponge squeeze), so the tie is the
`lowest_128_bits` decomposition `src = n₈ + 2^chalBits·hi`. `split = false` — the source is already
a `Challenge.t` (§8g's statement ξ word), so the tie is `Field.Assert.equal n scalar` (`:124`) and
the chain's `hi` cell is not allocated by any row. -/
def tfcRows (s : StepShape) (cv : ChalVars) (src : PVar) (split : Bool) (v : Nat)
    (wired : Bool) : List SRow :=
  let cr := crumbsOf s v
  [ genericRow (some (cv.n 0)) none none (some (cv.a 0)) none none (cConst 0 ++ cConst 2)
  , genericRow (some (cv.b 0)) none none none none none (cConst 2 ++ cNil) ]
  ++ (List.range s.emsRows).map (fun k =>
      ({ kind := .endoMulScalar
       , perm := [ some (cv.n k), some (cv.n (k+1)), some (cv.a k), some (cv.b k)
                 , some (cv.a (k+1)), some (cv.b (k+1)), none ]
       , advice := (List.range 8).map (fun j => (6 + j, (cr.getD (8 * k + j) 0 : Int)))
                   ++ [(14, 0)] } : SRow))
  ++ [ (if split then
          genericRow (some src) (some cv.hi) (some (cv.n s.emsRows)) none none none
                     (cSplit s.chalBits ++ cNil)
        else
          genericRow (some (cv.n s.emsRows)) (some src) none none none none (cEq ++ cNil))
     -- ⚑ `to_field_checked`'s CLOSING LINE: `Field.(scale a endo + b)`. Two halves of one row, and
     -- the `a₈`/`b₈` cells the `EndoMulScalar` chain produced now carry a value the rest of the
     -- assembly reads.
     , genericRow (some (cv.a s.emsRows)) (some (vEndoR s)) (some cv.liftT)
                  (some cv.liftT) (some (cv.b s.emsRows)) (some cv.lift) (cMul ++ cAdd)
     , probeRow wired (cv.n s.emsRows) (cv.a s.emsRows)
     , probeRow wired cv.lift (cv.b s.emsRows) ]

/-- **R2's rows** for challenge `c` — `tfcRows` at the transcript sponge's own squeeze. -/
def challengeRows (s : StepShape) (d : SpongeData) (wired : Bool) (c : Nat) : List SRow :=
  tfcRows s (r2Vars s c) (vSt s (s.absorbs + c + 1) 0) true (chalOf s d c) wired

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

/-- ⚑ `xi` and `rr` are the DEFERRED multipliers of §8g — `to_field_checked` of the statement's ξ
word and of the fr-sponge's second squeeze — NOT transcript challenges. The fold is `fed` by the
squeeze, not merely checked against it. -/
def runDef (s : StepShape) (d : SpongeData) (ftVal : Nat) (xi rr : Nat) : DefData :=
  let zs := (List.range s.bRounds).foldl
    (fun acc _ => let x := acc.getLastD 0; acc ++ [fMul x x]) [liftOf s d 0]
  let st := (List.range s.bRounds).foldl
    (fun (acc : List Nat × List Nat) k =>
      let f := fAdd 1 (fMul (liftOf s d (k + 1)) (zs.getD (s.bRounds - 1 - k) 0))
      (acc.1 ++ [f], acc.2 ++ [fMul (acc.2.getLastD 1) f]))
    ([], [1])
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
  , genericRow (some (vZ s 0)) (some (vLift s 0)) none none none none (cEq ++ cNil) ]
  ++ (List.range s.bRounds).map (fun k =>
      genericRow (some (vZ s k)) (some (vZ s k)) (some (vZ s (k+1))) none none none (cMul ++ cNil))
  ++ (List.range s.bRounds).map (fun k =>
      genericRow (some (vLift s (k+1))) (some (vZ s (s.bRounds - 1 - k))) (some (vFac s k))
                 (some (vAcc s k)) (some (vFac s k)) (some (vAcc s (k+1))) (cMulPlus1 ++ cMul))
  ++ [ probeRow wired (vAcc s s.bRounds) (vZ s s.bRounds) ]

/-- **R5a', `combined_inner_product`** — `Common.combined_evaluation` (`common.ml:258-…`), the
`2 × cipEvals` `mul_and_add`s. `cip = Σ_k ξ^k · (evₖ(ζ) + r · evₖ(ζω))`, assembled as a Horner fold
from the top over `Generic` rows, two per evaluation column:

    A(k)  half1  w₀=r      w₁=evₖ(ζω)  w₂=dₖ      dₖ = r · evₖ(ζω)
          half2  w₃=evₖ(ζ) w₄=dₖ       w₅=cₖ      cₖ = evₖ(ζ) + dₖ
    B(i)  half1  w₀=accᵢ   w₁=ξ        w₂=tᵢ      tᵢ = accᵢ · ξ
          half2  w₃=tᵢ     w₄=c_{n−1−i} w₅=accᵢ₊₁ accᵢ₊₁ = tᵢ + c_{n−1−i}

⚑ ξ and `r` are `vDLift 0` / `vDLift 1` — §8g's DEFERRED challenges, `to_field_checked` of the
statement's ξ word and of the fr-sponge's second squeeze (`step_verifier.ml:1012-1013`). Every
`Generic` half of this fold therefore hangs off the fr-sponge through σ, which is the retirement of
simplification #10. -/
def cipRows (s : StepShape) (wired : Bool) : List SRow :=
  [ genericRow (some (vCa s 0)) none none none none none (cConst 0 ++ cNil) ]
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [ genericRow (some (vDLift s 1)) (some (vEw s k)) (some (vDk s k))
                   (some (vEz s k)) (some (vDk s k)) (some (vCk s k)) (cMul ++ cAdd) ])
  ++ (List.range s.cipEvals).flatMap (fun i =>
      [ genericRow (some (vCa s i)) (some (vDLift s 0)) (some (vTk s i))
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
/-- ⚑ **The SEVEN TICK COSET SHIFTS, DERIVED** — `TickShifts.tickShiftsFp 16`, the `Shifts::new`
Blake2b→field construction over the Step field, `#guard`-pinned THERE byte-exact against o1-labs'
own `Shifts::new(Radix2EvaluationDomain::<Fp>::new(2^16))` output. This is what `Plonk_checks`
`ft_eval0`'s denominator fold really runs on; §13 re-states the byte-exact identity here and shows
the OLD fixtures move `ft_eval0`. (Retires the module header's simplification #8.) -/
def FT_SHIFTS : List Nat := (Dregg2.Bridge.TickShifts.tickShiftsFp 16).map (fun x => x.val)

/-- The seven distinct nonzero placeholders the rung used BEFORE the derivation was wired in. Kept
for exactly one purpose: §13's red control, which shows they give a DIFFERENT `ft_eval0`. Nothing
emits them. -/
def FT_SHIFTS_WERE_FIXTURES : List Nat :=
  (List.range 7).map (fun i => (1 + 7919 * (i + 1) * (i + 3)) % pN)
/-- The linearization's `Constants::mds` IS `Vesta::sponge_params().mds = fp_kimchi` (`curve.rs:63`),
i.e. K3's own `PastaPoseidon.mdsN` — the same nine constants the sponge rung R1 permutes with. -/
def FT_MDS9 : List Nat := Dregg2.Circuit.Emit.PastaPoseidon.mdsN.flatten

/-- The ft program's `.inp` lookup: the challenges and the 43 columns, straight from the chains. It
does NOT read column 3, so the `ft` override below is not circular. -/
def ftInputEnv (s : StepShape) (d : SpongeData) : VarEnv :=
  (List.range s.chals).map (fun c => (vN s c s.emsRows, (chalOf s d c : Int)))
  ++ (List.range s.chals).map (fun c => (vLift s c, (liftOf s d c : Int)))
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [(vEz s k, (evVal k 0 : Int)), (vEw s k, (evVal k 1 : Int))])

/-- ⚑ `Plonk.In_circuit.map_challenges ~f:Fn.id ~scalar plonk` (`step_verifier.ml:920-923`): the
`Scalar_challenge` fields α and ζ go through `scalar = SC.to_field_checked`, β and γ are `Challenge`
fields and stay RAW. So R6 reads `vLift` for α/ζ and `vN` for β/γ — upstream's own split, and the
retirement of the module header's simplification #7. -/
def ftWireOf (s : StepShape) : FtWire :=
  { ez := fun k => .inp (vColZ s k)
  , ew := fun k => .inp (vColW s k)
  , zeta := .inp (vLift s s.zetaChal)
  , alpha := .inp (vLift s s.alphaChal)
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
  let zeta := (lk (vLift s s.zetaChal)).toNat % pN
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

/-! ## §8f — R8, `finalize_other_proof`'s TAIL: the deferred values BIND.

`step_verifier.ml:1076-1147`. R5–R7 compute the deferred quantities; NOTHING yet compares them with
what the proof CLAIMS. This rung is that comparison, and it is the semantically load-bearing part of
`finalize_other_proof`:

  * **`ζω = domain#generator · plonk.zeta`** (`:934`) and the SECOND challenge polynomial
    `b(ζω) = ∏(1 + uₖ·(ζω)^{2^{k}})` over the LIFTED bulletproof challenges, so
    **`b_actual = challenge_poly ζ + r · challenge_poly ζω`** (`:1124-1128`) — the `+ r·…` leg the
    module header's simplification #4 named as absent.
  * **THREE `Shifted_value.Type1.to_field` unshifts** (`shifted_value.ml:133-135`: `t + t + c`) of
    `combined_inner_product` (`:1105-1109`), `b` (`:1126-1127`) and — inside
    `Plonk_checks.checked` (`plonk_checks.ml:536-544`) — `plonk.perm`.
    ⚑ **THE FIELD KEY.** A Type1 shift keys on the VALUE's own field, not the circuit's. These three
    are the Wrap proof-state's `fp` block, so the shift is **Type1 over `Fp`**: `c = 2^255 + 1`,
    `scale = 1/2` (`shift1`, `step_verifier.ml:825`; `PicklesStatementDiff` §1). The step statement's
    own `fq` block is Type2/`Fq` — subtract-only, no halving (`impls.ml:135`,
    `PicklesStepStatementDiff` §1) — and §16 shows both wrong readings diverge here.
  * **`xi_correct`** (`:1102-1104`) — the fr-sponge's own squeeze, `lowest_128_bits`-decomposed,
    against the statement's `xi`.
  * **`Boolean.all [xi_correct; b_correct; combined_inner_product_correct; plonk_checks_passed]`**
    (`:1141-1147`), each leg a REAL `Field.equal` gadget (`d·inv = 1 − bit`, `d·bit = 0`, `bit² =
    bit`), and the `should_verify` mux `verified && finalized || not should_verify`
    (`step_main.ml:121`, asserted at `:522`) closing on `= 1`. -/

/-- `Shifted_value.Type1.Shift.create (module Fp)`: `c = 2^{255} + 1` (`shifted_value.ml:122-126`,
`Fp.size_in_bits = 255`). -/
def SHIFT_C : Nat := (2 ^ 255 + 1) % pN
/-- …and `scale = 1/2`, as the `Fp` representative. -/
def SHIFT_INV2 : Nat := (pN + 1) / 2
/-- `Shifted_value.Type1.of_field` — `(x − c)·½`. -/
def shiftT1 (x : Nat) : Nat := fMul (fSub x SHIFT_C) SHIFT_INV2
/-- `Shifted_value.Type1.to_field` — `t + t + c`, the map the circuit emits. -/
def unshiftT1 (t : Nat) : Nat := fAdd (fAdd t t) SHIFT_C
/-- `Shifted_value.Type2.of_field` — subtract-only, `x − 2^255`. The WRONG-KIND reading, carried so
§16's control is about the rule and not about a typo. -/
def shiftT2 (x : Nat) : Nat := fSub x (2 ^ 255 % pN)

/-- The wire R8 reads: every field a SOURCE OP, so the rung's program can also be run on bent inputs
(§16's red controls) without touching the assembly. -/
structure FinWire where
  /-- ζ, LIFTED (`plonk.zeta`). -/
  zeta : AOp
  /-- `r`, LIFTED (`scalar (Scalar_challenge.create r_actual)`). -/
  r : AOp
  /-- `challenge_poly ζ` — R5's `vAcc bRounds`. -/
  bZeta : AOp
  /-- R5's `combined_inner_product` output. -/
  cipActual : AOp
  /-- R6's `Plonk_checks.checked` `perm` scalar. -/
  permActual : AOp
  /-- the LIFTED bulletproof challenges `u₀..u_{rounds−1}`. -/
  u : Nat → AOp
  /-- the fr-sponge's first squeeze (R7 segment B). -/
  xiSqueeze : AOp
  cipShift : AOp
  bShift : AOp
  permShift : AOp
  xiStmt : AOp

/-- What R8 bakes in, plus the witnesses its own rows CHECK. -/
structure FinCfg where
  rounds : Nat
  omega : Nat
  shiftC : Nat
  /-- `lowest_128_bits`' discarded high part. -/
  hiXi : Nat
  /-- per `Field.equal` gadget: the witnessed inverse and the result bit. -/
  eqInv : List Nat
  eqBit : List Nat
  /-- the kimchi `verified` bit and `should_verify` (`step_main.ml:36,121`). -/
  verified : Nat
  shouldVerify : Nat
  deriving Repr, Inhabited

structure FinSlots where
  zetaw : Nat
  bwZeta : Nat
  bActual : Nat
  cipUsed : Nat
  bUsed : Nat
  permUsed : Nat
  xiActual : Nat
  xc : Nat
  bc : Nat
  cc : Nat
  pc : Nat
  finalized : Nat
  out : Nat
  deriving Repr, Inhabited

/-- **The finalize program.** -/
def finBuild (W : FinWire) (C : FinCfg) : AM FinSlots := do
  let zero ← eLit 0
  let one ← eLit 1
  let shiftC ← eLit C.shiftC
  let two128 ← eLit (2 ^ 128 % pN)
  let omega ← eLit C.omega
  let zeta ← em W.zeta
  let r ← em W.r
  -- ── b_correct's SECOND leg (`:1124-1128`) ─────────────────────────────────────────────────
  let zetaw ← eMul omega zeta
  let zws ← (List.range C.rounds).foldlM (fun acc _ => do
      let y ← eMul (acc.getLastD zetaw) (acc.getLastD zetaw); pure (acc ++ [y])) [zetaw]
  let bw ← (List.range C.rounds).foldlM (fun acc k => do
      let u ← em (W.u k)
      let t ← eMul u (zws.getD (C.rounds - 1 - k) 0)
      let f ← eAdd one t
      eMul acc f) one
  let bz ← em W.bZeta
  let rbw ← eMul r bw
  let bAct ← eAdd bz rbw
  -- ── the THREE Type1/Fp unshifts ───────────────────────────────────────────────────────────
  let unshift : Nat → AM Nat := fun t => do let tt ← eAdd t t; eAdd tt shiftC
  let cipUsed ← unshift (← em W.cipShift)
  let bUsed ← unshift (← em W.bShift)
  let permUsed ← unshift (← em W.permShift)
  -- ── xi_actual = lowest_128_bits(squeeze) ──────────────────────────────────────────────────
  let sq ← em W.xiSqueeze
  let hi ← eWit C.hiXi
  let hiHigh ← eMul hi two128
  let xiAct ← eSub sq hiHigh
  let xiStmt ← em W.xiStmt
  -- ── `Field.equal`, the real gadget: `d·inv = 1 − bit`, `d·bit = 0`, `bit² = bit`. ─────────
  let mkEq : Nat → Nat → Nat → AM Nat := fun i x y => do
    let d ← eSub x y
    let iv ← eWit (C.eqInv.getD i 0)
    let bb ← eWit (C.eqBit.getD i 0)
    let bb2 ← eMul bb bb
    let _ ← eEq bb2 bb
    let p ← eMul d iv
    let q ← eSub one bb
    let _ ← eEq p q
    let sZ ← eMul d bb
    let _ ← eEq sZ zero
    pure bb
  let cipAct ← em W.cipActual
  let permAct ← em W.permActual
  let xc ← mkEq 0 xiAct xiStmt
  let bc ← mkEq 1 bUsed bAct
  let cc ← mkEq 2 cipUsed cipAct
  let pc ← mkEq 3 permUsed permAct
  -- ── `Boolean.all` and the `should_verify` mux, asserted ───────────────────────────────────
  let f1 ← eMul xc bc
  let f2 ← eMul f1 cc
  let fin ← eMul f2 pc
  let ver ← eWit C.verified
  let ver2 ← eMul ver ver
  let _ ← eEq ver2 ver
  let sv ← eWit C.shouldVerify
  let sv2 ← eMul sv sv
  let _ ← eEq sv2 sv
  let vf ← eMul ver fin
  let svf ← eMul sv vf
  let nsv ← eSub one sv
  let out ← eAdd svf nsv
  let _ ← eEq out one
  pure { zetaw := zetaw, bwZeta := bw, bActual := bAct, cipUsed := cipUsed, bUsed := bUsed
       , permUsed := permUsed, xiActual := xiAct, xc := xc, bc := bc, cc := cc, pc := pc
       , finalized := fin, out := out }

structure FinProg where
  prog : Array AOp
  slots : FinSlots
  deriving Repr, Inhabited

def finProgOf (W : FinWire) (C : FinCfg) : FinProg :=
  let r := (finBuild W C).run #[]
  { prog := r.2, slots := r.1 }

/-- The circuit variables EXPOSED as the public output — `pubWords` of them, drawn from every
sub-circuit so a public tie reaches all five. ⚑ The FIRST FOUR are the statement's deferred values;
R8's `Boolean.all` assert is what makes them a claim the circuit refuses to lie about. -/
def exposedVars (s : StepShape) : List PVar :=
  ([ vCipShift s, vBShift s, vPermShift s, vXiStmt s
   , vAcc s s.bRounds, vCa s s.cipEvals, vZ s s.bRounds
   , vSt s s.blocks 0, vSt s s.blocks 1, vSt s s.blocks 2
   , mpx s (pSum s (s.msmTerms - 2)), mpy s (pSum s (s.msmTerms - 2))
   , ipx s (qSum s (s.ipaRounds - 2)), ipy s (qSum s (s.ipaRounds - 2)) ]
   ++ (List.range s.chals).map (fun c => vN s c s.emsRows)
   -- ⚑ `0 .. bRounds−1`, NOT `0 .. bRounds`: `vAcc bRounds` and `vZ bRounds` are already the head
   -- entries, and at `shapeStep`'s 67 words the inclusive range made TWO of Step's public words
   -- carry the same circuit variable (measured 2026-08-02; the smoke shape's 12-word `take` cut
   -- before the collision, so the distinctness pin never saw it — §12 now pins BOTH shapes).
   ++ (List.range s.bRounds).map (fun k => vAcc s k)
   ++ (List.range s.bRounds).map (fun k => vZ s k)
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

/-! ### R8's wire, environment and data. -/

/-- R6's `ft_eval0`, as a value. -/
def FtData.out (f : FtData) : Nat := f.vals.getD f.fp.slots.ftEval0 0

/-- The finalize program's slots start after the ft program's. -/
def baseFin (s : StepShape) (f : FtData) : Nat := baseFtS s + f.fp.prog.size

/-- The fr-sponge's FIRST squeeze — R7 segment B's state after its first squeeze permutation, the
same convention R1 uses (`chalOf` reads lane 0 of the state after squeeze `c`'s permutation). -/
def frSqueezeVar (s : StepShape) : PVar := sgSt (baseSegB s) (nbB s) 2 (nbB s + 1) 0
def frSqueezeVal (segB : SegData) (specB : SegSpec) : Nat :=
  (segB.states.getD (specB.nb + 1) []).getD 0 0

/-- The fr-sponge's **SECOND** squeeze — `r_actual` (`step_verifier.ml:1008`). §8g's chain `1`
decomposes it and lifts it into the `r` the C8 fold and `b_correct` multiply by. -/
def frSqueeze2Var (s : StepShape) : PVar := sgSt (baseSegB s) (nbB s) 2 (nbB s + 2) 0
def frSqueeze2Val (segB : SegData) (specB : SegSpec) : Nat :=
  (segB.states.getD (specB.nb + 2) []).getD 0 0

/-- `b(ζω)` — the SECOND challenge polynomial, over the lifted bulletproof challenges. -/
def bwOf (s : StepShape) (d : SpongeData) : Nat :=
  let zetaw := fMul FT_OMEGA (liftOf s d s.zetaChal)
  let zws := (List.range s.bRounds).foldl
    (fun acc _ => let x := acc.getLastD 0; acc ++ [fMul x x]) [zetaw]
  (List.range s.bRounds).foldl
    (fun acc k => fMul acc (fAdd 1 (fMul (liftOf s d (k+1)) (zws.getD (s.bRounds - 1 - k) 0)))) 1

/-- `b_actual = challenge_poly ζ + r · challenge_poly ζω` (`step_verifier.ml:1124-1128`), computed
DIRECTLY here so §16 can pin the emitted program's own slot against it. `rv` is §8g's DEFERRED r. -/
def bActualOf (s : StepShape) (d : SpongeData) (df : DefData) (rv : Nat) : Nat :=
  fAdd (df.accs.getLastD 0) (fMul rv (bwOf s d))

def finWireOf (s : StepShape) (f : FtData) : FinWire :=
  { zeta := .inp (vLift s s.zetaChal)
  , r := .inp (vDLift s 1)
  , bZeta := .inp (vAcc s s.bRounds)
  , cipActual := .inp (vCa s s.cipEvals)
  , permActual := .inp (aVarAt (baseFtS s) f.fp.prog f.fp.slots.perm)
  , u := fun k => .inp (vLift s (k + 1))
  , xiSqueeze := .inp (frSqueezeVar s)
  , cipShift := .inp (vCipShift s)
  , bShift := .inp (vBShift s)
  , permShift := .inp (vPermShift s)
  , xiStmt := .inp (vXiStmt s) }

/-- Everything R8 needs, evaluated ONCE. -/
structure FinData where
  fp : FinProg
  vals : Array Nat
  bActual : Nat
  cipShift : Nat
  bShift : Nat
  permShift : Nat
  xiStmt : Nat
  xiHi : Nat
  deriving Repr, Inhabited

/-- R8's `.inp` lookup: the lifted challenges, §8g's deferred `r`, R5's two outputs, R6's `perm`
slot, R7's squeeze, and the four statement words — every one of them a variable another rung's rows
compute. -/
def finInputEnv (s : StepShape) (d : SpongeData) (f : FtData) (df : DefData)
    (segB : SegData) (specB : SegSpec) (rv : Nat) : VarEnv :=
  let sqv := frSqueezeVal segB specB
  let permA := f.vals.getD f.fp.slots.perm 0
  [ (vLift s s.zetaChal, (liftOf s d s.zetaChal : Int))
  , (vDLift s 1, (rv : Int))
  , (vAcc s s.bRounds, (df.accs.getLastD 0 : Int))
  , (vCa s s.cipEvals, (df.ca.getLastD 0 : Int))
  , (aVarAt (baseFtS s) f.fp.prog f.fp.slots.perm, (permA : Int))
  , (frSqueezeVar s, (sqv : Int))
  , (vCipShift s, (shiftT1 (df.ca.getLastD 0) : Int))
  , (vBShift s, (shiftT1 (bActualOf s d df rv) : Int))
  , (vPermShift s, (shiftT1 permA : Int))
  , (vXiStmt s, ((sqv % 2 ^ 128 : Nat) : Int)) ]
  ++ (List.range s.bRounds).map (fun k => (vLift s (k + 1), (liftOf s d (k + 1) : Int)))

/-- The HONEST config: `lowest_128_bits`' high part, and — because every `Field.equal` leg holds —
`bit = 1`, `inv = 0` in all four gadgets, with `verified = should_verify = 1`. §16 re-runs this at
bent inputs, where the honest witness is `bit = 0` and the assert FAILS. -/
def finCfgOf (s : StepShape) (hi : Nat) : FinCfg :=
  { rounds := s.bRounds, omega := FT_OMEGA, shiftC := SHIFT_C, hiXi := hi
  , eqInv := List.replicate 4 0, eqBit := List.replicate 4 1
  , verified := 1, shouldVerify := 1 }

def runFin (s : StepShape) (d : SpongeData) (f : FtData) (df : DefData)
    (segB : SegData) (specB : SegSpec) (rv : Nat) : FinData :=
  let sqv := frSqueezeVal segB specB
  let permA := f.vals.getD f.fp.slots.perm 0
  let p := finProgOf (finWireOf s f) (finCfgOf s (sqv / 2 ^ 128))
  let lk := envLookupAt (envIndex (finInputEnv s d f df segB specB rv))
  { fp := p, vals := aEval lk p.prog, bActual := bActualOf s d df rv
  , cipShift := shiftT1 (df.ca.getLastD 0), bShift := shiftT1 (bActualOf s d df rv)
  , permShift := shiftT1 permA, xiStmt := sqv % 2 ^ 128, xiHi := sqv / 2 ^ 128 }

/-- **R8's rows**: the compiled finalize program plus its σ-only probes. -/
def finRows (s : StepShape) (f : FtData) (fn : FinData) (wired : Bool) : List SRow :=
  let base := baseFin s f
  let V := aVarAt base fn.fp.prog
  aRows base fn.fp.prog
  ++ [ probeRow wired (V fn.fp.slots.finalized) (V fn.fp.slots.bActual)
     , probeRow wired (V fn.fp.slots.cipUsed) (V fn.fp.slots.xiActual)
     , probeRow wired (V fn.fp.slots.permUsed) (V fn.fp.slots.bUsed) ]

/-! ## §8g — the DEFERRED CHALLENGES: the fr-sponge FEEDS the fold.

`step_verifier.ml:1006-1013`. Before this section the C8 fold multiplied by two R1 transcript
challenges and the fr-sponge's squeeze reached nothing but `xi_correct` — the fold was CHECKED
against the squeeze and not FED by it (the module header's simplification #10). Here the two
multipliers are `to_field_checked` chains whose sources are the fr-sponge's own two squeezes:

  * **chain 0 — ξ.** Source is the STATEMENT's ξ word (`vXiStmt`), which is already a
    `Challenge.t`, so the chain's tie is `Field.Assert.equal n scalar` and not a decomposition. R8's
    `xi_correct` is what binds that word to the fr-sponge's FIRST squeeze — upstream's own two-step
    (`let xi_correct = … xi_actual … in let xi = scalar xi`), so a prover cannot move the fold
    without failing the assert.
  * **chain 1 — r.** Source is the fr-sponge's SECOND squeeze, decomposed by `lowest_128_bits`.
    Upstream carries no statement word for `r` at all: `scalar (Scalar_challenge.create r_actual)`.

⚑ THE RUNG CONSEQUENCE, stated plainly. Chain 0's source is a statement word and its rows ride with
R5, so ξ is derived at EVERY rung from r5 up. Chain 1's source is an R7 variable, so its rows ride
with R7: at r5/r6 (sub-circuits strictly below the fr-sponge) the fold's `r` is a free witness, and
at r7/r8 it is the squeeze's lift. That is the same ladder position `vEz 3` (R6's `ft_eval0`) and
the four statement words already occupy, and §15 pins which rung binds which. -/

/-- The two deferred prechallenges and their discarded high parts. -/
structure DefcData where
  /-- `lowest_128_bits` of the fr-sponge's first (ξ) and second (r) squeeze. -/
  pre : List Nat
  /-- the high parts. Chain `0`'s is unused — its source is already a `Challenge.t`. -/
  hi : List Nat
  deriving Repr, Inhabited

def runDefc (segB : SegData) (specB : SegSpec) : DefcData :=
  let sq1 := frSqueezeVal segB specB
  let sq2 := frSqueeze2Val segB specB
  { pre := [sq1 % 2 ^ 128, sq2 % 2 ^ 128], hi := [0, sq2 / 2 ^ 128] }

/-- Chain `c`'s LIFTED value — the multiplier itself. -/
def DefcData.lift (dc : DefcData) (s : StepShape) (c : Nat) : Nat :=
  liftVal s (dc.pre.getD c 0)

/-- **§8g's rows** for chain `c`, over the source `src`. -/
def defcRows (s : StepShape) (dc : DefcData) (c : Nat) (src : PVar) (split : Bool)
    (wired : Bool) : List SRow :=
  tfcRows s (defcVars s c) src split (dc.pre.getD c 0) wired

/-- Chain 0 (ξ), from the statement word — rides with R5. -/
def xiDefRows (s : StepShape) (dc : DefcData) (wired : Bool) : List SRow :=
  defcRows s dc 0 (vXiStmt s) false wired
/-- Chain 1 (r), from the fr-sponge's second squeeze — rides with R7. -/
def rDefRows (s : StepShape) (dc : DefcData) (wired : Bool) : List SRow :=
  defcRows s dc 1 (frSqueeze2Var s) true wired

/-! ## §9 — the whole assembly: rows, environment, placement, witness. -/

/-- Everything the schedule and the environment read, evaluated ONCE. -/
structure StepData where
  sh : StepShape
  sp : SpongeData
  msm : MsmData
  ipa : IpaData
  ft : FtData
  defc : DefcData
  df : DefData
  fin : FinData
  segA : SegData
  segB : SegData
  segC : SegData
  specA : SegSpec
  specB : SegSpec
  specC : SegSpec
  deriving Inhabited

/-- ⚑ THE DEPENDENCY ORDER, and why the fr-sponge now runs BEFORE the fold. Since §8g the C8 fold's
own multipliers are `to_field_checked` of the fr-sponge's two squeezes, so segment B is evaluated
first and `runDef` is fed from it. Nothing the fr-sponge absorbs depends on `combined_inner_product`
(segment B absorbs the digest of segment A, `ft_eval1`, the two public-poly evaluations and the 43
columns — R6's and R5's fixtures), so the order is a chain and not a cycle. -/
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
  let segB := runSeg specB
  -- ⚑ §8g: ξ and r, squeezed from the fr-sponge and lifted, are the fold's multipliers.
  let defc := runDefc segB specB
  let df := runDef s sp ftv (defc.lift s 0) (defc.lift s 1)
  let specC := hmSpec s msm ipa sp
  { sh := s, sp := sp, msm := msm, ipa := ipa, ft := ft, defc := defc, df := df
  , fin := runFin s sp ft df segB specB (defc.lift s 1)
  , segA := segA, segB := segB, segC := runSeg specC
  , specA := specA, specB := specB, specC := specC }

/-- **R7's rows** — the three sponge segments of §8e, then §8g's `r` chain over the fr-sponge's
second squeeze. -/
def absRows (t : StepData) (wired : Bool) : List SRow :=
  let s := t.sh
  segRows (baseSegA s) t.specA t.segA wired
  ++ segRows (baseSegB s) t.specB t.segB wired
  ++ segRows (baseSegC s) t.specC t.segC wired
  ++ rDefRows s t.defc wired

/-- **THE ROW SCHEDULE**, in the order `verify_one` runs it. -/
def stepRows (t : StepData) (wired : Bool) : List SRow :=
  let s := t.sh
  transcriptRows s t.sp wired
  ++ endoConstRow s
  ++ (List.range s.chals).flatMap (challengeRows s t.sp wired)
  ++ msmRows s t.msm wired
  ++ ipaRows s t.ipa wired
  ++ deferredRows s wired
  ++ xiDefRows s t.defc wired
  ++ cipRows s wired
  ++ closingRows s
  ++ ftRows s t.ft wired
  ++ absRows t wired
  ++ finRows s t.ft t.fin wired

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
      ++ [ (vHi s c, (hiOf s t.sp c : Int))
         , (vLiftT s c, (liftTOf s t.sp c : Int)), (vLift s c, (liftOf s t.sp c : Int)) ])
  ++ [ (vEndoR s, (ENDO_R : Int)) ]
  -- §8g: the two DEFERRED challenge chains (ξ from the statement word, r from the fr-sponge's
  -- second squeeze), each a full `to_field_checked` accumulator trace.
  ++ (List.range N_DEFC).flatMap (fun c =>
      let v := t.defc.pre.getD c 0
      let accs := emsAccs s v
      (List.range (s.emsRows + 1)).flatMap (fun k =>
        let a := accs.getD k (0, 2, 2)
        [ (vDN s c k, (a.1 : Int)), (vDA s c k, (a.2.1 : Int)), (vDB s c k, (a.2.2 : Int)) ])
      ++ [ (vDHi s c, (t.defc.hi.getD c 0 : Int))
         , (vDLiftT s c, (liftTVal s v : Int)), (vDLift s c, (liftVal s v : Int)) ])
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
  -- R8: the four STATEMENT words and the compiled finalize program's slots.
  ++ [ (vCipShift s, (t.fin.cipShift : Int)), (vBShift s, (t.fin.bShift : Int))
     , (vPermShift s, (t.fin.permShift : Int)), (vXiStmt s, (t.fin.xiStmt : Int)) ]
  ++ aEnvOf (baseFin s t.ft) t.fin.fp.prog t.fin.vals

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
  | transcript | challenges | msm | ipa | full | ftEval0 | absorb | finalize
  deriving Repr, DecidableEq, Inhabited

def Rung.tag : Rung → String
  | .transcript => "r1_transcript" | .challenges => "r2_challenges" | .msm => "r3_msm"
  | .ipa => "r4_ipa" | .full => "r5_full" | .ftEval0 => "r6_ft_eval0"
  | .absorb => "r7_absorption" | .finalize => "r8_finalize"

/-- Rung `k`'s rows.

⚑ **EVERY sub-circuit's row-set function is REACHED FROM HERE.** `rungRows` is the ONLY entry point
the emit driver has, and a sub-circuit whose rows live in a function nobody calls proves nothing:
measured on 2026-08-01, `cipRows` was absent from this `match` while every probe of every proved r5
still passed, so the `combined_inner_product` Horner chain the commit subject named was in NO proved
circuit and `vCa cipEvals` reached the public tie as a FREE variable. §15 now pins each rung's length
as the sum of its own sub-lists AND pins `stepRows = rungRows .finalize`, so a row-set that drops out
of this function is a red, not a silence. -/
def rungRows (t : StepData) (k : Rung) (wired : Bool) : List SRow :=
  let s := t.sh
  let a := transcriptRows s t.sp wired
  let b := endoConstRow s ++ (List.range s.chals).flatMap (challengeRows s t.sp wired)
  let c := msmRows s t.msm wired
  let d := ipaRows s t.ipa wired
  let e := deferredRows s wired ++ xiDefRows s t.defc wired ++ cipRows s wired ++ closingRows s
  let f := ftRows s t.ft wired
  let g := absRows t wired
  let h := finRows s t.ft t.fin wired
  match k with
  | .transcript => a
  | .challenges => a ++ b
  | .msm => a ++ b ++ c
  | .ipa => a ++ b ++ c ++ d
  | .full => a ++ b ++ c ++ d ++ e
  | .ftEval0 => a ++ b ++ c ++ d ++ e ++ f
  | .absorb => a ++ b ++ c ++ d ++ e ++ f ++ g
  | .finalize => a ++ b ++ c ++ d ++ e ++ f ++ g ++ h

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
def rowsS : List SRow := rungRows tS .finalize true
def rowsUS : List SRow := rungRows tS .finalize false
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
-- ⚑ `chals + N_DEFC` `to_field_checked` chains: R2's transcript challenges AND §8g's deferred ξ/r,
-- 8 `EndoMulScalar` rows each. The `+ N_DEFC` is #10's retirement, counted.
#guard (placedS.filter (fun g => g.kind == KGateType.endoMulScalar)).length
        == (shapeSmoke.chals + N_DEFC) * shapeSmoke.emsRows
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
-- ⚑ …AT THE COMMITTED SHAPE TOO. The smoke shape takes 12 of a 25-long list and so cannot see a
-- collision that only appears past word 12; this is the pin that does. (It found one: `vAcc bRounds`
-- and `vZ bRounds` were each exposed twice at `pubWords = 67`.)
#guard ((exposedVars shapeStep).map varIx).dedup.length == shapeStep.pubWords
#guard (exposedVars shapeStep).length == shapeStep.pubWords

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
#guard (rungProbeRows tS .finalize).all (fun r => permLookup pairsS ⟨r, 0⟩ != (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .finalize).all (fun r => permLookup pairsS ⟨r, 1⟩ != (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .finalize).all (fun r => permLookup pairsUS ⟨r, 0⟩ == (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .finalize).all (fun r => permLookup pairsUS ⟨r, 1⟩ == (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .finalize).length ≥ 10

-- ⚑ IT CAN GO RED. Desync ONE mid-chain probe cell and the σ check FAILS, so the `= true` above
-- is a gate rather than a tautology. (`toGrid` is first-wins, so the prepended override lands.)
#guard
  (let probe := (rungProbeRows tS .finalize).getD ((rungProbeRows tS .finalize).length / 2) 0
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
#guard tS.df.zs.getD 0 0 == liftOf shapeSmoke tS.sp 0
#guard (List.range shapeSmoke.bRounds).all (fun k =>
  tS.df.zs.getD (k + 1) 0 == fMul (tS.df.zs.getD k 0) (tS.df.zs.getD k 0))
#guard tS.df.accs.getLastD 0
        == (List.range shapeSmoke.bRounds).foldl
             (fun acc k => fMul acc
               (fAdd 1 (fMul (liftOf shapeSmoke tS.sp (k + 1))
                             (tS.df.zs.getD (shapeSmoke.bRounds - 1 - k) 0)))) 1
-- …and it is NOT the trivial product (a degenerate `b` would make the rung vacuous).
#guard tS.df.accs.getLastD 0 != 1

-- ── §12a — ⚑ THE FOLD IS FED BY THE FR-SPONGE (simplification #10, retired) ────────────────────
-- The multipliers the C8 fold uses are §8g's DEFERRED challenges. Named once, so every pin below
-- reads the same two values the `Generic` halves of `cipRows` multiply by.
def sq1S : Nat := frSqueezeVal tS.segB tS.specB
def sq2S : Nat := frSqueeze2Val tS.segB tS.specB
def xiFoldS : Nat := tS.defc.lift shapeSmoke 0
def rFoldS : Nat := tS.defc.lift shapeSmoke 1
/-- The multiplier a given fr-sponge squeeze would produce: `lowest_128_bits`, then
`to_field_checked` — the whole §8g chain, as a value. -/
def foldMulOf (sq : Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN)
    (Dregg2.Circuit.Emit.KimchiVerify.low128 sq)

-- ⚑ **ξ IS `endoMap` OF R7's FIRST SQUEEZE, r IS `endoMap` OF ITS SECOND.** `xi_correct` binds the
-- statement's ξ word to the first squeeze (§16d) and §8g's chain 0 lifts THAT word, so the composite
-- the fold multiplies by is exactly this. Upstream's own two-step, `step_verifier.ml:1010-1013`.
#guard ((xiFoldS : Nat) : ZMod pN) == foldMulOf sq1S
#guard ((rFoldS : Nat) : ZMod pN) == foldMulOf sq2S
-- …the two squeezes are different field elements, so ξ ≠ r is a fact about the sponge and not luck.
#guard sq1S != sq2S && xiFoldS != rFoldS
-- …and the lift is not the identity (a degenerate endo would make the chain decoration).
#guard xiFoldS != tS.defc.pre.getD 0 0 && rFoldS != tS.defc.pre.getD 1 0

-- ⚑ THE ASSEMBLED `combined_inner_product` IS THE VERIFIER'S. The Horner chain the `Generic` rows
-- compute equals `KimchiVerify.cipR` applied to the SAME ξ, r and evaluation columns — and `cipR`
-- IS the shipped `combinedInnerProduct` (`KimchiVerify.cipR_eq`, `rfl`, for every field; the
-- CommRing mirror exists precisely so a `ZMod pN` instance can answer to it). So the deferred rung
-- answers to the READ-ONLY transcription of `verifier.rs`, not to its own definition.
#guard
  ((tS.df.ca.getLastD 0 : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
         (tS.df.ez.map (fun n => (n : ZMod pN))) (tS.df.ew.map (fun n => (n : ZMod pN))))
-- …and it CAN go red: swapping ξ for r gives a different value (so the equality is discriminating,
-- not two names for zero).
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq2S) (foldMulOf sq2S)
          (tS.df.ez.map (fun n => (n : ZMod pN)))
          (tS.df.ew.map (fun n => (n : ZMod pN)))) == false)

-- ⚑⚑ **THE BITING RED CONTROL FOR #10: BENDING R7's SQUEEZE MOVES THE FOLD.** Before §8g the fold's
-- multipliers were R1 transcript challenges and this could not bite — the fr-sponge reached
-- `xi_correct` and nothing else, so a bent squeeze left `combined_inner_product` exactly where it
-- was. Now each squeeze is the SOURCE of a `to_field_checked` chain, and a one-unit bend in either
-- one moves the folded value.
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf (sq1S + 1)) (foldMulOf sq2S)
          (tS.df.ez.map (fun n => (n : ZMod pN)))
          (tS.df.ew.map (fun n => (n : ZMod pN)))) == false)
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf (sq2S + 1))
          (tS.df.ez.map (fun n => (n : ZMod pN)))
          (tS.df.ew.map (fun n => (n : ZMod pN)))) == false)
-- ⚑ …and the RETIRED reading — the last two R1 transcript challenges, which is what the fold
-- multiplied by until 2026-08-02 — is a DIFFERENT value. Derived, not fixed.
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR
          ((liftOf shapeSmoke tS.sp (shapeSmoke.chals - 1) : ZMod pN))
          ((liftOf shapeSmoke tS.sp (shapeSmoke.chals - 2) : ZMod pN))
          (tS.df.ez.map (fun n => (n : ZMod pN)))
          (tS.df.ew.map (fun n => (n : ZMod pN)))) == false)
#guard xiFoldS != liftOf shapeSmoke tS.sp (shapeSmoke.chals - 1)
#guard rFoldS != liftOf shapeSmoke tS.sp (shapeSmoke.chals - 2)

-- ⚑ …and it is a WIRE, not just an arithmetic identity: the variable `cipRows` Horners over is in a
-- σ class that also holds §8g chain 0's lift row, and the statement ξ word's class reaches THREE
-- rows (the chain's `Field.Assert.equal`, the closing public tie, and R8's `xi_correct` gadget).
#guard (classCells posS (vDLift shapeSmoke 0)).length ≥ 3
#guard (classCells posS (vDLift shapeSmoke 1)).length ≥ 3
#guard (classCells posS (vXiStmt shapeSmoke)).length ≥ 3
-- …the r chain's source really is segment B's SECOND squeeze cell (a state lane the sponge rows own).
#guard (classCells posS (frSqueeze2Var shapeSmoke)).length ≥ 2
#guard frSqueeze2Var shapeSmoke != frSqueezeVar shapeSmoke

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
def zetaS : Nat := ftInp (vLift shapeSmoke shapeSmoke.zetaChal)
def alphaS : Nat := ftInp (vLift shapeSmoke shapeSmoke.alphaChal)
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

-- ⚑⚑ **THE SEVEN COSET SHIFTS ARE THE DERIVED TICK SHIFTS** (simplification #8, retired). The rung
-- runs `TickShifts.tickShiftsFp 16` — the `Shifts::new` Blake2b→field construction — and that list
-- is pinned BYTE-EXACT there against o1-labs' own `Shifts::new(Radix2EvaluationDomain::<Fp>::new
-- (2^16))` output (`tick_shifts_export`, a path that runs kimchi and touches no Lean). Restated
-- here so a swap back to a fixture is a red in THIS file, at the point of use.
#guard FT_SHIFTS == Dregg2.Bridge.TickShifts.TICK_SHIFTS_16_ORACLE
#guard FT_SHIFTS.length == 7
-- …the first shift is the identity coset (`shifts[0] = 1`, `permutation.rs:158`), the rest are not,
-- and all seven are distinct — the structure `Shifts::new` guarantees and a fixture cannot fake.
#guard FT_SHIFTS.headD 0 == 1
#guard (FT_SHIFTS.drop 1).all (fun x => x != 1 && x != 0)
#guard FT_SHIFTS.dedup.length == 7
-- …and the derivation really is a derivation: the six sampled shifts are quadratic NON-residues of
-- `Fp` outside the `2^16` domain, which is `Shifts::sample`'s own acceptance predicate.
#guard (FT_SHIFTS.drop 1).all (fun x =>
  Dregg2.Bridge.TickShifts.accept FT_N [] ((x : Nat) : ZMod pN))
-- ⚑ …and they are NOT the placeholders the rung used before (the red control lives in §13's
-- `ft_eval0` pins below, where the fixtures give a different value).
#guard (List.range 7).all (fun i => FT_SHIFTS.getD i 0 != FT_SHIFTS_WERE_FIXTURES.getD i 0)
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
-- ⚑ …a bent DERIVED coset shift (the leg `MinaWrapFtEval0Weld` §6b exhibits on the real block):
-- bend one of `tickShiftsFp 16`'s own outputs by one and `ft_eval0` moves.
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
-- ⚑⚑ **DERIVED, NOT FIXED — the red control for simplification #8.** The seven placeholders the
-- rung ran until 2026-08-02 give a DIFFERENT `ft_eval0` at the same wire. So the value the circuit's
-- `Generic` rows compute is the one Mina's own `Shifts::new` cosets produce, and swapping the
-- derivation back out is a red rather than a silence.
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS_WERE_FIXTURES.map (fun x => ((x : Nat) : ZMod pN)))
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

/-! ## §15 — the LADDER is monotone, REACHED BY THE EMITTER, and each rung really adds its
sub-circuit.

⚑ THE REACHED-BY-THE-EMITTER PINS ARE THE FIRST BLOCK, and they exist because of a measured defect:
`cipRows` once lived in a function `rungRows` never called, so `r5_full` was proved seven times
without the `combined_inner_product` chain its own commit subject named, and `vCa cipEvals` reached
the public tie as a FREE variable — while every σ probe, every control and every public-input leg
passed. A length identity per rung, stated as the SUM OF ITS OWN SUB-LISTS, is what turns that from
a silence into a red; `stepRows == rungRows .finalize` closes the same hole on the other emitter. -/

-- Each rung IS the rung below plus exactly its own sub-circuit's rows.
#guard (rungRows tS .challenges true).length
        == (rungRows tS .transcript true).length + (endoConstRow shapeSmoke).length
           + ((List.range shapeSmoke.chals).flatMap (challengeRows shapeSmoke tS.sp true)).length
#guard (rungRows tS .msm true).length
        == (rungRows tS .challenges true).length + (msmRows shapeSmoke tS.msm true).length
#guard (rungRows tS .ipa true).length
        == (rungRows tS .msm true).length + (ipaRows shapeSmoke tS.ipa true).length
#guard (rungRows tS .full true).length
        == (rungRows tS .ipa true).length + (deferredRows shapeSmoke true).length
           + (xiDefRows shapeSmoke tS.defc true).length
           + (cipRows shapeSmoke true).length + (closingRows shapeSmoke).length
#guard (rungRows tS .ftEval0 true).length
        == (rungRows tS .full true).length + (ftRows shapeSmoke tS.ft true).length
#guard (rungRows tS .absorb true).length
        == (rungRows tS .ftEval0 true).length + (absRows tS true).length
#guard (rungRows tS .finalize true).length
        == (rungRows tS .absorb true).length + (finRows shapeSmoke tS.ft tS.fin true).length
-- …and the OTHER emitter (`stepRows`, the schedule) is the top rung, row for row.
#guard (stepRows tS true).map (fun r => r.kind) == (rungRows tS .finalize true).map (fun r => r.kind)
#guard (stepRows tS true).length == (rungRows tS .finalize true).length
-- …and each sub-list is NON-EMPTY, so "the sum matches" cannot be satisfied by a vanished rung.
#guard (cipRows shapeSmoke true).length > 0 && (deferredRows shapeSmoke true).length > 0
#guard (ftRows shapeSmoke tS.ft true).length > 0 && (absRows tS true).length > 0
#guard (finRows shapeSmoke tS.ft tS.fin true).length > 0 && (endoConstRow shapeSmoke).length > 0
#guard (xiDefRows shapeSmoke tS.defc true).length > 0
        && (rDefRows shapeSmoke tS.defc true).length > 0
-- ⚑ …and R7's own sub-list really is the three segments PLUS §8g's `r` chain.
#guard (absRows tS true).length
        == (segRows (baseSegA shapeSmoke) tS.specA tS.segA true).length
           + (segRows (baseSegB shapeSmoke) tS.specB tS.segB true).length
           + (segRows (baseSegC shapeSmoke) tS.specC tS.segC true).length
           + (rDefRows shapeSmoke tS.defc true).length

-- ⚑ **WHICH RUNG BINDS WHICH MULTIPLIER** (#10's honest residue, machine-checked). ξ's chain rides
-- with R5 because its source is a STATEMENT word, so `vDLift 0` has a computing row from `r5_full`
-- up. `r`'s source is the fr-sponge's second squeeze, an R7 variable, so `vDLift 1` has NO computing
-- row below `r7_absorption` and has one at and above it. Stated as a pin so the ladder position is
-- a fact rather than a sentence in a header.
def posAt (k : Rung) : List (PVar × Cell) :=
  circuitPositions (rungPub shapeSmoke k) (stepGates (rungRows tS k true))
#guard (classCells (posAt .full) (vDLift shapeSmoke 0)).length ≥ 2
#guard (classCells (posAt .ftEval0) (vDLift shapeSmoke 0)).length ≥ 2
#guard (classCells (posAt .full) (vDLift shapeSmoke 1)).length ≥ 1
#guard (classCells (posAt .absorb) (vDLift shapeSmoke 1)).length ≥ 2
#guard (classCells (posAt .finalize) (vDLift shapeSmoke 1)).length ≥ 3
-- …and the ξ chain's `EndoMulScalar` rows are in r5 while the r chain's are not.
#guard ((rungRows tS .full true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (shapeSmoke.chals + 1) * shapeSmoke.emsRows
#guard ((rungRows tS .ftEval0 true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (shapeSmoke.chals + 1) * shapeSmoke.emsRows
#guard ((rungRows tS .absorb true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (shapeSmoke.chals + 2) * shapeSmoke.emsRows

#guard (rungRows tS .full true).length < (rungRows tS .ftEval0 true).length
#guard (rungRows tS .ftEval0 true).length < (rungRows tS .absorb true).length
#guard (rungRows tS .absorb true).length < (rungRows tS .finalize true).length
-- R8 is `Generic`-only over R7 (it is scalar arithmetic + the boolean gadgets).
#guard ((rungRows tS .finalize true).drop (rungRows tS .absorb true).length).all
        (fun r => r.kind == KGateType.generic || r.kind == KGateType.zero)
-- R6 is `Generic`-only (it is scalar arithmetic; every other gate family is unchanged by it).
#guard ((rungRows tS .ftEval0 true).drop (rungRows tS .full true).length).all
        (fun r => r.kind == KGateType.generic || r.kind == KGateType.zero)
-- R7 adds `Poseidon` (11 rows per permutation, upstream's own run length) and — since §8g — exactly
-- ONE further `to_field_checked` chain, `r_actual`'s. No curve gate, no second chain.
#guard ((rungRows tS .absorb true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * (shapeSmoke.blocks + tS.specA.blocks + tS.specB.blocks + tS.specC.blocks)
#guard ((rungRows tS .full true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * shapeSmoke.blocks
#guard (List.range 4).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul, .zero].getD i .zero
  ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length
    ≥ ((rungRows tS .ftEval0 true).filter (fun r => r.kind == k)).length)
#guard (List.range 3).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul].getD i .zero
  ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length
    == ((rungRows tS .ftEval0 true).filter (fun r => r.kind == k)).length)
-- …and the compiled ft program is a real program, not a stub.
#guard ftS.fp.prog.size ≥ 900
#guard (aHalfSlots ftS.fp.prog).length ≥ 700

/-! ## §16 — R8: `finalize_other_proof`'s tail, against the value layer.

Every scalar R8 emits is pinned against the READ-ONLY `KimchiVerify` object it claims to compute, on
the SAME inputs, each with a red control that BITES. A rung that proves but computes the wrong scalar
is the failure mode this section exists to catch. -/

def finS : FinData := tS.fin
def finVal (i : Nat) : Nat := finS.vals.getD i 0
def zetaLS : Nat := liftOf shapeSmoke tS.sp shapeSmoke.zetaChal
/-- ⚑ `r` is §8g's DEFERRED challenge — `to_field_checked` of the fr-sponge's SECOND squeeze
(`step_verifier.ml:1008,1013`), not a transcript challenge. -/
def rLS : Nat := rFoldS
/-- The lifted bulletproof challenges, in `bEval`'s own list order (factor `k` carries the exponent
`2^{bRounds−1−k}`). -/
def usS : List (ZMod pN) :=
  (List.range shapeSmoke.bRounds).map (fun k => ((liftOf shapeSmoke tS.sp (k + 1) : Nat) : ZMod pN))

-- ── (a) `to_field_checked`'s CLOSING LINE — the endo lift, retiring simplification #7 ──────────
-- ⚑ The `EndoMulScalar` chain's `a₈`/`b₈` cells, combined by R2's new row, ARE
-- `ScalarChallenge::to_field(endo_r)` of the squeeze — `KimchiVerify.endoMap`, the same map
-- `MinaRealBlockTranscript.derived_zeta` checks on a real block. So `plonk.zeta`/`plonk.alpha`, ξ, r
-- and every bulletproof challenge are now the LIFTED values upstream uses, not the prechallenges.
#guard (List.range shapeSmoke.chals).all (fun c =>
  ((liftOf shapeSmoke tS.sp c : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN)
         (chalOf shapeSmoke tS.sp c))
-- …and it BITES on the constant: the BASE endo `FT_ENDO` in place of the SCALAR endo `endo_r` — the
-- exact cube-root conflation `MinaWrapFtEval0Weld` closed — gives a different lift.
#guard (((liftOf shapeSmoke tS.sp 0 : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((FT_ENDO : Nat) : ZMod pN)
              (chalOf shapeSmoke tS.sp 0)) == false
#guard ENDO_R != FT_ENDO
-- …and on the challenge: challenge 1's lift is not challenge 0's.
#guard (((liftOf shapeSmoke tS.sp 0 : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN)
              (chalOf shapeSmoke tS.sp 1)) == false
-- …and the lift is NOT the identity on any challenge (a degenerate endo would make the pin vacuous).
#guard (List.range shapeSmoke.chals).all (fun c =>
  liftOf shapeSmoke tS.sp c != chalOf shapeSmoke tS.sp c)

-- ── (b) `b_correct` — BOTH legs (`step_verifier.ml:1124-1128`) ────────────────────────────────
-- ⚑ `b_actual = challenge_poly ζ + r · challenge_poly ζω`. `KimchiVerify.ipaB0` is exactly
-- `bEval ζ + evalscale · bEval ζω`; `bEvalSq` is its ladder form (`bEvalSq_eq_bEval`, a theorem for
-- every CommRing), which is what runs at `ZMod pN`. The `+ r·…` leg is the one the module header
-- named as ABSENT — it is here, and it is this value.
#guard ((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
           + ((rLS : Nat) : ZMod pN)
             * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                 (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN)) usS
-- …and the compiled slot IS the direct computation (the program is a compiler, not an oracle).
#guard finVal finS.fp.slots.bActual == finS.bActual
#guard finVal finS.fp.slots.zetaw == fMul FT_OMEGA zetaLS
-- ⚑ …and the SECOND leg is load-bearing: dropping it (i.e. `b(ζ)` alone) is a DIFFERENT value.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS) == false
-- ⚑ …and ζω really is ω·ζ, not ζ: evaluating the second polynomial at ζ moves the answer.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
            + ((rLS : Nat) : ZMod pN)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS) == false
-- ⚑ …and the RAW prechallenges in place of the lifted ones move it (so (a) is load-bearing HERE).
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN)
              ((List.range shapeSmoke.bRounds).map
                 (fun k => ((chalOf shapeSmoke tS.sp (k + 1) : Nat) : ZMod pN)))
            + ((rLS : Nat) : ZMod pN)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                  (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN))
                  ((List.range shapeSmoke.bRounds).map
                     (fun k => ((chalOf shapeSmoke tS.sp (k + 1) : Nat) : ZMod pN)))) == false
-- ⚑ …and — since §8g — the `r` that weights the second leg is `endoMap` of the fr-sponge's SECOND
-- squeeze, so BENDING THAT SQUEEZE MOVES `b_actual` too. This is #10's red control on the
-- `b_correct` side: the value is derived from the sponge, not fixed by the transcript.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
            + foldMulOf (sq2S + 1)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                  (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN)) usS) == false
-- …and the RETIRED reading (the second-to-last transcript challenge) also moves it.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
            + ((liftOf shapeSmoke tS.sp (shapeSmoke.chals - 2) : Nat) : ZMod pN)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                  (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN)) usS) == false
-- …and neither b-polynomial is the trivial product.
#guard finS.bActual != 0 && bwOf shapeSmoke tS.sp != 1

-- ── (c) The THREE `Shifted_value.Type1.to_field` unshifts, and the FIELD KEY ───────────────────
-- ⚑ The shift constants are what `Shift.create (module Fp)` builds: `c = 2^255 + 1` and `½`.
#guard ((SHIFT_C : Nat) : ZMod pN) == (2 : ZMod pN) ^ 255 + 1
#guard 2 * SHIFT_INV2 % pN == 1
-- ⚑ Type1 ROUND-TRIPS, so the encoding is an encoding and not a digest.
#guard unshiftT1 (shiftT1 (finS.bActual)) == finS.bActual
#guard unshiftT1 (shiftT1 7) == 7 && unshiftT1 (shiftT1 (pN - 1)) == pN - 1
-- ⚑ **THE FIELD KEY IS LOAD-BEARING.** A Type2 reading (subtract-only, `x − 2^255`, the STEP
-- statement's own `fq` block, `impls.ml:135`) and the raw unshifted value BOTH diverge from the
-- Type1/`Fp` reading these three words wear. Getting this wrong misencodes SILENTLY.
#guard shiftT1 finS.bActual != shiftT2 finS.bActual
#guard shiftT1 finS.bActual != finS.bActual
#guard unshiftT1 (shiftT2 finS.bActual) != finS.bActual
-- ⚑ …and the circuit's own emitted unshift slots hit the three actual values.
#guard finVal finS.fp.slots.cipUsed == tS.df.ca.getLastD 0
#guard finVal finS.fp.slots.bUsed == finS.bActual
#guard finVal finS.fp.slots.permUsed == ftS.vals.getD ftS.fp.slots.perm 0
-- …and `combined_inner_product` really is the value R5's Horner chain produced, which §12 already
-- pinned against `KimchiVerify.cipR`. So the unshift lands on `cipR`, not on a local name for it.
#guard ((finVal finS.fp.slots.cipUsed : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
             (tS.df.ez.map (fun n => (n : ZMod pN))) (tS.df.ew.map (fun n => (n : ZMod pN)))

-- ── (d) `xi_correct` — the fr-sponge's own squeeze ────────────────────────────────────────────
-- ⚑ `xi_actual = lowest_128_bits (squeeze sponge)` (`step_verifier.ml:820-822,1102`), and the
-- squeeze is R7 segment B's — an assembly variable, not a fixture.
#guard finVal finS.fp.slots.xiActual == finS.xiStmt
#guard finS.xiStmt == Dregg2.Circuit.Emit.KimchiVerify.low128 (frSqueezeVal tS.segB tS.specB)
#guard finS.xiStmt < 2 ^ 128
-- …and the squeeze is NOT already 128 bits (so the decomposition is doing work).
#guard finS.xiHi != 0
-- …and it is NOT any R1 transcript squeeze: the two sponges are different objects, which is why the
-- check is a check.
#guard (List.range shapeSmoke.chals).all (fun c =>
  finS.xiStmt != chalOf shapeSmoke tS.sp c)
-- ⚑ **AND THIS WORD FEEDS THE FOLD** (simplification #10, retired). `xi_correct` ties the statement
-- ξ word to this squeeze, and §8g's chain 0 lifts THAT WORD into the multiplier `cipRows` Horners
-- over — upstream's `let xi_correct = … in let xi = scalar xi` (`step_verifier.ml:1010-1012`). So a
-- prover cannot move the fold's ξ without failing `xi_correct`, and cannot satisfy `xi_correct`
-- without the fold's ξ being `endoMap` of the fr-sponge's squeeze.
#guard ((xiFoldS : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN) finS.xiStmt
#guard tS.defc.pre.getD 0 0 == finS.xiStmt

-- ── (e) `Boolean.all` and the `should_verify` mux ─────────────────────────────────────────────
-- ⚑ ALL FOUR legs are 1 on the honest instance, the conjunction is 1, and the muxed output is 1 —
-- which is the value the rung's last row ASSERTS.
#guard [finVal finS.fp.slots.xc, finVal finS.fp.slots.bc, finVal finS.fp.slots.cc,
        finVal finS.fp.slots.pc, finVal finS.fp.slots.finalized, finVal finS.fp.slots.out]
        == [1, 1, 1, 1, 1, 1]

/-- Re-run R8's program with ONE statement word bent and the `Field.equal` witnesses set the way an
HONEST prover would then have to set them (`bit = 0`, `inv = d⁻¹`), so the control is about the
CHECK and not about a witness nobody could produce. Returns the `out` slot — the value the last row
asserts equals 1. -/
def finOutBent (which : Nat) (sv : Nat) : Nat :=
  let s := shapeSmoke
  let d := tS.sp
  let sqv := frSqueezeVal tS.segB tS.specB
  let base := finInputEnv s d tS.ft tS.df tS.segB tS.specB rFoldS
  -- bend the `which`-th statement word (0 = cip, 1 = b, 2 = perm, 3 = xi)
  let tgt : PVar :=
    match which with
    | 0 => vCipShift s | 1 => vBShift s | 2 => vPermShift s | _ => vXiStmt s
  let env := base.map (fun p => if p.1 == tgt then (p.1, p.2 + 1) else p)
  -- the honest witnesses for the bent instance: the bent leg's difference is `±2` (an unshift
  -- doubles) or `−1` (the raw ξ word), so `bit = 0` and `inv = d⁻¹` there, `bit = 1` elsewhere.
  let dv : Nat := if which == 3 then pN - 1 else 2
  let inv := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv dv
  let idx : Nat := match which with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0
  let C : FinCfg :=
    { finCfgOf s (sqv / 2 ^ 128) with
      eqInv := (List.replicate 4 0).set idx inv
      eqBit := (List.replicate 4 1).set idx 0
      shouldVerify := sv }
  let p := finProgOf (finWireOf s tS.ft) C
  (aEval (envLookupAt (envIndex env)) p.prog).getD p.slots.out 0

-- ⚑ **THE RED CONTROLS BITE, ONE PER DEFERRED WORD.** Bend the statement's `combined_inner_product`,
-- its `b`, its `plonk.perm` or its `xi` by ONE, give the equality gadget the witnesses an honest
-- prover would then have to give, and the assert `out = 1` FAILS. That is the whole point of the
-- rung: the deferred values BIND.
#guard (List.range 4).all (fun i => finOutBent i 1 != 1)
-- …and the UNBENT re-run through the same helper is 1, so the reds are about the bend.
#guard finVal finS.fp.slots.out == 1
-- ⚑ **BOTH BRANCHES OF THE `should_verify` MUX OCCUR.** With `should_verify = 0` the dummy path
-- accepts the very same bent statement — `verified && finalized ||| not should_verify`
-- (`step_main.ml:121`). A mux with one reachable branch is decoration.
#guard (List.range 4).all (fun i => finOutBent i 0 == 1)

-- ── (f) NO FREE VARIABLE reaches the public vector ────────────────────────────────────────────
-- ⚑ Every exposed variable's copy class has a cell OUTSIDE its closing row, i.e. some row COMPUTES
-- it. This is the shape of the defect that hid `cipRows`: a public word tied to a variable no gate
-- writes passes every probe and every control while binding nothing.
#guard (exposedVars shapeSmoke).all (fun v => (classCells posS v).length ≥ 2)
-- …and the four STATEMENT words are among them, each reaching R8's rows.
#guard (classCells posS (vCipShift shapeSmoke)).length ≥ 2
#guard (classCells posS (vBShift shapeSmoke)).length ≥ 2
#guard (classCells posS (vPermShift shapeSmoke)).length ≥ 2
#guard (classCells posS (vXiStmt shapeSmoke)).length ≥ 2
-- …and every `.inp` source of R8's program is a variable the assembly's OTHER rows carry, so the
-- rung reads the assembly rather than a private island.
#guard (finS.fp.prog.toList.filterMap (fun o =>
          match o with | .inp v => some v | _ => none)).all
        (fun v => (classCells posS v).length ≥ 2)
#guard (finS.fp.prog.toList.filter (fun o =>
          match o with | .inp _ => true | _ => false)).length ≥ 10
-- …and R8's program is a real program, not a stub.
#guard finS.fp.prog.size ≥ 80

end Dregg2.Circuit.Emit.KimchiStepMain
