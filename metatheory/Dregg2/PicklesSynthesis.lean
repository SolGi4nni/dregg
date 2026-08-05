/-
# Dregg2.PicklesSynthesis — the CI aggregate root for the Pickles-in-Lean synthesis rung (R1–R4a)

## WHY THIS FILE EXISTS

The Pickles-synthesis epoch (`docs/PICKLES-SYNTHESIS-EPOCH-SCOPE.md`) produced six Lean modules that
each build standalone and each carry green-or-bust `#assert_axioms`/`by decide` differentials against
o1js / the real chain. But **standalone-green is not CI-green**: until a `defaultTargets` library
transitively imports a module, `lake build` never elaborates it, so its `#guard`/`#assert_axioms`/
`by decide` goldens never run in the target — the classic *gating-defaults-to-silence* wound (a module
that compiles under `lake env lean <file>` but is invisible to `lake build`).

This module is a pure re-export aggregate: importing the six roots them into a `lean_lib`
(`PicklesSynthesis`, registered in `lakefile.toml` `defaultTargets`), so a plain `lake build`
elaborates all six and their theorems must pass or the build goes RED.

## SUBSTRATE (House Law #1)

Every gate/placement/render/statement-packing below is **Lean-authored synthesis**. Rust
(`proof-systems`) only ever RUNS the Lean-emitted artifact (see `KimchiRender` / the R4a harness).
No Rust AIR, no hand-written constraints. This aggregate authors nothing new — it only forces the
already-authored six into the build graph.

## WHAT IS ROOTED HERE (the clean-cone six), AND WHAT IS DEFERRED

Rooted (import cone builds green at HEAD, does NOT go through the ChipArity-churned `EffectVmEmitV2`
cone — verified: the cone pulls `EffectVmEmit` (v1) + `DescriptorIR2`, both already in `Dregg2.lean`,
never `EffectVmEmitV2`):

  * `Dregg2.Circuit.Emit.KimchiCustomGates`   — R2: custom-gate rows (typ+coeffs) byte-exact vs o1js
  * `Dregg2.Circuit.Emit.KimchiPlacement`     — R1: cell placement + copy-permutation `wires` byte-exact
  * `Dregg2.Circuit.Emit.KimchiAssertEqual`   — ⚑ Snarky's `assert_equal` as a ZERO-ROW union-find
      over `PVar`, composed at `circuitPositions`. Proved general in the gate list: merging emits no
      row and moves no coefficient, and a merged placement IS `place` of the renamed gate list — so
      the existing naming-a-variable style is the special case and every byte pin transfers. The
      fail-closed entry routes through `placeCheckedWith`, so H1/dead-gap/H2 are the ones running
  * `Dregg2.Circuit.Emit.KimchiRender`        — R4a: PlacedGate → proof-systems gate-list/witness render
  * `Dregg2.Circuit.Emit.KimchiRenderPoseidon` — R4a-scaled: a REAL Poseidon-permutation circuit
      (11 byte-exact `Poseidon` rows + a `Zero` gate, Lean-placed, Lean-witnessed via `PastaPoseidon`)
  * `Dregg2.Circuit.Emit.KimchiPreimageCircuit` — ⚑ the first circuit here that is NOT a Pickles
      shape: `Poseidon.hash([x]) = c` with `c` the ONE PUBLIC INPUT, i.e. the shape of a zkApp
      method body. Its siblings above all carry `public_input_size = 0` and no statement; this one
      carries a statement, a secret, and the copy-permutation class that BINDS them
  * `Dregg2.Circuit.Emit.KimchiRenderCompleteAdd`   — CURVE gate: a REAL `complete_add` circuit
      (G + [2]G = [3]G; Lean witness generator, output cross-checked vs the `PastaCurve.Gp3` KAT)
  * `Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar` — CURVE gate: a REAL `endo_mul_scalar` circuit
      (16-bit scalar crumb-decode; the three folds satisfy `endomulScalarConstraints` over `ZMod pN`)
  * `Dregg2.Circuit.Emit.KimchiRenderVarBaseMul`    — CURVE gate: a REAL `var_base_mul` circuit
      (5-bit chained scalar-mul step; both rows satisfy `varBaseMulConstraints` over `ZMod pN`)
  * `Dregg2.Circuit.Emit.KimchiRenderEndoMul`       — CURVE gate: a REAL `endo_mul` circuit
      (4-bit endo-optimized step; both rows satisfy `endoMulConstraints` over `ZMod pN`)
  * `Dregg2.Circuit.Emit.WitnessBuilder`      — the reusable witness-assembly core (compute → place →
      compose): reproduces `poseidonWitness` byte-identically through the combinator (`#guard`) and
      COMPOSES two gates sharing a copied wire with a consistent shared cell (`place`'s copy-permutation
      σ holds — `by decide` on the concrete circuit, falsifiable)
  * `Dregg2.Circuit.Emit.KimchiComposeStepFragment` — the multi-step `step_main` COMPONENT: 6 chained
      multi-chunk `var_base_mul` scalar muls + a 16-block `endo_mul` + a 6-long `complete_add`
      accumulator, 132 rows / 4 gate types / 239 variables, placed by `place` and composed by
      `WitnessBuilder`; every row satisfies its `KimchiVerify` constraint body ON THE ASSEMBLED GRID,
      σ holds on that grid (falsifiably), and the point/scalar semantics are cross-checked against
      `PastaCurve`'s independent Jacobian formulas. Proved pure-Rust by `pickles-stepfragment-harness`
  * `Dregg2.Circuit.Emit.KimchiWrapMain` — ⚑ **`wrap_main`, the OTHER half of Pickles recursion**,
    and a different field and curve from the step side: `wrap_main_inputs.ml:4,6` sets `Me = Tock`
    and `Impl = Impls.Wrap`, so the wrap circuit computes over **Fq** with **Vesta** as its inner
    curve and a **Pallas**-committed proof, where the step side is Fp/Pallas/Vesta. Four rungs
    assembled: the Fq Poseidon transcript of `wrap_verifier.ml:516-646` driven by the REAL rate-2
    state machine and pinned against a real accepted proof's own β/γ/α′/ζ′; `to_field_checked` over
    Fq at Pallas's endo scalar with both `lowest_128_bits` halves range-checked; the branch
    selection (`One_hot_vector` · `Pseudo.choose` · `ones_vector`'s `Field.equal` gadget ·
    `Branch_data.Checked.pack`), which has no step-side analogue at all; and the closing public tie.
    Its §13 names by sub-circuit everything `wrap_main` still has that this does not.
  * `Dregg2.Circuit.Emit.KimchiStepMain` — **`step_verifier.verify_one` itself**, in the SEVEN named
      sub-circuits it runs: the Fp Poseidon transcript SPONGE (state copy-wired across every block
      boundary — no prior rung had copy-wired a `Poseidon` gate at all), `to_field_checked`'s chained
      `EndoMulScalar` rows tied back to the squeeze, the commitment MSM whose `var_base_mul` scalar
      counter CLOSES ON the challenge the `EndoMulScalar` chain decoded (one σ class across three
      gate types), the `Scalar_challenge.endo` fold rounds, the deferred `b(ζ)` +
      `combined_inner_product` (pinned against `KimchiVerify.cipR`) with Step's `PRIMARY_LEN = 67`
      public input placed through `placeChecked`, **`scalars_env` + the six-gate linearization
      CONSTANT TERM + `ft_eval0` + `Plonk_checks.checked`** (compiled from a straight-line program
      onto double-`Generic` rows and pinned value-for-value against `KimchiVerify.gateLinConst` /
      `ftEval0R` / the 67 constraint bodies list-by-list, each with a red control), and **the
      43-column evaluation ABSORPTION with `Opt_sponge` masking + `hash_messages_for_next_step_proof`**.
      All SEVEN gate types Mina's step circuits use, in one circuit. Proved pure-Rust rung by rung by
      `pickles-stepmain-harness`
  * `Dregg2.Circuit.Emit.KimchiRenderPublicInput` — the PUBLIC-INPUT path of `place`, which every rung
      above ran at `pubSize = 0` (measured 2026-08-01: all nine committed fixtures carried
      `public_input_size: 0`, so the leading public rows, the `External i ↦ {i,0}` cells and the
      `pubSize + gateIndex` offset were identity everywhere and had never been proved). Two circuits
      with `pubSize > 0` — 3 words, and 67 at Step's measured `PRIMARY_LEN` (mina-rust
      `ProofConstants`) — pinned here (`place`'s public rows ARE kimchi's `[1,0,0,0,0]` Pub gates; the
      public cells wire into the circuit; σ is a permutation with `pubSize > 0`) and proved pure-Rust
      by `pickles-publicinput-harness`, both polarities plus a σ control and a non-vacuity control
  * `Dregg2.Bridge.PicklesR3BranchDataDiff`   — R3: the branch_data prefix-mask pack (vs devnet block)
  * `Dregg2.Bridge.PicklesStatementDiff`      — R3: the WHOLE Wrap statement packing byte-exact
  * `Dregg2.Bridge.PicklesStepStatementDiff`  — R3: the Step per-proof layout + `fq=Type2/Fq` field-key

DEFERRED to the ChipArity `DescriptorIR2`/`EffectVmEmitV2` convergence (a sibling lane owns it): the
de-vacuum modules `CaveatCommitBindsOrCollides` / `RotatedCommitBindsOrCollides`, whose cone goes
through the churned `EffectVmEmitV2`. They are NOT imported here.

⚠ SCOPE (Phase A, NOT soundness). Rooting these runs their DIFFERENTIAL fidelity checks in CI. It does
NOT make them "machine-checked Pickles": the R1–R4a work is byte-exact FIDELITY to o1js / the chain +
a real kimchi inner proof (R4a), not a recursion-soundness theorem (Phase B / R5).
-/

import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiAssertEqual
import Dregg2.Circuit.Emit.KimchiRender
import Dregg2.Circuit.Emit.KimchiRenderPoseidon
import Dregg2.Circuit.Emit.KimchiPreimageCircuit
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
import Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar
import Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
import Dregg2.Circuit.Emit.KimchiRenderEndoMul
import Dregg2.Circuit.Emit.WitnessBuilder
import Dregg2.Circuit.Emit.KimchiComposeMSM
import Dregg2.Circuit.Emit.KimchiComposeStepFragment
import Dregg2.Circuit.Emit.KimchiRenderPublicInput
import Dregg2.Circuit.Emit.KimchiStepMain
import Dregg2.Circuit.Emit.KimchiWrapMain
-- ⚑ W-XHAT's two-source SRS pin. `MinaStepSrsLagrange` (the data) is reached through
-- `KimchiWrapMain`; the PIN that says the SRS construction reproduces Mina's devnet SRS imports the
-- 5.4 MB `MinaWrapSrsG` and is deliberately NOT on the assembly's own import path, so it needs a
-- root of its own or it would build only under `lake env lean` — gating-defaults-to-silence.
import Dregg2.Circuit.Emit.MinaStepSrsLagrangePin
-- ⚑ THE PROVER-CHOICE CENSUS, one module per assembly. Rooted here rather than left to
-- `lake env lean`, because a census nothing builds is the gating-defaults-to-silence wound in the
-- instrument that is supposed to detect it. Each states, as NAMED THEOREMS over the emitted rows,
-- how many cells a prover can still choose and which of them change what the circuit accepts.
import Dregg2.Circuit.Emit.KimchiStepProverChoice
import Dregg2.Circuit.Emit.KimchiWrapProverChoice
-- ⚑ THE STEP→WRAP CHAIN, ROOTED 2026-08-04. Its 19 pins (18 `#assert_compiled` + 1
-- `#assert_axioms`) ran in NO build: the module was RED (a width conjunct W-PREV falsified,
-- `KimchiStepWrapChain` §9a) AND unrooted, so the redness was invisible to everything except
-- `check-lean-orphans.sh`.
-- ⚠ TWO COST CLAIMS THE ALLOWLIST ENTRY MADE, BOTH MEASURED FALSE HERE:
--   * "rooting pulls the whole `KimchiWrapMain` cone" — this file has imported `KimchiWrapMain`
--     two lines up all along, so the closure grows by exactly ONE module (3055 → 3056 jobs), the
--     same finding `metatheory/lakefile.toml` records for the 20 orphans rooted the same day;
--   * "~515 s, the most expensive single rooting in this population by two orders of magnitude" —
--     the module builds in **11 s** (`124ba5077`, hbox, warm `.lake`, INCLUDING C codegen). The
--     old file on the same box, same warm tree, `lean` with an extracted `LEAN_PATH`: **425.8 s**
--     (and RED). Nearly all of that was the ONE `native_decide` that had to evaluate `wrapPublic`
--     = `wrapPublicAt _ .prev` — the whole nine-rung environment including §15's 67-scalar MSM
--     ladders, three `qInv`s deep each. That conjunct is now the kernel-clean INSTANCE
--     `the_emitted_public_vector_is_its_rungs_width`, which needs no environment at all. It is also
--     why the predecessor's two isolation probes each cost more than the whole file: probing a
--     conjunction that contains `.prev` re-pays `.prev` every time. 425.8 s → 11 s, 39x.
import Dregg2.Circuit.Emit.KimchiStepWrapChain
import Dregg2.Bridge.PicklesR3BranchDataDiff
import Dregg2.Bridge.PicklesStatementDiff
import Dregg2.Bridge.PicklesStepStatementDiff

namespace Dregg2.PicklesSynthesis

/-- A single tautology whose only purpose is to give this aggregate a checkable elaboration signal
of its own (so `#print axioms` on the module head has a symbol to hang on) and to document, in-tree,
that the six imports above are the rooted set. It asserts nothing about the imports beyond that they
elaborated (any red among them fails this module's build before this line is reached). -/
theorem pickles_synthesis_rooted : True := trivial

#assert_axioms pickles_synthesis_rooted

end Dregg2.PicklesSynthesis
