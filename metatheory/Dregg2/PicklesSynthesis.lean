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
  * `Dregg2.Circuit.Emit.KimchiRender`        — R4a: PlacedGate → proof-systems gate-list/witness render
  * `Dregg2.Circuit.Emit.KimchiRenderPoseidon` — R4a-scaled: a REAL Poseidon-permutation circuit
      (11 byte-exact `Poseidon` rows + a `Zero` gate, Lean-placed, Lean-witnessed via `PastaPoseidon`)
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
import Dregg2.Circuit.Emit.KimchiRender
import Dregg2.Circuit.Emit.KimchiRenderPoseidon
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
import Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar
import Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
import Dregg2.Circuit.Emit.KimchiRenderEndoMul
import Dregg2.Circuit.Emit.WitnessBuilder
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
