/-
# Dregg2.CommitBindsGuards — the CI aggregate root for the FLOOR-FREE commitment-binding teeth

## WHY THIS FILE EXISTS

The 2026-07-31 light-client soundness-weld de-vacuuming produced two modules that restate the
published-commitment anti-ghost teeth WITHOUT the `Poseidon2SpongeCR` floor
(`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES that floor FALSE at deployed
BabyBear width, so the floored twins are true-but-empty at deployment):

  * `Dregg2.Circuit.Emit.CaveatCommitBindsOrCollides` — the caveat manifest + DFA route-commitment
    carrier: a forged manifest/rc either MOVES `caveatCommit`/`caveatCommitRc`, or the prover hands
    back a genuine `Poseidon2Binding.SpongeColl` at the two lists `chainCommitFind` returns.
  * `Dregg2.Circuit.RotatedCommitBindsOrCollides` — the PUBLISHED rotated commitment
    (`OLD_COMMIT`/`NEW_COMMIT`, the felts the light client pins): a forged authority residue / cap
    root / commitments root either MOVES the published commitment, or exhibits a `WireColl1`.

Both build standalone under `lake env lean <file>` and both pin every headline with
`#assert_axioms`. But **standalone-green is not CI-green.** Until a `defaultTargets` library
transitively imports a module, `lake build` never elaborates it, so its `#assert_axioms` never run in
the target — the *gating-defaults-to-silence* wound. `scripts/check-guard-modules.py` (the burndown
gate born from `Dregg2.Bridge.MinaWrapFtEval0Weld`, whose `#guard`-backed headline sat downstream of
a real `gateLinConst` defect for its whole life because `lake build` never compiled it) listed BOTH
of these as `UNTRACKED-ORPHAN` — not even in `lean-orphans-allow.txt`, i.e. silent claims nobody had
tracked.

This module is a pure re-export aggregate: importing the two roots them into a `lean_lib`
(`CommitBindsGuards`, registered in `lakefile.toml` `defaultTargets`), so a plain `lake build`
elaborates both and their thirteen `#assert_axioms` must pass or the build goes RED.

## WHY IT COULD NOT LAND UNTIL NOW

`RotatedCommitBindsOrCollides`'s import cone goes through `Dregg2.Circuit.Emit.EffectVmEmitV2`, which
was RED at HEAD mid-ChipArity cutover — so `PicklesSynthesis` and `MinaBridgeGuards` each explicitly
DEFERRED these two in their own headers. `f81509ff6` (the `chipArity_le_rate hins` one-liner) fixed
`EffectVmEmitV2`; the deferral has outlived its reason. The cone is verified green at HEAD via
`scripts/dregg-clean-build` (which grades the COMMITTED tree, not the churned working tree).

## SUBSTRATE (House Law #1)

Every binding/extractor/residual below is **Lean-authored**. Rust (`rotation_witness::wire_commit`,
`compute_canonical_state_commitment_v9_felt`, `descriptor_ir2.rs`) is the SOURCE of the deployed
commitment shape these model; the Lean here states and proves the binding. No Rust AIR, no
hand-written constraints. This aggregate authors nothing new — it only forces the already-authored
two into the build graph so their negative assertions can go red.

⚠ SCOPE. Rooting these runs their axiom-hygiene pins in CI and makes the floor-free teeth answerable
to a plain build. It does NOT by itself de-vacuum any CONSUMER: a consumer still calling the floored
`Poseidon2SpongeCR` twins stays vacuous at deployment until it is flipped onto the `_or_collides`
shapes. What is rooted here is the floor-free STATEMENTS being real, checked objects.
-/

import Dregg2.Circuit.Emit.CaveatCommitBindsOrCollides
import Dregg2.Circuit.RotatedCommitBindsOrCollides

namespace Dregg2.CommitBindsGuards

/-- A single tautology giving this aggregate a checkable elaboration signal of its own (so
`#print axioms` on the module head has a symbol to hang on) and documenting, in-tree, that the two
imports above are the rooted set. It asserts nothing about the imports beyond that they elaborated —
any red `#assert_axioms` among them fails this module's build before this line is reached. -/
theorem commit_binds_guards_rooted : True := trivial

#assert_axioms commit_binds_guards_rooted

end Dregg2.CommitBindsGuards
