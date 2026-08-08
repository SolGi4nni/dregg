/-
# Dregg2.MinaBridgeGuards — the CI aggregate root for the Mina→dregg wrap-recursion welds

## WHY THIS FILE EXISTS

Six `Dregg2.Bridge.MinaWrap*` / `TickShifts` modules carry the **P4 recursion-boundary evidence** for
the Mina bridge — the byte-exact deferred-value expansion, the challenge/opening replay against real
block 539508, the `ft_eval0` linearization-constant reproduction (`gateLinConst`), the public-input
slot layout, and the derived coset tick-shifts. Each builds standalone under `lake env lean <file>`
and each pins its claim green-or-bust with `#guard` / `#assert_axioms`.

But **standalone-green is not CI-green.** Until a `defaultTargets` library transitively imports a
module, `lake build` never elaborates it, so its `#guard`/`#assert_axioms` never run in the target —
the *gating-defaults-to-silence* wound. This is not hypothetical here: it is the EXACT sequence that
produced `Dregg2.Bridge.MinaWrapFtEval0Weld` (`scripts/check-guard-modules.py` documents it). That
module carried a `#guard`-backed headline AND, from its birth commit, sat downstream of a real
`gateLinConst` defect — invisible because `lake build` never compiled it, so the `#guard` never fired.
The defect was found only when a lane forced the module to compile.

This module is a pure re-export aggregate: importing the six roots them into a `lean_lib`
(`MinaBridgeGuards`, registered in `lakefile.toml` `defaultTargets`), so a plain `lake build`
elaborates all six and every one of their `#guard`s / `#assert_axioms` must pass or the build goes
RED. The recursion-boundary evidence is now permanent CI, not a claim that runs only when targeted.

## SUBSTRATE (House Law #1)

Every gate/word/shift/pin below is **Lean-authored**. Rust (`proof-systems`, the Mina node) is the
SOURCE of the pinned real-block bytes; the Lean here reproduces them and refuses the tampered ones.
No Rust AIR, no hand-written constraints. This aggregate authors nothing new — it only forces the
already-authored six into the build graph so their negative assertions can go red.

## WHAT IS ROOTED HERE (the six Mina wrap welds + the synthesized-circuit weld)

  * `Dregg2.Bridge.MinaWrapChallengesWeld` — Fiat-Shamir challenges + opening wires == real block 539508
  * `Dregg2.Bridge.MinaWrapDeferred`       — `expandDeferred`: the deferred-value expansion, refutable
  * `Dregg2.Bridge.MinaWrapDeferredWeld`   — the 6/6 boundary words (`expandDeferred` vs `w539508`)
  * `Dregg2.Bridge.MinaWrapFtEval0Weld`    — `ft_eval0` + the `gateLinConst` reproduction (six gate bodies)
  * `Dregg2.Bridge.MinaWrapPublicInput`    — the wrap public-input slot layout + `publicComm` gold
  * `Dregg2.Bridge.TickShifts`             — the derived coset tick-shifts (one `powFast` body, no twin)
  * `Dregg2.Bridge.StepMainFtEval0RealBlock` — ⚑ the SYNTHESIZED `ft_eval0` circuit's own straight-line
      program (the one `KimchiStepMain`'s `r6_ft_eval0` rows execute) run on block 539508's Step wire:
      it reproduces `FT_EVAL0` and the constant term byte-for-byte, with four red paths (a bent coset
      shift, the identity shifts, `er` in place of the base endo, a wrong domain). Rooted HERE and not
      in `FFI.lean` for the same reason the weld it sits beside is: one-block fixtures.
  * `Dregg2.Bridge.MinaMultiBlockConformance` — ⚑⚑ **the same weld functions on blocks that are NOT
      539508.** Seven fixtures (five devnet including the hardfork genesis, one mainnet, plus 539508
      as the control), each with its OWN targets from openmina and its OWN inputs from the
      independent binprot re-walk. Every claim above this line was, until it landed, stated over one
      block; this is what makes "the welds conform to the protocol" a sentence with a red path.
      GENERATED — regenerate with `metatheory/fixtures/pickles-extractors/
      gen_multiblock_conformance.py`, do not hand-edit.

## ⚑ 2026-08-08 — THE WRAP-CLOSING / FINALIZE-SCALARS CONE, ROOTED OUT OF ORPHANHOOD

Three more `Circuit.Emit` Mina modules join. All three were reachable from NO `defaultTargets`
entry — `check-lean-orphans.sh` named them UNLISTED — while their own docblocks said *"NOT imported
by the `Dregg2` root, per house practice for gates."* That practice is exactly HALF a practice: a
gate stays out of the FFI root set, but it must be rooted in a GUARD library or its oleans go stale
on disk and `lake build` checks nothing (the `MinaWrapVerifierSponge` §8 census weld shipped
through that hole). Each was built green at HEAD before rooting:

  * `Dregg2.Circuit.Emit.MinaWrapClosingAir`       — the Pallas closing-verifier AIR (FSI1's other
      curve): the accumulator machine at `pLimb`, block 539508's Step `sg` fixtures, the b-fold and
      both-polarity refusal exhibits.
  * `Dregg2.Circuit.Emit.MinaWrapClosingScheduled` — its scheduled/selector-forced form (the
      `AirSelectorForcing` route), same fixtures, zero `#guard`s.
  * `Dregg2.Circuit.Emit.MinaFinalizeScalars`      — `dregg-mina-finalize-scalars::v1`: the whole
      in-AIR finalize-scalars row program (slot tables, liveness windows, the C5 zk-poly leg) over
      the real block.

  * `Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld` — the weld between the finalize-scalars fixture
      constants and the Wrap fixtures' own values (domain generator, zk roots, shifts, the C5
      witnessed inverse). It was RED at the first rooting pass (an `Inhabited`-instance hole at
      its `WRAP_BLOCKS.getD … default` statement) while its authoring lane was live; it
      elaborates clean now and joins the same day.

(The DAG is redundant on purpose: `MinaWrapFtEval0Weld` transitively pulls Deferred/DeferredWeld/
PublicInput/TickShifts, and `MinaWrapChallengesWeld` is a second top. All six are imported explicitly
so the rooted set is self-documenting and a re-parenting of the DAG cannot silently un-root one.)

⚠ SCOPE (fidelity, NOT recursion-soundness). Rooting these runs their DIFFERENTIAL replay checks in
CI: the emitted words reproduce the real block and the tampered ones are refused. It does NOT make the
bridge "machine-checked recursion" — that is the FRI/STARK floor named elsewhere, not a `#guard`.
-/

import Dregg2.Bridge.MinaWrapChallengesWeld
import Dregg2.Bridge.MinaWrapDeferred
import Dregg2.Bridge.MinaWrapDeferredWeld
import Dregg2.Bridge.MinaWrapFtEval0Weld
import Dregg2.Bridge.MinaWrapPublicInput
import Dregg2.Bridge.TickShifts
import Dregg2.Bridge.StepMainFtEval0RealBlock
import Dregg2.Bridge.MinaMultiBlockConformance
import Dregg2.Circuit.Emit.MinaWrapClosingAir
import Dregg2.Circuit.Emit.MinaWrapClosingScheduled
import Dregg2.Circuit.Emit.MinaFinalizeScalars
import Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld

namespace Dregg2.MinaBridgeGuards

/-- A single tautology giving this aggregate a checkable elaboration signal of its own (so `#print
axioms` on the module head has a symbol to hang on) and documenting, in-tree, that the six imports
above are the rooted set. It asserts nothing about the imports beyond that they elaborated — any red
`#guard`/`#assert_axioms` among them fails this module's build before this line is reached. -/
theorem mina_bridge_guards_rooted : True := trivial

#assert_axioms mina_bridge_guards_rooted

end Dregg2.MinaBridgeGuards
