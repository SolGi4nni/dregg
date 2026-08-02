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

namespace Dregg2.MinaBridgeGuards

/-- A single tautology giving this aggregate a checkable elaboration signal of its own (so `#print
axioms` on the module head has a symbol to hang on) and documenting, in-tree, that the six imports
above are the rooted set. It asserts nothing about the imports beyond that they elaborated — any red
`#guard`/`#assert_axioms` among them fails this module's build before this line is reached. -/
theorem mina_bridge_guards_rooted : True := trivial

#assert_axioms mina_bridge_guards_rooted

end Dregg2.MinaBridgeGuards
