/-
# FloorRatchetEmit — the LOWERING tool for the refuted-floor accrual ratchet.

`Dregg2/Verify/FloorRatchet.lean` holds the gate; `Dregg2/Verify/FloorRatchetBaseline.lean`
holds the grandfathered carriers it compares against. This root module is how that baseline
is REWRITTEN, and it lives outside the `Dregg2` library on purpose: it `import Dregg2`, which
the gate's own modules must not do (they are imported BY the root).

## After landing a port, bank the win

    cd metatheory
    lake env lean FloorRatchetEmit.lean

The uncommented invocation below is the plain, SHRINK-ONLY emitter: it writes
`baseline ∩ current`, so a carrier that is not already grandfathered is dropped rather than
laundered in. Then rebuild (`lake build Dregg2`) and commit the shortened baseline with the
port. The gate's own summary line reports `slack` — how many baseline names are no longer
carriers, i.e. how much the ratchet can be lowered for free right now.

## Raising the ratchet (rare, and deliberate)

Swap the invocation for `#floor_ratchet_emit!` — a different token, which grandfathers every
current carrier including the new ones. It lands as ADDED LINES in the baseline diff. Do this
only when a new declaration genuinely cannot be built without a hypothesis this tree proves
FALSE, and say why in the commit message. Adding a line here is a claim, on the record, that
a new theorem is knowingly vacuous at deployed BabyBear parameters.

⚑ Both emitters run `surface`, which FAILS CLOSED on a partial environment (< 500 000
constants, an unresolvable sentinel floor, a sentinel whose in-tree refutation is not
rediscovered, or a missing `prop-body` keystone). A baseline generated over half a tree would
under-count carriers and then fire false positives on everyone else's modules, so the emitter
refuses to write one at all. If this module errors, build the tree green FIRST.
-/
import Dregg2

-- Relative to the process CWD, so run it from `metatheory/` (as the recipe above does).
#floor_ratchet_emit "Dregg2/Verify/FloorRatchetBaseline.lean"
