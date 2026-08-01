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
port. The gate's own summary line reports `slack` — how many baseline rows are no longer
carriers, i.e. how much the ratchet can be lowered for free right now.

⚑ A row is a PAIR — `declaration.name ⊣ floor+floor+…` — and the emit always writes the
carrier's CURRENT floor set. So a shrink emit now banks TWO kinds of win: a declaration that
stopped being a carrier at all (its row is dropped) and one that merely SHED a floor (its row
is lowered). Both are things a name-keyed baseline could not see.

## ⚑ THE ONE-TIME MIGRATION OFF NAME-ONLY ROWS — RUN THIS, THEN DELETE THE INLINE ARRAY

The key landed on 2026-08-01 against a baseline of ~2195 name-only rows, which could not be
hand-keyed and had to red nothing on the day. So a row with no `⊣` is a LEGACY row and still
grandfathers its declaration against the ENTIRE refuted-floor set — the hole, still open, for
that one declaration. `#floor_ratchet` prints the surviving count on every run and
`scripts/floor_ratchet_check.sh` refuses an increase. The healthy value is 0, and getting
there is two steps on a green tree:

  1. `lake env lean FloorRatchetEmit.lean` — every legacy row that is still a carrier is
     rewritten as a keyed row, in `Dregg2/Verify/FloorRatchetBaseline.lean`. This includes the
     275 names currently living in `Dregg2/Verify/FloorRatchetBaselineInline.lean`: the emitter
     reads both arrays and writes ONE file.
  2. Empty `FloorRatchetBaselineInline.inlineSpelled` (delete `i0`/`i1`, leave the array `#[]`).
     Its names are now keyed rows in the main baseline; left in place they are 275 legacy rows
     that no emit will ever reach, because nothing rewrites that file.

Rebuild after both. `legacy` in the gate's summary line should read 0; if it does not, the
rows it is still counting are in a file the emitter did not write.

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
