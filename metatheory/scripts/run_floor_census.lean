/-
# run_floor_census.lean — the driver that makes `#floor_census` RUNNABLE.

    cd metatheory && lake env lean scripts/run_floor_census.lean     # ~2 min on a warm tree

Why this file has to exist. `#floor_census` (`Dregg2/Verify/FloorCensus.lean`) measures the
IMPORTED environment and fails closed under 500 000 constants, so it must be invoked from a module
that imports `Dregg2` — and `FloorCensus` cannot invoke itself, because the root imports IT. The
invocation therefore had nowhere to live, and for most of this campaign there was no driver and no
elaborating root, so **the v2 census had never once run**: every v2 figure in the planning docs was
an estimate standing in for a measurement nobody could take. The first real run is checked in at
`docs/artifacts/floor-census-v2-2026-07-26/`, with its provenance and the two numbers it corrected.

⚑ MEASURE ON A CLEAN EXPORT, NOT THE WORKING TREE. This tree is worked by several lanes at once; a
working-tree run carries other people's uncommitted providers and reports a surface no other
checkout reproduces. `git archive <commit> metatheory | tar x -C <dir>`, clone `.lake` into it
(`cp -c -R` on APFS, `cp -a` elsewhere — lake traces are content-hash keyed, so unchanged modules
replay rather than rebuild), build the root there, then run this. md5-verify `FloorCensus.lean`
identical across any trees you compare: a ruler that differs is not a comparison.

The output path is a string LITERAL because `#floor_census` takes one — edit the line below to put
the TSV where you want it. `#floor_census` with no argument prints the whole report to stdout
instead, which is fine for grepping one class and useless for a diff.
-/
import Dregg2

#floor_census "/tmp/floor-census-v2.tsv"
