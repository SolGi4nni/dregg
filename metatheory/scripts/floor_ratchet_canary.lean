/-
# floor_ratchet_canary.lean — THE GATE, CAUGHT IN THE ACT OF BITING.

A gate that has never been seen to fail is not a gate; it is a green light with no bulb. The
vacuity campaign shipped six teeth that never ran, and one that returned EXIT=0 from a cached
olean while a forced fresh elaboration returned EXIT=1 on a real violation. So `#floor_ratchet`
does not get to be trusted on the strength of passing.

This file is a DELIBERATE VIOLATION. It declares exactly the shape the campaign measured
accruing 46 times in its own window — a brand-new theorem taking `Poseidon2SpongeCR` as a
hypothesis, which `Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` proves
FALSE at deployed BabyBear parameters, making the theorem VACUOUS — and then invokes the gate.

    cd metatheory && lake env lean scripts/floor_ratchet_canary.lean

**EXPECTED: EXIT=1**, with `⚑ FLOOR-RATCHET: 1 NEW declaration(s) …`. A ZERO exit here means
the gate has gone blind and every guarantee in `Dregg2/Verify/FloorRatchet.lean` is void.
`scripts/floor_ratchet_check.sh --canary` asserts that inversion so CI watches the gate fail on
every run, which is the only way "it fails on a violation" stays a fact rather than a memory.

## Why a standalone file, and not a temporary edit to the tree

Two reasons, both load-bearing.

1. **It is swarm-safe.** Injecting a violation by editing `Dregg2.lean` or some module, building,
   and reverting is a mutation of a tree several agents share; a crash mid-run leaves a poisoned
   root behind. Nothing here touches a tracked file, so the canary is safe to run at any time,
   concurrently, by anyone.

2. **It exercises the subtle half of the gate.** The violating declaration elaborates in THIS
   file, so it has no module index in the environment. `FloorRatchet.ourNames` deliberately
   counts an index-less constant as OURS — `#floor_census`'s `moduleOf` maps that case to
   `` `«current» ``, which `ourModule` REJECTS, and a gate inheriting that would be blind to
   the file it is standing in. The canary is what keeps that decision honest: revert it and
   this file goes green.

The gate is also invoked from `Dregg2.lean` itself, where it sees declarations by module index
instead. Both paths run the same `check`; a build-level red was demonstrated separately by
landing this same theorem in a real module of a HEAD-pinned tree.
-/
import Dregg2

open Dregg2.Circuit.Poseidon2Binding

/-- THE VIOLATION. A perfectly true-looking, perfectly USELESS theorem: its hypothesis is
refuted at the parameters the system is deployed at, so it says nothing about anything. Its
conclusion is an equation — not `¬ Floor …` and not `False` — so the gate's anti-floor
exemption does not apply, exactly as for the 46 real accruals. -/
theorem floor_ratchet_canary_violation
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (xs ys : List ℤ) (h : sponge xs = sponge ys) : xs = ys :=
  hCR xs ys h

#floor_ratchet
