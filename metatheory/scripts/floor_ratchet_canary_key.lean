/-
# floor_ratchet_canary_key.lean — THE BASELINE KEY, CAUGHT IN THE ACT OF BITING.

The sibling of `floor_ratchet_canary.lean` for the bypass none of the others could catch: a
declaration that is ALREADY GRANDFATHERED, changing WHAT IT ASSUMES.

## What the hole was

`#floor_ratchet` compared the live carrier surface against the baseline on `c.name.toString`
ALONE, and the per-declaration scan recorded only the FIRST floor it found (`Carrier.floor` and
`Carrier.cls` were reporting-only). So a grandfathered NAME was a blanket exemption over the ENTIRE
refuted-floor set, for the life of the name:

  * a baselined declaration could be DRAINED of `compressInjective` and ACQUIRE `Poseidon2SpongeCR`
    in the same commit — a different vacuity claim, same green build;
  * a declaration binding two refuted floors could drop one and add another and report the same
    first hit;
  * a name could be deleted and a DIFFERENT theorem reintroduced under it, green.

That was live while a drain was in flight. An audit measured **477** declarations binding
`compressInjective` / `compressNInjective` / `cellLeafInjective` directly, **161** of which bind a
SECOND refuted floor as well — 161 permanent name-shaped holes sitting in exactly the declarations
being edited.

The key is now the PAIR `name ⊣ floor+floor+…`, read as an UPPER BOUND: a baselined row grandfathers
any SUBSET of its floor set. Acquiring a floor is a fresh carrier and a hard error; DROPPING one is
a port and stays grandfathered, because a gate that reddened on the campaign's own wins would be
switched off, which lands where a blind gate lands.

## What this file asserts

    cd metatheory && lake env lean scripts/floor_ratchet_canary_key.lean

**EXPECTED: EXIT=1**, with `⚑ FLOOR-RATCHET:` naming BOTH `floor_ratchet_key_canary_acquires` and
`floor_ratchet_key_canary_swapped`, and naming NEITHER of the two `control_` theorems.
A ZERO exit means the baseline is keyed on the name again and every grandfathered declaration is
free to assume whatever it likes.

⚑ **THE CONTROLS ARE NOT DECORATION HERE — THEY ARE WHAT MAKES THE OTHER TWO MEAN ANYTHING.** All
four theorems below are pinned in `FloorRatchet.canaryPins`, and none of them appears in the real
baseline. The controls pin the two ways this tooth can go wrong in the direction a canary cannot
see:

  * `control_…_unchanged` — pinned floor set, unchanged. If the pins matched NOTHING (a typo in a
    floor name, a changed separator, a sort that stopped being deterministic) the two violations
    would still be reported and this file would still exit 1, for a reason with nothing to do with
    the key. This control failing is the only signal that the pins are live.
  * `control_…_drained` — pinned under TWO floors, assumes ONE. This is a PORT, the exact shape the
    in-flight `compressInjective` drain produces ~321 times, and it must not cost a red. If the
    rule were EQUALITY rather than SUBSET it would be reported here, and the campaign would be
    paying a build error for each of its own wins.

`floor_ratchet_check.sh` fails hard if the gate names a `control_`-prefixed theorem.

Two independent things guard this tooth, on purpose. This canary is the END-TO-END one (real
declarations, the real command, a real nonzero exit). The `#guard`s next to `rowAdmits` in
`Dregg2/Verify/FloorRatchet.lean` are the ALGEBRA one, and they need no environment — they run
whenever that module elaborates, which matters because this file cannot run at all unless the whole
root tree is green.

⚑ Nothing here touches a tracked file, so this is swarm-safe to run at any time, concurrently.
-/
import Dregg2

open Dregg2.Circuit.Poseidon2Binding
open Dregg2.Circuit.StateCommit (compressNInjective)

/-- ⚑ THE CONTROL. Pinned as `control_floor_ratchet_key_canary_unchanged ⊣ …Poseidon2SpongeCR`, and
it assumes exactly that one floor. It is as VACUOUS as the two violations below — that is the
point of a ratchet: a grandfathered pair stays grandfathered — so it must NOT be named. If it is,
the pins are not matching and the two violations below prove nothing. -/
theorem control_floor_ratchet_key_canary_unchanged {sponge : List ℤ → ℤ}
    (hCR : Poseidon2SpongeCR sponge) (xs ys : List ℤ) (h : sponge xs = sponge ys) : xs = ys :=
  hCR xs ys h

/-- ⚑ THE OTHER CONTROL, and the one that keeps this tooth usable. Pinned as
`control_floor_ratchet_key_canary_drained ⊣ …Poseidon2SpongeCR+…compressNInjective`, and it assumes
only the first: a declaration that SHED a refuted floor. That is a PORT — the campaign's own
output, ~321 declarations' worth in the in-flight `compressInjective` drain — and a grandfathered
row is an UPPER BOUND, so it must stay EXEMPT. It appearing in the violation list means the key
went to EQUALITY and every port now reds the root. -/
theorem control_floor_ratchet_key_canary_drained {sponge : List ℤ → ℤ}
    (hCR : Poseidon2SpongeCR sponge) (xs ys : List ℤ) (h : sponge xs = sponge ys) : xs = ys :=
  hCR xs ys h

/-- **THE ACQUISITION** — the measured case, 161 times over. Pinned under `Poseidon2SpongeCR`, and
it still assumes `Poseidon2SpongeCR`: nothing was removed, the declaration merely picked up a
SECOND refuted floor. Under a name-keyed baseline this is invisible, because the name is listed and
the first floor found is unchanged. -/
theorem floor_ratchet_key_canary_acquires {sponge cn : List ℤ → ℤ}
    (hCR : Poseidon2SpongeCR sponge) (_hCN : compressNInjective cn)
    (xs ys : List ℤ) (h : sponge xs = sponge ys) : xs = ys :=
  hCR xs ys h

/-- **THE SWAP** — drained of the floor it was grandfathered for, resting on a different one. Same
name, same conclusion shape, entirely different claim about the deployed system. Under a name-keyed
baseline the drain reads as a PORT (the old floor is gone) while the vacuity is untouched. -/
theorem floor_ratchet_key_canary_swapped {cn : List ℤ → ℤ}
    (hCN : compressNInjective cn) (xs ys : List ℤ) (h : cn xs = cn ys) : xs = ys :=
  hCN xs ys h

#floor_ratchet
