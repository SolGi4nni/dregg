/-
# floor_ratchet_canary_bundle.lean — THE B3 TOOTH, CAUGHT IN THE ACT OF BITING.

The sibling of `floor_ratchet_canary.lean`, for the bypass that canary could never have caught.

## What B3 was

`#floor_ratchet` closed its floor set to a fixpoint over `Prop`-valued DEFS: a def whose BODY
mentions a floor carries that floor, and so do its users. It did NOT propagate through STRUCTURE
FIELDS. So a structure like `Poseidon2RealizedSponge` — whose `spongeCR` field is typed at
`Poseidon2SpongeCR`, a hypothesis this tree PROVES FALSE at deployed BabyBear parameters, making
the structure UNINHABITABLE there — was itself grandfathered, and a BRAND-NEW theorem taking it as
a hypothesis added **zero carriers**:

    theorem b3_via_grandfathered_bundle (R : Poseidon2RealizedSponge s) … : xs = ys :=
      R.spongeCR xs ys h

Measured on a HEAD-pinned green tree before the fix: `lake env lean` on this exact file returned
**EXIT=0**, `1600 grandfathered carriers` — identical to the run without it. The declaration is as
vacuous as a floor binder and the gate had nothing to say. Thirty-two such bundles were
grandfathered; `Dregg2.Circuit.CircuitSoundness.CommitSurface` carries FOUR refuted floors as
fields and is reached by 409 declarations.

## What this file asserts

    cd metatheory && lake env lean scripts/floor_ratchet_canary_bundle.lean

**EXPECTED: EXIT=1**, with `⚑ FLOOR-RATCHET:` and the name `b3_via_grandfathered_bundle`.
A ZERO exit means the joint prop-body × bundle fixpoint has stopped propagating through fields and
the bypass is open again.

Two independent things guard that fixpoint, on purpose. This canary is the END-TO-END one (a real
declaration, the real command, a real nonzero exit). `FloorRatchet.sentinelBundles` is the
IN-BUILD one: five named structures that must be rediscovered as floor-carrying or the root build
fails closed. A canary can be deleted without a signal; a fail-closed sentinel cannot fire on a
tree nobody built. Both, or neither means anything.

⚑ Nothing here touches a tracked file, so this is swarm-safe to run at any time, concurrently.
-/
import Dregg2

open Dregg2.Circuit.Poseidon2Binding

/-- THE VIOLATION. The floor arrives through a grandfathered STRUCTURE instead of a binder, and
the conclusion is an equation — so neither the binder scan nor the anti-floor exemption applies.
Exactly as vacuous as `floor_ratchet_canary.lean`'s theorem, and invisible before B3 closed. -/
theorem b3_via_grandfathered_bundle {sponge : List ℤ → ℤ}
    (R : Poseidon2RealizedSponge sponge) (xs ys : List ℤ)
    (h : sponge xs = sponge ys) : xs = ys := R.spongeCR xs ys h

#floor_ratchet
