/-
# `Dregg2.Crypto.SpongeCarrierBridge` — `SpongeCarrierReduction.SpongeKeyed` IS
`Poseidon2KeyedBridge.DomainSeparatedSponge`, PROVED.

`SpongeCarrierReduction` restates the deployed keyed sponge low in the import graph, because the
carriers it has to serve (`Circuit.OodCommitmentBinding` and everything above it) sit BELOW
`Circuit.Poseidon2KeyedBridge` — which reaches them through `FloorRegroundedConsumers`. Restating an
interface is exactly how a swarm ends up with a MIRROR: two structures that look alike, drift apart,
and verify against each other's reconstruction instead of the real object.

This file removes that risk by discharging the identification instead of asserting it. Every theorem
below is `rfl`:

  * `spongeKeyed_ofDomainSeparated` converts the deployed bundle,
  * `spongeFamily_ofDomainSeparated` proves the two KEYED FAMILIES are the SAME `KeyedHashFamily`,
  * `hashGame_ofDomainSeparated` proves the two COLLISION GAMES are the same `Game`, and
  * `floor_iff_domainSeparatedCREff` proves the two FLOORS are the same `Prop`.

So a reduction landed on `SpongeCarrierReduction`'s floor is landed on
`DomainSeparatedCREffRegrounded.DomainSeparatedCREff` — the deployed-sponge floor the rest of the tree
already prices — and `Poseidon2KeyedBridge`'s faithfulness lemmas (`deployed_hash_is_family_instance`,
`wins_iff_deployed_collision`) apply to it verbatim.

No `sorry`, no `axiom`.
-/
import Dregg2.Crypto.SpongeCarrierReduction
import Dregg2.Circuit.DomainSeparatedCREffRegrounded

namespace Dregg2.Crypto.SpongeCarrierBridge

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed spongeFamily)
open Dregg2.Circuit.Poseidon2KeyedBridge (DomainSeparatedSponge poseidon2KeyedFamily)
open Dregg2.Circuit.DomainSeparatedCREffRegrounded (DomainSeparatedCREff)
open Dregg2.Crypto.FloorGames (Game Adversary hashGame HashCRHardQuant)

set_option autoImplicit false

/-- The deployed bundle, converted. Field-for-field: there is nothing to get wrong, and the theorems
below prove there was nothing got wrong. -/
def spongeKeyed_ofDomainSeparated (D : DomainSeparatedSponge) : SpongeKeyed where
  sponge := D.sponge
  Tag := D.Tag
  tagFintype := D.tagFintype
  tagNonempty := D.tagNonempty
  tagCode := D.tagCode
  deployedTag := D.deployedTag

/-- **⚑ THE SAME KEYED FAMILY.** The spine's family at a converted bundle IS `Poseidon2KeyedBridge`'s
family at the original — by `rfl`, so every faithfulness lemma proved about one holds of the other. -/
theorem spongeFamily_ofDomainSeparated (D : DomainSeparatedSponge) :
    spongeFamily (spongeKeyed_ofDomainSeparated D) = poseidon2KeyedFamily D := rfl

/-- **THE SAME COLLISION GAME** — hence the same adversaries, the same advantage, the same everything
a reduction can land on. -/
theorem hashGame_ofDomainSeparated (D : DomainSeparatedSponge) :
    hashGame (spongeFamily (spongeKeyed_ofDomainSeparated D)) = hashGame (poseidon2KeyedFamily D) :=
  rfl

/-- **⚑ THE SAME FLOOR.** A reduction discharged against the spine's floor is discharged against the
deployed-sponge floor `DomainSeparatedCREff` that `DomainSeparatedCREffRegrounded` prices at both
poles. The spine is not a private assumption; it is the tree's own. -/
theorem floor_iff_domainSeparatedCREff (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop) :
    HashCRHardQuant (spongeFamily (spongeKeyed_ofDomainSeparated D)) Eff ↔
      DomainSeparatedCREff D Eff :=
  Iff.rfl

/-- The deployed fixed function is the same one on both sides. -/
theorem deployedHash_ofDomainSeparated (D : DomainSeparatedSponge) :
    (spongeKeyed_ofDomainSeparated D).deployedHash = D.deployedHash := rfl

#assert_axioms spongeFamily_ofDomainSeparated
#assert_axioms hashGame_ofDomainSeparated
#assert_axioms floor_iff_domainSeparatedCREff
#assert_axioms deployedHash_ofDomainSeparated

end Dregg2.Crypto.SpongeCarrierBridge
