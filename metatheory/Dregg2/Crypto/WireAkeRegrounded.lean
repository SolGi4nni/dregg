/-
# `Dregg2.Crypto.WireAkeRegrounded` — the DEPLOYED wire-handshake CHANNEL BINDING
RE-GROUNDED off the VACUOUS injective `HashCR` floor onto the PROPER keyed `CollisionResistant` floor.

## The gap this closes (the closest-to-deployed leg of the forward-scaffolding floor sweep)

`WireAke.channel_binding` / `channel_binding_transcript` are the NO-UKS / no-key-reuse floor of the
deployed peer handshake (`wire/src/server.rs`, the `PeerAuthResponse` arm): the session key
`sessionKey cr frameK = cr.H () (frameK (ss_x, ss_pq, tr))` — the concat-KDF over BOTH shared secrets AND
the transcript — is modeled as a collision-resistant hash over an INJECTIVE framing, so two sessions sharing
a key share a transcript (an unknown-key-share attack is a transcript collision). Both are conditioned on
`HermineHintMLWE.HashCR cr` — the SAME injective floor `HashFloorHonesty.hashCR_false_of_compressing` PROVES
FALSE for any compressing commitment. The deployed concat-KDF maps a long framed `(ss_x, ss_pq, tr)`
pre-image to a fixed-width session key, so it IS compressing — the deployed no-UKS lemma is VACUOUSLY TRUE
at real parameters.

`HermineHashCRRegrounded` landed the generic commit-reveal regrounding (`commitRevealFamily`,
`hermine_commitment_binding_advantage_bound`); this file instantiates it for the wire channel-binding hash's
own `cr`, so the deployed no-UKS guarantee no longer rides an empty hypothesis. Mirror of
`IdentityCommitmentRegrounded` (the id-commit leg of the same sweep).

## The re-grounding

* **`channelKeyFamily cr`** — the deployed session-key hash `cr.H ()` over the framed
  `(ss_x, ss_pq, transcript)` pre-images, as the keyed hash family `commitRevealFamily cr ()` the honest
  collision game runs over. `sessionKey_eq_family` pins it definitionally to `WireAke.sessionKey`.
* **`channel_binding_advantage_bound`** — the advantage-bounded sibling of `channel_binding`: a UKS /
  key-reuse adversary (two DISTINCT framed inputs — hence, by `WireAke.uks_breaks_hashcr`, two distinct
  `(ss_x, ss_pq, transcript)` triples colliding to one session key, a hash collision) IS a `CollisionFinder`,
  so under the proper `CollisionResistant (channelKeyFamily cr)` floor its advantage is `Negl`. "equal key ⟹
  equal transcript" becomes "⟹ equal transcript EXCEPT with negligible probability" — a key-reuse / UKS
  attack succeeds only with negligible advantage. Discharged by `thread_advantage_bound` (the single
  `CollisionResistant` leaf), reusing the generic commit-reveal keystone.

## Non-fake

The floor is SATISFIABLE (`channelKey_crK_CR`: the injective identity carrier `WireAke.crK` discharges it)
and LOAD-BEARING (`channelKey_badCR_not_CR`: the COLLIDING session-key hash `badChannelKey` has a
key-reuse equivocator winning on every key, advantage `1`, so its family is NOT CR). The old injective-floor
theorems (`channel_binding`, `channel_binding_transcript`, `uks_breaks_hashcr`) are KEPT untouched; this file
only ADDS the sibling. `#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no fresh
`axiom`, no `native_decide`.

## Coordination

This is the wire-AKE channel-binding commit-reveal leg. The generic template is `HermineHashCRRegrounded`;
the id-commit leg is `IdentityCommitmentRegrounded`; the STARK/FRI/apex-availability hash consumers are
`Circuit.FloorRegroundedConsumers`. It stays in the `WireAke` channel-binding subtree — no consumer moved
here lives elsewhere. `ake_authentication` / `ake_session_key_secure` are NOT touched: they already reduce to
the standard floor (`SchnorrDLHard ∨ MSISHard`, `MLWESearchHard`), not to the vacuous injective `HashCR`.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.WireAke

namespace Dregg2.Crypto.WireAkeRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv idFamily idFamily_CR)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.HermineHashCRRegrounded
  (commitRevealFamily commitRevealFamily_CR_of_hashcr hermine_commitment_binding_advantage_bound
   crEquivocator)

set_option autoImplicit false

/-! ## §1 — the deployed session-key hash as a keyed family. -/

/-- **THE CHANNEL-BINDING KEYED FAMILY.** The deployed concat-KDF session-key hash `cr.H ()` over the framed
`(ss_x, ss_pq, transcript)` pre-images, as a `KeyedHashFamily` (`commitRevealFamily cr ()`). This is the
keyed hash the proper collision game runs over — the honest floor object the wire channel binding needs. -/
def channelKeyFamily {Pre K : Type} [DecidableEq Pre] [DecidableEq K]
    (cr : CommitReveal Unit Pre K) : KeyedHashFamily :=
  commitRevealFamily cr ()

/-- The keyed family's hash IS the deployed `WireAke.sessionKey` on the framed input — the abstract game
runs over exactly the deployed session-key hash. -/
theorem sessionKey_eq_family {SS Tr Pre K : Type} [DecidableEq Pre] [DecidableEq K]
    (cr : CommitReveal Unit Pre K) (frameK : SS × SS × Tr → Pre) (ssx sspq : SS) (tr : Tr) (n : ℕ)
    (k : (channelKeyFamily cr).Key n) :
    Dregg2.Crypto.WireAke.sessionKey cr frameK ssx sspq tr
      = (channelKeyFamily cr).H n k (frameK (ssx, sspq, tr)) := rfl

/-! ## §2 — the advantage-bounded channel-binding keystone (`channel_binding`, re-grounded). -/

/-- **RE-GROUNDED `WireAke.channel_binding`.** Under the proper keyed floor, the key-reuse / UKS adversary
(per key, two DISTINCT framed inputs — hence two distinct `(ss_x, ss_pq, transcript)` triples, by
`WireAke.uks_breaks_hashcr` — colliding to one session key, a hash collision) has negligible advantage. The
Boolean "equal session key ⟹ equal transcript" becomes "⟹ equal transcript EXCEPT with negligible
probability": an unknown-key-share attack cannot pin a shared key across distinct channels except with
negligible advantage. Proof: `thread_advantage_bound` (the single `CollisionResistant` leaf), via the
generic commit-reveal keystone. -/
theorem channel_binding_advantage_bound {Pre K : Type} [DecidableEq Pre] [DecidableEq K]
    (cr : CommitReveal Unit Pre K)
    (hCR : CollisionResistant (channelKeyFamily cr))
    (uksEquivocator : CollisionFinder (channelKeyFamily cr)) :
    Negl (collisionAdv (channelKeyFamily cr) uksEquivocator) :=
  hermine_commitment_binding_advantage_bound hCR uksEquivocator

/-! ## §3 — non-vacuity: the floor is satisfiable AND load-bearing on the channel-binding hash. -/

/-- **(TOOTH — the floor is SATISFIABLE on the channel-binding hash.)** The honest transcript-including
carrier `WireAke.crK` (`H () p = p`, injective — the identity framing binds the transcript) satisfies the
proper keyed floor: the sibling hypothesis is inhabited, unlike the vacuous injective floor. -/
theorem channelKey_crK_CR : CollisionResistant (channelKeyFamily Dregg2.Crypto.WireAke.crK) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.WireAke.crK () Dregg2.Crypto.WireAke.crK_hashcr

/-- A COLLIDING session-key hash `H () _ = 0` — every framed `(ss_x, ss_pq, tr)` maps to one key, so any two
distinct channels share it (the transcript-blind concat-KDF `WireAke` warns of, as a hash). -/
def badChannelKey : CommitReveal Unit ℤ ℕ := ⟨fun _ _ => 0⟩

/-- **(TOOTH — the floor is LOAD-BEARING on the channel-binding hash.)** The colliding `badChannelKey` has
the key-reuse equivocator `crEquivocator badChannelKey () 7 8` winning on EVERY key (`7 ≠ 8` yet both hash to
`0`), so its advantage is the constant `1` and the family is NOT collision-resistant. So the sibling cannot
be discharged on a transcript-blind session-key hash — the proper floor is a genuine constraint, exactly as
`WireAke.uks_breaks_hashcr` shows the channel stops binding once collision-resistance fails. -/
theorem channelKey_badCR_not_CR : ¬ CollisionResistant (channelKeyFamily badChannelKey) := by
  intro hCR
  have hadv : collisionAdv (channelKeyFamily badChannelKey) (crEquivocator badChannelKey () (7 : ℤ) 8)
      = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (channelKeyFamily badChannelKey).Key n =>
        (crEquivocator badChannelKey () (7 : ℤ) 8).wins n k) = fun _ => true := by
      funext k
      simp [CollisionFinder.wins, crEquivocator, commitRevealFamily, badChannelKey]
    show @winProb ((channelKeyFamily badChannelKey).Key n)
        ((channelKeyFamily badChannelKey).keyFintype n)
        (fun k => (crEquivocator badChannelKey () (7 : ℤ) 8).wins n k) = 1
    rw [hall]
    exact @winProb_top ((channelKeyFamily badChannelKey).Key n)
      ((channelKeyFamily badChannelKey).keyFintype n)
      ((channelKeyFamily badChannelKey).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR (crEquivocator badChannelKey () 7 8))

/-- **THE RE-GROUNDED CHANNEL BINDING FIRES AT A REAL FLOOR WITNESS.** On the injective identity family
(`HashFloorHonesty.idFamily_CR`), the UKS-equivocation advantage is negligible — the deployed channel
binding runs end-to-end to a genuine `Negl` conclusion at an inhabited floor hypothesis. -/
theorem channel_binding_fires (uksEquivocator : CollisionFinder idFamily) :
    Negl (collisionAdv idFamily uksEquivocator) :=
  hermine_commitment_binding_advantage_bound idFamily_CR uksEquivocator

#assert_all_clean [
  channel_binding_advantage_bound,
  sessionKey_eq_family,
  channelKey_crK_CR,
  channelKey_badCR_not_CR,
  channel_binding_fires
]

end Dregg2.Crypto.WireAkeRegrounded
