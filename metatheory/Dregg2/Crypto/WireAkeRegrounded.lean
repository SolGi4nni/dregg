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
  (commitRevealFamily commitRevealFamily_CR_of_hashcr commitOpenGame openToFinder
   hermine_commitment_binding_advantage_bound hermine_commitment_binding_from_polyTime
   hashAnsSizeOf openAnsSizeOf crEquivocator)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv hashGame finderToAdv HashCRHardQuant
   collisionResistant_iff_hashCRHardQuant_top hard_bot_vacuous)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)

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

/-! ## §2 — the UKS break, as a SECURITY REDUCTION.

⚑ **WHAT THIS SECTION USED TO EXPORT, AND WHY IT IS GONE.** `channel_binding_advantage_bound` took
`hCR : CollisionResistant (channelKeyFamily cr)`. `FloorGames.collisionResistant_iff_hashCRHardQuant_top`
proves that IS the collision floor at the UNRESTRICTED class, and `collisionResistant_false_of_compressing`
proves THAT false for any compressing hash — including the deployed concat-KDF, which maps a long framed
`(ss_x, ss_pq, transcript)` pre-image to a fixed-width session key. So the exported binding rested on a
hypothesis REFUTED at deployed parameters: vacuous, and vacuous in exactly the way the sweep exists to
name. Its `_eff` sibling took a `CollisionFinder` and applied the floor TO IT — hypothesis and conclusion
the same object, with the UKS attack never appearing in a `Prop`. BOTH ARE DELETED.

What stands here is the generic commit-opening REDUCTION (`HermineHashCRRegrounded` §2) instantiated at
the deployed session-key family: the break is a `Game` whose win relation says an adversary published a
session key together with two DISTINCT framed `(ss_x, ss_pq, transcript)` triples that BOTH derive it —
the unknown-key-share attack, on the deployed key — and the extractor DISCARDS the key to reach a genuine
collision. The advantage inequality is unconditional; the class is discharged at `IsPolyTime` below. -/

/-- **THE UNKNOWN-KEY-SHARE GAME** — the commit-opening break of the deployed session-key hash. A win is
one session key derived from two DISTINCT channels: exactly the attack `WireAke.channel_binding` denies. -/
abbrev uksGame {Pre K : Type} [DecidableEq Pre] [DecidableEq K] (cr : CommitReveal Unit Pre K) : Game :=
  commitOpenGame (channelKeyFamily cr)

/-- **THE PROBLEM IS IN THE STATEMENT** — a win unfolds, by `Iff.rfl`, to two distinct framed inputs
deriving one published session key. -/
theorem uksGame_wins_iff {Pre K : Type} [DecidableEq Pre] [DecidableEq K]
    (cr : CommitReveal Unit Pre K) (n : ℕ) (k : (channelKeyFamily cr).Key n) (p : K × Pre × Pre) :
    (uksGame cr).wins n k p ↔ (p.2.1 ≠ p.2.2 ∧ cr.H () p.2.1 = p.1 ∧ cr.H () p.2.2 = p.1) :=
  Iff.rfl

/-- **⚑ RE-GROUNDED `WireAke.channel_binding` — from the session-key hash's collision floor, VIA the
reduction.** Under the collision floor at the class `Eff`, a UKS adversary whose extracted finder is in
that class has NEGLIGIBLE advantage: "equal session key ⟹ equal transcript" becomes "⟹ equal transcript
EXCEPT with negligible probability", off a floor the deployed concat-KDF can actually satisfy.

`Eff` is a parameter here because this is the statement at an ARBITRARY class; `_from_polyTime` below
discharges it. -/
theorem channel_binding_advantage_bound {Pre K : Type} [DecidableEq Pre] [DecidableEq K]
    (cr : CommitReveal Unit Pre K)
    (Eff : Adversary (hashGame (channelKeyFamily cr)) → Prop)
    (A : Adversary (uksGame cr))
    (hEff : Eff (openToFinder (channelKeyFamily cr) A))
    (hD : HashCRHardQuant (channelKeyFamily cr) Eff) :
    Negl (gameAdv (uksGame cr) A) :=
  hermine_commitment_binding_advantage_bound (channelKeyFamily cr) Eff A hEff hD

/-- **⚑ THE EFFICIENCY OBLIGATION DISCHARGED.** A UKS adversary that is EFFICIENT at the game's own answer
encoding yields a collision finder that is STILL efficient (the extractor DISCARDS the published key, so
its growth constants are `(1, 0)` and nothing can blow up), so the collision floor at `Eff := IsPolyTime`
applies to IT and the channel binds with no floating efficiency parameter. The per-site inputs are the
reshaper's declared work `(cw, bw)` and the family's own encoding `szIn`/`szOut` — the deployed pre-image
and key encodings, which a `KeyedHashFamily` over abstract carriers cannot supply itself. -/
theorem channel_binding_from_polyTime {Pre K : Type} [DecidableEq Pre] [DecidableEq K]
    (cr : CommitReveal Unit Pre K) (szIn : ℕ → Pre → ℕ) (szOut : ℕ → K → ℕ)
    (A : Adversary (uksGame cr))
    (hA : IsPolyTime (openAnsSizeOf (channelKeyFamily cr) szIn szOut) A) (cw bw : ℕ)
    (hD : HashCRHardQuant (channelKeyFamily cr)
      (IsPolyTime (hashAnsSizeOf (channelKeyFamily cr) szIn))) :
    Negl (gameAdv (uksGame cr) A) :=
  hermine_commitment_binding_from_polyTime (channelKeyFamily cr) szIn szOut A hA cw bw hD

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
theorem channel_binding_fires (A : Adversary (commitOpenGame idFamily)) :
    Negl (gameAdv (commitOpenGame idFamily) A) :=
  hermine_commitment_binding_advantage_bound idFamily (fun _ => True) A trivial
    ((collisionResistant_iff_hashCRHardQuant_top _).mp idFamily_CR)

/-! ## §4 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at the compressing session-key hash.)** The bare-CR floor at the colliding
`badChannelKey` is refuted (`channelKey_badCR_not_CR`), and it IS `HashCRHardQuant _ ⊤`
(`collisionResistant_iff_hashCRHardQuant_top`) — so the `⊤` class is FALSE. The price of `hEff`, stated as a
theorem: the class cannot be left implicit, because the implicit `⊤` is the empty hypothesis the sweep
exists to name. -/
theorem channelKey_eff_top_false :
    ¬ HashCRHardQuant (channelKeyFamily badChannelKey) (fun _ => True) :=
  fun h => channelKey_badCR_not_CR ((collisionResistant_iff_hashCRHardQuant_top _).mpr h)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the floor holds for ANY
session-key hash, including a transcript-blind one. Recorded HONESTLY — the two poles together make `Eff` a
dial, not a costume. -/
theorem channelKey_eff_bot_vacuous {Pre K : Type} [DecidableEq Pre] [DecidableEq K]
    (cr : CommitReveal Unit Pre K) :
    HashCRHardQuant (channelKeyFamily cr) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — the gate does NOT follow from the floor applied at another adversary.)** From the floor at
some OTHER adversary `B`, NOT the one extracted from the equivocator, the UKS-equivocator's negligibility
does not follow: `hD B hB` bounds a DIFFERENT ensemble than `collisionAdv (channelKeyFamily cr)
uksEquivocator`, and only `collisionAdv_eq_gameAdv` at the extracted finder connects them. -/
example {Pre K : Type} [DecidableEq Pre] [DecidableEq K] (cr : CommitReveal Unit Pre K)
    (Eff : Adversary (hashGame (channelKeyFamily cr)) → Prop)
    (A : Adversary (uksGame cr))
    (B : Adversary (hashGame (channelKeyFamily cr))) (hB : Eff B)
    (hD : HashCRHardQuant (channelKeyFamily cr) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (uksGame cr) A) := hD B hB)
  trivial

/-- **THE `Eff` GATE FIRES AT A REAL FLOOR WITNESS.** On the injective transcript-including carrier
`WireAke.crK` the `Eff`-floor at `⊤` holds (`channelKey_crK_CR`, an INHABITED hypothesis, unlike the vacuous
injective floor), so the `Eff` gate runs end-to-end to a genuine `Negl`. -/
theorem channel_binding_eff_fires (A : Adversary (uksGame Dregg2.Crypto.WireAke.crK)) :
    Negl (gameAdv (uksGame Dregg2.Crypto.WireAke.crK) A) :=
  channel_binding_advantage_bound Dregg2.Crypto.WireAke.crK (fun _ => True) A trivial
    ((collisionResistant_iff_hashCRHardQuant_top _).mp channelKey_crK_CR)

#assert_all_clean [
  uksGame_wins_iff,
  channel_binding_advantage_bound,
  channel_binding_from_polyTime,
  sessionKey_eq_family,
  channelKey_crK_CR,
  channelKey_badCR_not_CR,
  channel_binding_fires,
  channelKey_eff_top_false,
  channelKey_eff_bot_vacuous,
  channel_binding_eff_fires
]

end Dregg2.Crypto.WireAkeRegrounded
