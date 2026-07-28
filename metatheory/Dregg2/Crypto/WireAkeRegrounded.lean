/-
# `Dregg2.Crypto.WireAkeRegrounded` — the DEPLOYED wire-handshake CHANNEL BINDING
RE-GROUNDED off the VACUOUS injective `HashCR` floor onto the KEYED COLLISION GAME
(`FloorGames.HashCRHardQuant F Eff`, adversary class IN THE STATEMENT).

⚑ The intermediate spelling `HashFloorHonesty.CollisionResistant` is DELETED (2026-07-28): it WAS
`HashCRHardQuant F (fun _ => True)` with the `⊤` folded into a name, and that `⊤` floor is itself FALSE
for every compressing hash (`FloorGames.hashCRHardQuant_top_false_of_compressing`) — the deployed
concat-KDF included. The `⊤`-class results below are stated with the `⊤` written out; the DISCHARGED
binding is §5's keyed-ROM successor.

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
  so under the collision floor `HashCRHardQuant (channelKeyFamily cr) Eff` its advantage is `Negl`. "equal
  key ⟹ equal transcript" becomes "⟹ equal transcript EXCEPT with negligible probability" — a key-reuse /
  UKS attack succeeds only with negligible advantage. `Eff` stays a PARAMETER: the discharge is §5's
  keyed-ROM floor, because the `⊤` class is refuted at the deployed compressing KDF.

## ⚑ The `IsPolyTime` discharge is DELETED; the DISCHARGED successor is §5's keyed-ROM binding (07-24)

`channel_binding_from_polyTime` discharged `Eff` at `CostAdversary.IsPolyTime`, whose floor
`HashCRHardQuant … (IsPolyTime …)` is REFUTED at deployed parameters
(`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` — `IsPolyTime` prices answer
SIZE, so a `.pure` answerer with a hardcoded short collision is in the class and wins with probability
`1`). It is DELETED, and §5 lands the successor on the PROVED keyed-ROM floor: the UKS forger is an
ORACLE PROGRAM (`RomOpenEff`, query-counted, oracle sampled AFTER the program is fixed), and
`channel_binding_rom` concludes `Negl` from `KeyedRomFloor.keyedRom_hard` (the birthday bound — a
THEOREM) with NOTHING refutable carried. The `_advantage_bound` form above stays as the honest
fixed-hash statement with `hEff` in the open.

## Non-fake

The `⊤`-class floor is SATISFIABLE (`channelKey_crK_CR`: the injective identity carrier `WireAke.crK`
discharges it) and REFUTABLE (`channelKey_badCR_not_CR`: the COLLIDING session-key hash `badChannelKey` has
a collision at every key, so `hashCRHardQuant_top_false_of_compressing` refutes the floor on it).

⚑ Those two poles are the whole shape of the `⊤` class: it holds exactly for the injective families and
fails exactly for the compressing ones. So `channelKey_crK_CR` says `crK` is NOT compressing — and the
deployed concat-KDF, which is, sits with `badChannelKey` on the refuted side. §5's keyed-ROM successor is
what carries the deployed claim.

The old injective-floor theorems (`channel_binding`, `channel_binding_transcript`, `uks_breaks_hashcr`) are
KEPT untouched; this file only ADDS the sibling. `#assert_all_clean` (⊆ {propext, Classical.choice,
Quot.sound}); no `sorry`, no fresh `axiom`, no `native_decide`.

## Coordination

This is the wire-AKE channel-binding commit-reveal leg. The generic template is `HermineHashCRRegrounded`;
the id-commit leg is `IdentityCommitmentRegrounded`; the STARK/FRI/apex-availability hash consumers are
`Circuit.FloorRegroundedConsumers`. It stays in the `WireAke` channel-binding subtree — no consumer moved
here lives elsewhere. `ake_authentication` / `ake_session_key_secure` are NOT touched: they already reduce to
the standard floor (`SchnorrDLHard ∨ MSISHard`, `MLWESearchHard`), not to the vacuous injective `HashCR`.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Crypto.WireAke

namespace Dregg2.Crypto.WireAkeRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv idFamily)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.HermineHashCRRegrounded
  (commitRevealFamily commitRevealFamily_CR_of_hashcr commitOpenGame openToFinder
   hermine_commitment_binding_advantage_bound crEquivocator)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv hashGame finderToAdv HashCRHardQuant
   hashCRHardQuant_top_false_of_compressing idFamily_hashCRHardQuant_top hard_bot_vacuous)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier)
open Dregg2.Crypto.RomCarrierSites
  (flatFamily taggedCarrier romOpenGame RomOpenEff rom_open_binds romOpen_forger_excluded
   romOpenAdv constOpenComp constOpen_in_eff constOpen_gameAdv_pos constOpen_binds)

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

⚑ **WHAT THIS SECTION USED TO EXPORT, AND WHY IT IS GONE.** `channel_binding_advantage_bound` took the
collision floor at the UNRESTRICTED class — `HashCRHardQuant (channelKeyFamily cr) (fun _ => True)`, then
written `CollisionResistant (channelKeyFamily cr)`, a spelling since DELETED — and
`FloorGames.hashCRHardQuant_top_false_of_compressing` proves THAT false for any compressing hash,
including the deployed concat-KDF, which maps a long framed
`(ss_x, ss_pq, transcript)` pre-image to a fixed-width session key. So the exported binding rested on a
hypothesis REFUTED at deployed parameters: vacuous, and vacuous in exactly the way the sweep exists to
name. Its `_eff` sibling took a `CollisionFinder` and applied the floor TO IT — hypothesis and conclusion
the same object, with the UKS attack never appearing in a `Prop`. BOTH ARE DELETED.

What stands here is the generic commit-opening REDUCTION (`HermineHashCRRegrounded` §2) instantiated at
the deployed session-key family: the break is a `Game` whose win relation says an adversary published a
session key together with two DISTINCT framed `(ss_x, ss_pq, transcript)` triples that BOTH derive it —
the unknown-key-share attack, on the deployed key — and the extractor DISCARDS the key to reach a genuine
collision. The advantage inequality is unconditional; the DISCHARGED instantiation is §5's keyed-ROM
binding (the `IsPolyTime` discharge that stood here is deleted — its floor is refuted). -/

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

/-! ## §3 — non-vacuity: the floor is satisfiable AND load-bearing on the channel-binding hash. -/

/-- **(TOOTH — the `⊤`-class floor is SATISFIABLE on the channel-binding hash.)** The honest
transcript-including carrier `WireAke.crK` (`H () p = p`, injective — the identity framing binds the
transcript) satisfies the keyed collision floor at the UNRESTRICTED class: the sibling hypothesis is
inhabited, unlike the vacuous injective floor.

⚑ And injectivity is the ONLY way to satisfy it (see `channelKey_badCR_not_CR`), so this witness says
`crK` is not compressing. The deployed concat-KDF is, and so cannot be on this side. -/
theorem channelKey_crK_CR :
    HashCRHardQuant (channelKeyFamily Dregg2.Crypto.WireAke.crK) (fun _ => True) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.WireAke.crK () Dregg2.Crypto.WireAke.crK_hashcr

/-- A COLLIDING session-key hash `H () _ = 0` — every framed `(ss_x, ss_pq, tr)` maps to one key, so any two
distinct channels share it (the transcript-blind concat-KDF `WireAke` warns of, as a hash). -/
def badChannelKey : CommitReveal Unit ℤ ℕ := ⟨fun _ _ => 0⟩

/-- **(TOOTH — the `⊤`-class floor is REFUTABLE on the channel-binding hash.)** The colliding
`badChannelKey` has a collision at EVERY key (`7 ≠ 8` yet both hash to `0`), so
`hashCRHardQuant_top_false_of_compressing` refutes the floor at the UNRESTRICTED class. The sibling cannot
be discharged on a transcript-blind session-key hash, exactly as `WireAke.uks_breaks_hashcr` shows the
channel stops binding once collision-resistance fails — and the argument needs only compression, so it
runs at the deployed concat-KDF too. -/
theorem channelKey_badCR_not_CR :
    ¬ HashCRHardQuant (channelKeyFamily badChannelKey) (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨(0 : ℤ)⟩
    (fun _ _ => ⟨(7 : ℤ), (8 : ℤ), ?_, rfl⟩)
  show (7 : ℤ) ≠ (8 : ℤ)
  norm_num

/-- **THE RE-GROUNDED CHANNEL BINDING FIRES AT A REAL FLOOR WITNESS.** On the injective identity family
(`FloorGames.idFamily_hashCRHardQuant_top`), the UKS-equivocation advantage is negligible — the channel
binding runs end-to-end to a genuine `Negl` conclusion at an inhabited floor hypothesis. (Inhabited
BECAUSE the family is injective; no compressing family reaches this witness.) -/
theorem channel_binding_fires (A : Adversary (commitOpenGame idFamily)) :
    Negl (gameAdv (commitOpenGame idFamily) A) :=
  hermine_commitment_binding_advantage_bound idFamily (fun _ => True) A trivial
    idFamily_hashCRHardQuant_top

/-! ## §4 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at the compressing session-key hash.)** The price of `hEff`, stated as
a theorem: the class cannot be left implicit, because the implicit `⊤` is the empty hypothesis the sweep
exists to name — refuted at the colliding `badChannelKey`.

⚑ This IS `channelKey_badCR_not_CR` — nothing is added. It used to bridge a `CollisionResistant`
refutation across `collisionResistant_iff_hashCRHardQuant_top`; with the `⊤` now written into the tooth's
own statement, the bridge is the identity. Both names are kept because `Verify/FloorRatchetBaseline`
grandfathers refuted-floor carriers BY NAME. -/
theorem channelKey_eff_top_false :
    ¬ HashCRHardQuant (channelKeyFamily badChannelKey) (fun _ => True) :=
  channelKey_badCR_not_CR

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
injective floor), so the `Eff` gate runs end-to-end to a genuine `Negl`. Read with
`channelKey_eff_top_false`: it fires HERE and cannot fire at a compressing KDF, which is why the deployed
discharge is §5. -/
theorem channel_binding_eff_fires (A : Adversary (uksGame Dregg2.Crypto.WireAke.crK)) :
    Negl (gameAdv (uksGame Dregg2.Crypto.WireAke.crK) A) :=
  channel_binding_advantage_bound Dregg2.Crypto.WireAke.crK (fun _ => True) A trivial
    channelKey_crK_CR

/-! ## §5 — ⚑⚑ THE DISCHARGED SUCCESSOR: the UKS binding on the PROVED keyed-ROM floor.

⚑ **THE MODELLING STEP, STATED (not smuggled).** The deployed concat-KDF `cr.H ()` is idealised as ONE
SAMPLED oracle `H : Unit × Pre → Fin (2 ^ l)` over the (finite, truncated-deployed-shape) framed
`(ss_x, ss_pq, transcript)` pre-image space `Pre` — the standard ROM idealisation of the fixed KDF at
an ASYMPTOTIC key width, exactly `RomCarrierSites`' header: a deliberate labelled modelling step, NOT a
derivation about the fixed public function; there is no `l` at which `Fin (2 ^ l)` IS the deployed
fixed-width session key. What it buys: the floor under the binding is `KeyedRomFloor.keyedRom_hard`
(the birthday bound, PROVED) where the deleted `_from_polyTime` form carried a hypothesis that is
FALSE. The break keeps the §2 commitOpenGame SHAPE: the PUBLISHED session key is in the win relation
(`romOpenGame`), the forger is a query-counted oracle program fixed BEFORE the oracle is sampled. -/

section RomSuccessor

variable (Pre : Type) [Fintype Pre] [DecidableEq Pre] [Nonempty Pre]

/-- **THE UKS KEYED-ROM FAMILY** — the deployed session-key KDF as a sampled oracle over the framed
pre-image space (`Unit` tag: the deployed KDF has a single domain-separation slot; the KEYING is the
oracle sampling itself), ideal `λ`-bit session keys. -/
def uksRomFamily : KeyedRomFamily :=
  flatFamily Unit inferInstance inferInstance inferInstance (fun _ => Pre)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)

/-- The family's width obligation, closed by construction — no site-side width fact survives. -/
theorem uksRomFamily_card_R (l : ℕ) :
    letI := (uksRomFamily Pre).rFin l
    Fintype.card ((uksRomFamily Pre).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE UKS CARRIER** — the session key is one oracle query at the framed pre-image; the encoding is
the identity in the payload, injective on the nose (the framing injectivity `WireAke.channel_binding`
carries lives in the pre-image space itself here). -/
def uksRomCarrier : RomCarrier (uksRomFamily Pre) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => Pre) (fun _ => inferInstance)
    (fun _ _ p => p) (fun _ _ _ _ h => h)

/-- **THE UKS BREAK AT THE SAMPLED ORACLE** — the §2 shape verbatim: the adversary PUBLISHES a session
key and exhibits two DISTINCT framed pre-images that BOTH derive it. -/
abbrev uksRomGame : Game := romOpenGame (uksRomFamily Pre) (uksRomCarrier Pre)

/-- **THE DEPLOYED UKS ATTACK IS A WIN** — two distinct framed `(ss_x, ss_pq, transcript)` pre-images
whose sampled-oracle keys both equal the published key `k` are a win of the game, by the win relation
itself (`WireAke.uks_breaks_hashcr`, restated at the sampled oracle). -/
theorem uksRom_forgery_is_break (l : ℕ) (H : (uksRomGame Pre).Inst l) (k : Fin (2 ^ l))
    {p p' : Pre} (hne : p ≠ p') (h1 : H ((), p) = k) (h2 : H ((), p') = k) :
    (uksRomGame Pre).wins l H (k, ((), ()), p, p') :=
  ⟨hne, h1, h2⟩

/-- **⚑⚑ THE RE-GROUNDED CHANNEL BINDING — floor PROVED, nothing refutable carried.** Every
query-bounded UKS forger has NEGLIGIBLE advantage: one published session key derives from ONE channel
except with negligible probability, in the keyed ROM model of the header. The hypotheses are a
polynomial query budget and the forger's membership in the query class. This is what
`channel_binding_from_polyTime` (DELETED — floor refuted) claimed and could not have. -/
theorem channel_binding_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (uksRomGame Pre))
    (hA : RomOpenEff (uksRomFamily Pre) (uksRomCarrier Pre) Q A) :
    Negl (gameAdv (uksRomGame Pre) A) :=
  rom_open_binds _ _ Q hQ (uksRomFamily_card_R Pre) A hA

/-- **(TOOTH — the counterexample DIES.)** A UKS forger with non-negligible advantage is OUTSIDE the
query class: the answer-size strategy that refutes the `IsPolyTime` floor cannot produce a member. -/
theorem uksRom_nonNegl_forger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (uksRomGame Pre)) (hnn : ¬ Negl (gameAdv (uksRomGame Pre) A)) :
    ¬ RomOpenEff (uksRomFamily Pre) (uksRomCarrier Pre) Q A :=
  romOpen_forger_excluded _ _ Q hQ (uksRomFamily_card_R Pre) A hnn

/-- **(TOOTH — admitted, winnable, DEFANGED, at a CLOSED instance.)** At `Pre = Fin 4`, `Q = 2`: the
`0`-query hardcoded opener — the exact shape that refutes the `IsPolyTime` floor with probability `1` —
is IN the class, wins with POSITIVE probability at every parameter, and its advantage is NEGLIGIBLE.
The whole successor spine elaborates end-to-end at a closed instance; the counterexample dies by
keying, not by exclusion. -/
theorem uksRom_fires :
    (RomOpenEff (uksRomFamily (Fin 4)) (uksRomCarrier (Fin 4)) (fun _ => 2)
        (romOpenAdv _ _ (constOpenComp _ (uksRomCarrier (Fin 4))
          (fun l => (0 : Fin (2 ^ l))) (fun _ => ((), ())) (fun _ => (0 : Fin 4))
          (fun _ => (1 : Fin 4)))))
    ∧ (∀ l, 0 < gameAdv (uksRomGame (Fin 4))
        (romOpenAdv _ _ (constOpenComp _ (uksRomCarrier (Fin 4))
          (fun l => (0 : Fin (2 ^ l))) (fun _ => ((), ())) (fun _ => (0 : Fin 4))
          (fun _ => (1 : Fin 4)))) l)
    ∧ Negl (gameAdv (uksRomGame (Fin 4))
        (romOpenAdv _ _ (constOpenComp _ (uksRomCarrier (Fin 4))
          (fun l => (0 : Fin (2 ^ l))) (fun _ => ((), ())) (fun _ => (0 : Fin 4))
          (fun _ => (1 : Fin 4))))) := by
  refine ⟨constOpen_in_eff _ _ _ _ _ _ _,
    fun l => constOpen_gameAdv_pos _ _ _ _ _ _ l (by show (0 : Fin 4) ≠ 1; decide),
    constOpen_binds _ _ _ _ _ _ (fun _ => 2) ⟨1, 5, ?_⟩ (uksRomFamily_card_R (Fin 4))⟩
  filter_upwards [Filter.eventually_ge_atTop 5] with n hn
  have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith

end RomSuccessor

#assert_all_clean [
  uksGame_wins_iff,
  channel_binding_advantage_bound,
  sessionKey_eq_family,
  channelKey_crK_CR,
  channelKey_badCR_not_CR,
  channel_binding_fires,
  channelKey_eff_top_false,
  channelKey_eff_bot_vacuous,
  channel_binding_eff_fires,
  uksRomFamily_card_R,
  uksRom_forgery_is_break,
  channel_binding_rom,
  uksRom_nonNegl_forger_excluded,
  uksRom_fires
]

end Dregg2.Crypto.WireAkeRegrounded
