/-
# `Dregg2.Crypto.ForkingDischargeConsumers` — THREADING the discharge through the protocol layer.

`ForkingDischarge` retired the deterministic forking-extractor hypothesis at the keystone. This file
threads that discharge through every consumer of it.

## The uniform shape

Each protocol game in `Dregg2/Crypto/` is TWO theorems:

  * an inner, fork-FREE soundness theorem taking `heuf : EufCma S pk Q` — `chain_unforgeable_under_eufcma`,
    `turn_sound`, `downgrade_resistant`, `revocation_sound`, `no_two_conflicting_finalized`,
    `no_forged_block`, `ake_authentication`, `ucRealizes_iff_eufCma`, `multi_session_realization`;
  * an outer `…_under_floor` wrapper that produces that `EufCma` from
    `HybridCombiner.hybrid_secure_if_either_floor` — and therefore TAKES the two un-discharged forking
    reductions `dlFork` / `msisFork` and passes them straight through.

So the fork hypothesis enters the protocol layer at exactly ONE point per consumer, and always the same
one. Replacing that one call with `ForkingDischarge.hybrid_secure_if_either_floor_discharged` retires it
everywhere: the wrappers below are the ORIGINAL consumers with `dlFork` and `msisFork` DELETED, the two
REALIZABILITY bridges in their place, and the classical floor moved to the field-scalar
`SchnorrEufCma.SchnorrDLHardF` — the floor the Schnorr forking reduction is actually PROVED against.

## What each wrapper still assumes, precisely

  * the two hardness FLOORS (`SchnorrDLHardF ∨ MSISHard`) — irreducible, as they must be;
  * `ForgeryRealizable` / `ClassicalForgeryRealizable` — MODELLING bridges saying the abstract game's bare
    `∃`-forgery is produced by an actual adversary with a prefix world and a rewindable challenge. They
    assume nothing cryptographic;
  * whatever protocol-level hypotheses the game already had (quorum bounds, honest-signing rules, circuit
    soundness, hash collision-resistance …) — untouched.

The forking extraction — rewind, shared commitment/nonce, distinct challenges, MSIS/DL witness — is PROVED
and appears in NO hypothesis here.

## PQ-only corollaries

`hybrid_secure_under_msis_alone` shows the hybrid needs NO classical model at all when the lattice floor
holds: `hybrid_secure_if_either_floor` demanded `dlFork` even on the `MSISHard` branch, where it is never
used. So the deployed post-quantum statement carries with zero classical hypotheses.

`#assert_all_clean` (⊆ `{propext, Classical.choice, Quot.sound}`).
-/
import Dregg2.Crypto.ForkingDischarge
import Dregg2.Crypto.CapabilityChain
import Dregg2.Crypto.TurnSoundness
import Dregg2.Crypto.DowngradeResistance
import Dregg2.Crypto.RevocationSoundness
import Dregg2.Crypto.ConsensusSafety
import Dregg2.Crypto.BlocklaceSafety
import Dregg2.Crypto.WireAke
import Dregg2.Crypto.UcSignature
import Dregg2.Crypto.LightClientSoundness

namespace Dregg2.Crypto.ForkingDischargeConsumers

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.HermineTSUF
open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.SchnorrEufCma
open Dregg2.Crypto.ForkingDischarge

/-! ## §0 — The two shared parameters: the lattice instance and the scalar group. -/

section Consumers

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq] [Fintype Rq] [DecidableEq Rq]
variable {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
variable {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
variable {F : Type*} [Field F] [ShortNorm F] [Fintype F] [DecidableEq F]
variable {Gp : Type*} [AddCommGroup Gp] [Module F Gp]
variable {Ωc : Type*} [Fintype Ωc] {Ωp : Type*} [Fintype Ωp]

/-! ## §1 — The PQ-ONLY keystone: the hybrid needs NO classical model under the lattice floor.

`HybridCombiner.hybrid_secure_if_either_floor` demanded `dlFork` unconditionally, even though on the
`MSISHard` branch it is never used. Once the pq leg is discharged, the deployed post-quantum statement
stands with ZERO classical hypotheses — no curve, no discrete log, no classical fork. -/

/-- **THE HYBRID, SECURE ON THE LATTICE FLOOR ALONE.** No curve group, no discrete-log assumption, no
classical forking reduction — just the Module-SIS floor and the pq realizability bridge. This is the
deployed post-quantum claim, standing on its own. -/
theorem hybrid_secure_under_msis_alone
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Q : Msg → Prop)
    (A : Mo →ₗ[Rq] No) (t : No) (β : ℕ) (Ωp : Type*) [Fintype Ωp]
    (hΩp : 0 < Fintype.card Ωp) (hC : 0 < Fintype.card Rq)
    (hrealPq : ForgeryRealizable Pq pkp Q A t β Ωp)
    (hmsis : MSISHard (augmented A t) ((β + β) + (β + β))) :
    EufCma (hybrid Cl Pq) (pkc, pkp) Q :=
  hybrid_euf_cma_if_either Cl Pq pkc pkp Q
    (Or.inr (pq_euf_cma_grounded_in_msis_discharged Pq pkp Q A t β Ωp hΩp hC hrealPq hmsis))

/-- **THE HYBRID, SECURE ON THE DISCRETE-LOG FLOOR ALONE.** Symmetrically: no lattice instance, no MSIS,
no pq forking reduction — just the field-scalar discrete-log floor and the classical realizability
bridge. -/
theorem hybrid_secure_under_dl_alone
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Q : Msg → Prop) (g : Gp)
    (Ωc : Type*) [Fintype Ωc]
    (hΩc : 0 < Fintype.card Ωc) (hF : 0 < Fintype.card F)
    (hrealCl : ClassicalForgeryRealizable (F := F) Cl pkc Q g Ωc)
    (hdl : SchnorrDLHardF (S := F) g) :
    EufCma (hybrid Cl Pq) (pkc, pkp) Q :=
  hybrid_euf_cma_if_either Cl Pq pkc pkp Q
    (Or.inl (classical_euf_cma_grounded_in_dl_discharged hΩc hF hrealCl hdl))

/-! ## §2 — `CapabilityChain` — biscuit/credential attenuation soundness. -/

/-- **`chain_unforgeable_under_hybrid_floor`, DISCHARGED.** The per-honest-key `dlFork` / `msisFork`
hypotheses are GONE; the per-key realizability bridges take their place, and the forking is proved. An
accepting chain rooted at an honest key is entirely honestly signed, under
`SchnorrDLHardF ∨ MSISHard`. -/
theorem chain_unforgeable_under_hybrid_floor_discharged
    {Auth : Type*} [LE Auth] {Msg : Type*}
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (g : Gp) (A : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (honestPk : (PKc × PKp) → Prop) (Q : (PKc × PKp) → Msg → Prop)
    (body : Option (Sigc × Sigp) →
      CapabilityChain.Block Auth (PKc × PKp) (Sigc × Sigp) → Msg)
    (rootPk : PKc × PKp)
    (blocks : List (CapabilityChain.Block Auth (PKc × PKp) (Sigc × Sigp)))
    (hrealCl : ∀ pk, honestPk pk → ClassicalForgeryRealizable (F := F) Cl pk.1 (Q pk) g Ωc)
    (hrealPq : ∀ pk, honestPk pk → ForgeryRealizable Pq pk.2 (Q pk) A t β Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented A t) ((β + β) + (β + β)))
    (hdel : ∀ (pk : PKc × PKp) (ps : Option (Sigc × Sigp))
        (b : CapabilityChain.Block Auth (PKc × PKp) (Sigc × Sigp)),
      honestPk pk → Q pk (body ps b) → honestPk b.nextPk)
    (rootHonest : honestPk rootPk)
    (hverify : CapabilityChain.VerifyChain (hybrid Cl Pq) body rootPk blocks) :
    CapabilityChain.ChainSigned Q body rootPk blocks := by
  refine CapabilityChain.chain_unforgeable_under_eufcma (hybrid Cl Pq) body honestPk Q hdel ?_
    rootPk blocks rootHonest hverify
  rintro ⟨a, b⟩ hpk
  exact hybrid_secure_if_either_floor_discharged Cl Pq a b (Q (a, b)) g A t β Ωc Ωp
    hΩc hΩp hF hC (hrealCl (a, b) hpk) (hrealPq (a, b) hpk) hfloor

/-! ## §3 — `TurnSoundness` — a verified turn was authorized AND correctly evolved state. -/

/-- **`turn_sound_under_floor`, DISCHARGED.** No `dlFork`, no `msisFork`. -/
theorem turn_sound_under_floor_discharged
    {State Effect SK PK Msg Sig Proof : Type*}
    (Cl : SigScheme SK PK Msg Sig) (Pq : SigScheme SK PK Msg Sig)
    (pkc pkp : PK) (encMsg : State → Effect → Msg)
    (applyEff : Effect → State → State)
    (checks : Proof → State → Effect → State → Prop)
    (Q : Msg → Prop) (g : Gp) (A : Mo →ₗ[Rq] No) (tgt : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (hrealCl : ClassicalForgeryRealizable (F := F) Cl pkc Q g Ωc)
    (hrealPq : ForgeryRealizable Pq pkp Q A tgt β Ωp)
    (hcs : TurnSoundness.CircuitSound applyEff checks)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented A tgt) ((β + β) + (β + β)))
    (tn : TurnSoundness.Turn State Effect) (r : TurnSoundness.Receipt (Sig × Sig) Proof)
    (hvalid : TurnSoundness.Valid (hybrid Cl Pq) encMsg checks (pkc, pkp) tn r) :
    Q (encMsg tn.old tn.eff) ∧ TurnSoundness.CorrectTransition applyEff tn :=
  TurnSoundness.turn_sound (hybrid Cl Pq) encMsg applyEff checks (pkc, pkp) Q
    (hybrid_secure_if_either_floor_discharged Cl Pq pkc pkp Q g A tgt β Ωc Ωp
      hΩc hΩp hF hC hrealCl hrealPq hfloor)
    hcs tn r hvalid

/-! ## §4 — `DowngradeResistance` — you cannot strip the post-quantum half. -/

/-- **`downgrade_resistant_under_floor`, DISCHARGED.** No `dlFork`, no `msisFork`. -/
theorem downgrade_resistant_under_floor_discharged
    {Suite : Type*} [PartialOrder Suite] {Msg : Type*}
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (aPk : PKc × PKp) (pkc : PKc) (pkp : PKp)
    (g : Gp) (A : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (bodyEnc : Finset Suite → Finset Suite → Suite → Msg)
    (Qb : Msg → Prop) (aTrue bTrue : Finset Suite) (best : Suite)
    (hrealCl : ClassicalForgeryRealizable (F := F) Cl pkc Qb g Ωc)
    (hrealPq : ForgeryRealizable Pq pkp Qb A t β Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented A t) ((β + β) + (β + β)))
    (honestB : DowngradeResistance.HonestSigner bodyEnc Qb bTrue)
    (hbest : DowngradeResistance.IsStrongestCommon aTrue bTrue best)
    (tr : DowngradeResistance.SignedTranscript Suite (Sigc × Sigp))
    (hlt : tr.neg < best)
    (hAccept : DowngradeResistance.AAccepts (hybrid Cl Pq) bodyEnc (pkc, pkp) aTrue tr ∧
      DowngradeResistance.BAccepts (hybrid Cl Pq) bodyEnc aPk bTrue tr) :
    False :=
  DowngradeResistance.downgrade_resistant (hybrid Cl Pq) bodyEnc aPk (pkc, pkp) Qb aTrue bTrue best
    honestB hbest
    (hybrid_secure_if_either_floor_discharged Cl Pq pkc pkp Qb g A t β Ωc Ωp
      hΩc hΩp hF hC hrealCl hrealPq hfloor)
    tr hlt hAccept

/-! ## §5 — `RevocationSoundness` — a revoked token cannot pass as un-revoked. -/

/-- **`revocation_sound_under_floor`, DISCHARGED (forking legs).** No `dlFork`, no `msisFork`. ⚑ NB
(2026-07-24): the underlying `RevocationSoundness.revocation_sound`/`revocation_sound_under_floor`
are DELETED (their `HashCR` hypothesis is refuted at every compressing root hash —
`hashCR_false_of_compressing`); this composition now routes through the KEPT dichotomy
`forged_non_revocation_breaks_cr_or_forges` and still carries `hcr : HashCR` — a refuted-floor
hypothesis this forking-lane composition inherits. Its hash horn's honest discharge is
`RevocationSoundness.revocationRoot_binds_rom` (keyed-ROM floor, PROVED); the deterministic composite
here survives only as the forking-discharge exemplar, vacuous at deployed hash parameters. -/
theorem revocation_sound_under_floor_discharged
    {Id Digest Epoch Msg : Type*}
    {SKc PKc Sigc SKp PKp Sigp : Type*} [DecidableEq Id]
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp)
    (g : Gp) (A : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (tree : HermineHintMLWE.CommitReveal Unit (Finset Id) Digest)
    (bodyEnc : Digest → Epoch → Msg)
    (Q : Msg → Prop) (trueRevoked : Epoch → Finset Id)
    (hrealCl : ClassicalForgeryRealizable (F := F) Cl pkc Q g Ωc)
    (hrealPq : ForgeryRealizable Pq pkp Q A t β Ωp)
    (hcr : HermineHintMLWE.HashCR tree)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented A t) ((β + β) + (β + β)))
    (honest : RevocationSoundness.HonestAttestation tree bodyEnc Q trueRevoked)
    (att : RevocationSoundness.AttestedRoot Digest Epoch (Sigc × Sigp))
    (witnessSet : Finset Id) (id : Id)
    (hverify : RevocationSoundness.verifyAttested (hybrid Cl Pq) bodyEnc (pkc, pkp) att)
    (hrevoked : id ∈ trueRevoked att.epoch)
    (hopen : tree.H () witnessSet = att.root)
    (habsent : id ∉ witnessSet) :
    False :=
  (RevocationSoundness.forged_non_revocation_breaks_cr_or_forges (hybrid Cl Pq) tree bodyEnc
      (pkc, pkp) Q trueRevoked honest att witnessSet id hverify hrevoked hopen habsent).elim
    (fun hbreak => hbreak hcr)
    (hybrid_secure_if_either_floor_discharged Cl Pq pkc pkp Q g A t β Ωc Ωp
      hΩc hΩp hF hC hrealCl hrealPq hfloor)

/-! ## §6 — `ConsensusSafety` — QUANTUM-SAFE FINALITY. -/

/-- **`consensus_safe_under_floor`, DISCHARGED.** The per-member forking reductions are GONE. Two
conflicting blocks cannot both be finalized, under `n > 3f` and `SchnorrDLHardF ∨ MSISHard`. -/
theorem consensus_safe_under_floor_discharged
    {Member : Type*} [DecidableEq Member] {Height Block Msg : Type*}
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (committee byz : Finset Member) (pkc : Member → PKc) (pkp : Member → PKp)
    (voteMsg : Height → Block → Msg) (Q : Member → Msg → Prop)
    (n f : ℕ) (hn : 3 * f + 1 ≤ n) (hcard : committee.card = n)
    (hbyz : byz ⊆ committee) (hbyzc : byz.card ≤ f)
    (g : Gp) (Amap : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (hrealCl : ∀ m : Member, ClassicalForgeryRealizable (F := F) Cl (pkc m) (Q m) g Ωc)
    (hrealPq : ∀ m : Member, ForgeryRealizable Pq (pkp m) (Q m) Amap t β Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented Amap t) ((β + β) + (β + β)))
    (hrule : ConsensusSafety.HonestVotingRule voteMsg Q (fun m => m ∈ committee ∧ m ∉ byz))
    (height : Height) (b b' : Block) (hconf : b ≠ b')
    (F1 : ConsensusSafety.Finalized (hybrid Cl Pq) committee
      (fun m => (pkc m, pkp m)) voteMsg (n - f) height b)
    (F2 : ConsensusSafety.Finalized (hybrid Cl Pq) committee
      (fun m => (pkc m, pkp m)) voteMsg (n - f) height b') :
    False :=
  ConsensusSafety.no_two_conflicting_finalized (hybrid Cl Pq) committee byz
    (fun m => (pkc m, pkp m)) voteMsg Q n f hn hcard hbyz hbyzc
    (fun m _ _ =>
      hybrid_secure_if_either_floor_discharged Cl Pq (pkc m) (pkp m) (Q m) g Amap t β Ωc Ωp
        hΩc hΩp hF hC (hrealCl m) (hrealPq m) hfloor)
    hrule height b b' hconf F1 F2

/-! ## §7 — `BlocklaceSafety` — no forged block. -/

/-- **`no_forged_block_under_floor`, DISCHARGED.** No `dlFork`, no `msisFork`. -/
theorem no_forged_block_under_floor_discharged
    {Creator BId Msg : Type*}
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkOf : Creator → PKc × PKp)
    (body : BlocklaceSafety.Blk Creator BId → Msg) (Q : Msg → Prop)
    (g : Gp) (Amap : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (b : BlocklaceSafety.Blk Creator BId) (σ : Sigc × Sigp)
    (hrealCl : ClassicalForgeryRealizable (F := F) Cl (pkOf b.creator).1 Q g Ωc)
    (hrealPq : ForgeryRealizable Pq (pkOf b.creator).2 Q Amap t β Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented Amap t) ((β + β) + (β + β)))
    (accepted : (hybrid Cl Pq).verify (pkOf b.creator) (body b) σ) (never : ¬ Q (body b)) :
    False := by
  have heuf : EufCma (hybrid Cl Pq) ((pkOf b.creator).1, (pkOf b.creator).2) Q :=
    hybrid_secure_if_either_floor_discharged Cl Pq (pkOf b.creator).1 (pkOf b.creator).2 Q
      g Amap t β Ωc Ωp hΩc hΩp hF hC hrealCl hrealPq hfloor
  exact heuf ⟨body b, σ, never, accepted⟩

/-! ## §8 — `WireAke` — the authenticated key exchange. -/

/-- **`ake_authentication_grounded`, DISCHARGED (forking legs).** No `dlFork`, no `msisFork`. ⚑ NB
(2026-07-24): the underlying `WireAke.ake_authentication`/`ake_authentication_grounded` are DELETED
(their `HashCR` hypothesis is refuted — `hashCR_false_of_compressing`); this composition now routes
through the KEPT dichotomy `accept_without_match_breaks_auth` and still carries `hcr : HashCR` — a
refuted-floor hypothesis this forking-lane composition inherits. The id horn's honest discharge is
`IdentityCommitmentRegrounded`'s keyed-ROM binding; the deterministic composite here survives only as
the forking-discharge exemplar, vacuous at deployed hash parameters. -/
theorem ake_authentication_grounded_discharged
    {SKc PKc Msg Sigc SKp PKp Sigp Pre Id : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (cr : HermineHintMLWE.CommitReveal Unit Pre Id) (frame : PKc → PKp → Pre)
    (hframe : Function.Injective2 frame) (hcr : HermineHintMLWE.HashCR cr)
    (id : Id) (edP : PKc) (mlP : PKp) (Q : Msg → Prop)
    (hcommitP : IdentityCommitment.verify_committed cr frame id edP mlP)
    (g : Gp) (A : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (hrealCl : ClassicalForgeryRealizable (F := F) Cl edP Q g Ωc)
    (hrealPq : ForgeryRealizable Pq mlP Q A t β Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented A t) ((β + β) + (β + β)))
    (ed' : PKc) (ml' : PKp) (c : Msg) (σ : Sigc × Sigp)
    (hacc : WireAke.SessionAccepts Cl Pq cr frame id ed' ml' c σ) :
    WireAke.MatchingSession Q c :=
  by
  by_contra hnomatch
  rcases WireAke.accept_without_match_breaks_auth Cl Pq cr frame hframe id edP mlP Q hcommitP
    ed' ml' c σ hacc hnomatch with hforge | hnhcr
  · exact hybrid_secure_if_either_floor_discharged Cl Pq edP mlP Q g A t β Ωc Ωp
      hΩc hΩp hF hC hrealCl hrealPq hfloor hforge
  · exact hnhcr hcr

/-! ## §9 — `UcSignature` — the UC realization (single- and multi-session). -/

/-- **`hybrid_sig_uc_realizes`, DISCHARGED.** No `dlFork`, no `msisFork`. -/
theorem hybrid_sig_uc_realizes_discharged
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Recorded : Msg → Prop)
    (g : Gp) (A : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (hrealCl : ClassicalForgeryRealizable (F := F) Cl pkc Recorded g Ωc)
    (hrealPq : ForgeryRealizable Pq pkp Recorded A t β Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented A t) ((β + β) + (β + β))) :
    UcSignature.UcRealizes (hybrid Cl Pq) (pkc, pkp) Recorded :=
  (UcSignature.ucRealizes_iff_eufCma _ _ _).2
    (hybrid_secure_if_either_floor_discharged Cl Pq pkc pkp Recorded g A t β Ωc Ωp
      hΩc hΩp hF hC hrealCl hrealPq hfloor)

/-- **`hybrid_multi_session_uc_realizes`, DISCHARGED.** The per-session forking reductions are GONE. -/
theorem hybrid_multi_session_uc_realizes_discharged
    {SID SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : SID → PKc) (pkp : SID → PKp) (Recorded : SID → Msg → Prop)
    (g : Gp) (A : Mo →ₗ[Rq] No) (t : No) (nb : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (hrealCl : ∀ i, ClassicalForgeryRealizable (F := F) Cl (pkc i) (Recorded i) g Ωc)
    (hrealPq : ∀ i, ForgeryRealizable Pq (pkp i) (Recorded i) A t nb Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented A t) ((nb + nb) + (nb + nb))) :
    UcSignature.MultiUcRealizes (hybrid Cl Pq) (fun i => (pkc i, pkp i)) Recorded :=
  UcSignature.multi_session_realization (hybrid Cl Pq) (fun i => (pkc i, pkp i)) Recorded
    (fun i => hybrid_secure_if_either_floor_discharged Cl Pq (pkc i) (pkp i) (Recorded i)
      g A t nb Ωc Ωp hΩc hΩp hF hC (hrealCl i) (hrealPq i) hfloor)

/-! ## §10 — `LightClientSoundness` — a ledgerless client cannot accept a forged history. -/

/-- **`accepting_forged_history_breaks_floor`, DISCHARGED.** No per-member `dlFork` / `msisFork`. -/
theorem accepting_forged_history_breaks_floor_discharged
    {Member : Type*} [DecidableEq Member] {Msg Block Pre IdT : Type*}
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (R : @LightClientSoundness.Roster PKc PKp Member Pre IdT)
    (voteMsg : ℕ → Block → Msg) (q start : ℕ) (Q : Member → Msg → Prop)
    (g : Gp) (Amap : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (hrealCl : ∀ m : Member, ClassicalForgeryRealizable (F := F) Cl (R.edPk m) (Q m) g Ωc)
    (hrealPq : ∀ m : Member, ForgeryRealizable Pq (R.mlPk m) (Q m) Amap t β Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented Amap t) ((β + β) + (β + β)))
    (H : LightClientSoundness.AcceptedHistory Cl Pq R voteMsg q start)
    (c : LightClientSoundness.Cert Cl Pq R voteMsg q) (hc : c ∈ H.certs)
    (m : Member) (hm : m ∈ c.fin.quorum)
    (hnever : ¬ Q m (voteMsg c.height c.block)) :
    False := by
  obtain ⟨σ, hv⟩ := c.fin.votes m hm
  have heuf : EufCma (hybrid Cl Pq) (R.edPk m, R.mlPk m) (Q m) :=
    hybrid_secure_if_either_floor_discharged Cl Pq (R.edPk m) (R.mlPk m) (Q m)
      g Amap t β Ωc Ωp hΩc hΩp hF hC (hrealCl m) (hrealPq m) hfloor
  simp only [LightClientSoundness.memberPk] at hv
  exact heuf ⟨voteMsg c.height c.block, σ, hnever, hv⟩

/-- **`lightclient_no_fork_under_floor`, DISCHARGED** (the long-range / equivocation leg): two certificates
at the same height cannot carry different blocks. Routes through the DISCHARGED consensus-safety keystone,
so no forking hypothesis survives. -/
theorem lightclient_no_fork_under_floor_discharged
    {Member : Type*} [DecidableEq Member] {Msg Block Pre IdT : Type*}
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (R : @LightClientSoundness.Roster PKc PKp Member Pre IdT)
    (voteMsg : ℕ → Block → Msg) (start : ℕ) (Q : Member → Msg → Prop)
    (byz : Finset Member) (n f : ℕ)
    (hn : 3 * f + 1 ≤ n) (hcard : R.committee.card = n)
    (hbyz : byz ⊆ R.committee) (hbyzc : byz.card ≤ f)
    (g : Gp) (Amap : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (hrealCl : ∀ m : Member, ClassicalForgeryRealizable (F := F) Cl (R.edPk m) (Q m) g Ωc)
    (hrealPq : ∀ m : Member, ForgeryRealizable Pq (R.mlPk m) (Q m) Amap t β Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented Amap t) ((β + β) + (β + β)))
    (hrule : ConsensusSafety.HonestVotingRule voteMsg Q (fun m => m ∈ R.committee ∧ m ∉ byz))
    (H : LightClientSoundness.AcceptedHistory Cl Pq R voteMsg (n - f) start)
    (c c' : LightClientSoundness.Cert Cl Pq R voteMsg (n - f))
    (hc : c ∈ H.certs) (hc' : c' ∈ H.certs)
    (hh : c.height = c'.height) (hbne : c.block ≠ c'.block) :
    False :=
  consensus_safe_under_floor_discharged Cl Pq R.committee byz R.edPk R.mlPk voteMsg Q n f hn hcard
    hbyz hbyzc g Amap t β hΩc hΩp hF hC hrealCl hrealPq hfloor hrule
    c.height c.block c'.block hbne c.fin (by rw [hh]; exact c'.fin)

end Consumers

/-! ## Kernel-clean keystones.

TWELVE protocol consumers, each with BOTH forking hypotheses retired. What remains in every one: the two
named floors, the two realizability MODELLING bridges, and the game's own protocol hypotheses. -/

#assert_all_clean [
  hybrid_secure_under_msis_alone,
  hybrid_secure_under_dl_alone,
  chain_unforgeable_under_hybrid_floor_discharged,
  turn_sound_under_floor_discharged,
  downgrade_resistant_under_floor_discharged,
  revocation_sound_under_floor_discharged,
  consensus_safe_under_floor_discharged,
  no_forged_block_under_floor_discharged,
  ake_authentication_grounded_discharged,
  hybrid_sig_uc_realizes_discharged,
  hybrid_multi_session_uc_realizes_discharged,
  accepting_forged_history_breaks_floor_discharged,
  lightclient_no_fork_under_floor_discharged
]

end Dregg2.Crypto.ForkingDischargeConsumers
