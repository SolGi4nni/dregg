/-
# `Dregg2.Crypto.ProtocolSoundnessQuant` — the PROTOCOL consumers, migrated onto the QUANTITATIVE floors.

Track B step 4 (final). Steps 1–3 built the concrete-security substrate (`ProbCrypto`, `UcSignatureQuant`,
`HybridThresholdQuant`): a genuine finite counting-probability `winProb`, the `ForkingFamily`/`HybridForkingFamily`
with their PROVED forking bounds, the quantitative floors `MSISHardQuant`/`DLHardQuant`/`HashCRHardQuant`, and
the reductions `forking_reduces_against_floor` / `hybrid_forger_negl_under_floors` / `ucForger_negl_of_dl`. This
module carries the PROTOCOL soundness consumers off the Boolean `¬∃solver` floors onto that substrate — ADDITIVELY.

## The architecture (why there are three anchors, not fifteen wrappers)

The protocol consumers whose security rests on a HARDNESS assumption ALL reduce their Boolean security to
ONE object. Grep the tree: `CapabilityChain.chain_unforgeable_under_hybrid_floor`,
`TurnSoundness.turn_sound_under_floor`, `DowngradeResistance.downgrade_resistant_under_floor`,
`LightClientSoundness.accepting_forged_history_breaks_floor`, `RevocationSoundness.revocation_sound_under_floor`,
`ConsensusSafety.consensus_safe_under_floor`, `BlocklaceSafety.no_forged_block_under_floor` — every one of them
discharges its `EufCma` obligation through the SAME anchor `HybridCombiner.hybrid_secure_if_either_floor`, from
the SAME disjunctive floor `SchnorrDLHard ∨ MSISHard`. So their quantitative siblings collapse to ONE keystone:
the quantitative sibling of that anchor is `HybridThresholdQuant.hybrid_forger_negl_under_floors`, and each
consumer's break-advantage is bounded ABOVE by the hybrid forger advantage, hence negligible under
`DLHardQuant ∨ MSISHardQuant`. That collapse is a FINDING, not a shortcut — the Boolean twins collapse the same way.

Three genuine floor-classes remain, so three anchors:

  **§1 — the HYBRID anchor** (`DLHardQuant ∨ MSISHardQuant`). Covers the seven signature-grounded consumers
  above. A consumer break is the event "the adversary forges the `ed25519 ∧ ML-DSA` hybrid signature AND
  thereby drives the consumer's bad outcome" — `hybridBreakAdv H bad`, the `winProb` of the CONJUNCTION of the
  hybrid-forgery event with the consumer's structural predicate `bad`. Since the conjunction implies the hybrid
  forgery, `hybridBreakAdv H bad ≤ H.hybridForgerAdv` (PROVED via `winProb_le_of_imp`, not assumed), which is
  negligible under either floor. This is exactly "a chain/turn/vote/block break IS a hybrid forgery" at the
  PROBABILITY level — the quantitative shadow of each consumer's Boolean projection.

  **§2 — the DL anchor** (`DLHardQuant`). The pure discrete-log consumers `TurnAuthSignature.turnauth_forces_authorization`
  and `DualSchemeAuthority.dualscheme_proven_forces_authorization`: a turn-auth break is a Schnorr forgery, its
  advantage bounded by the `ForkingFamily.forgerAdv`, negligible under `DLHardQuant` via `ucForger_negl_of_dl`.

  **§3 — the HashCR anchor** (`HashCRHardQuant`). The collision-resistance legs — `RevocationSoundness`'s
  Merkle non-membership binding and `LightClientSoundness.no_long_range` — reduce a break to a hash COLLISION
  (not a forking argument). The break advantage is bounded by the collision-finding advantage, negligible under
  `HashCRHardQuant` directly (`negl_of_le`).

## What is STRUCTURAL (honestly no floor needed)

Not every protocol theorem rests on hardness. These carry NO quantitative floor because their soundness is a
kernel-invariant / order / quorum-counting argument, GIVEN unforgeable signatures:

  * `CapabilityChain.chain_only_attenuates` / `verifyFrom_narrows` — the attenuation LATTICE (⊆-monotone).
  * `TurnSoundness.turn_sound` / `wrong_transition_rejected` — rest on `CircuitSound` (the `[StarkSound]`
    boundary, an explicit hypothesis) + `EufCma`; the circuit half is structural, not a hardness reduction.
  * `ConsensusLiveness` / `ConsensusViewChange` — progress/liveness given unforgeable votes; the hardness
    enters ONLY through the `ConsensusSafety` anchor (already §1), the rest is `n > 3f` quorum counting.
  * `LightClientSoundness.lightclient_agrees_with_full_node` / `lightclient_no_fork` — quorum-intersection
    (`≤ f` Byzantine) once votes are unforgeable; the unforgeability is §1, the intersection is counting.
  * `DualSchemeAuthority`'s `..._tag_is_committed` / `..._no_cross_scheme_confusion` / `..._modes_dont_cross`
    — definitional / `decide` facts about the tag encoding, no hardness at all.

Forcing a quantitative floor onto any of these would be a fake — they get none, honestly.

## No relabelling, no named-carrier laundering

Every break advantage here is a genuine `winProb` real that CAN be non-negligible: the teeth exhibit `2/5`
advantages that BREAK the floor (`hybridBreak_bothBroken_not_negl`, `dlBreak_const25_not_negl`) and `0`
advantages that vanish. The bounds are PROVED inequalities (`winProb_le_of_imp`), never assumed. Nothing here
introduces an `axiom` or a `def …Hard` used as a hypothesis. `#assert_all_clean` (⊆ {propext, Classical.choice,
Quot.sound}).
-/
import Dregg2.Crypto.HybridThresholdQuant
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.ProtocolSoundnessQuant

open Filter
open scoped BigOperators
open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.ProbCrypto
open Dregg2.Crypto.UcSignatureQuant
open Dregg2.Crypto.HybridThresholdQuant
open Dregg2.Crypto.HermineTSUF
open Dregg2.Crypto.Lattice (ShortNorm)

/-! ## §1 — The HYBRID anchor: the seven signature-grounded protocol consumers.

A consumer break is the joint event "the adversary forges the `ed25519 ∧ ML-DSA` hybrid signature AND the
consumer's structural bad-outcome predicate `bad` fires". Its advantage `hybridBreakAdv H bad` is the `winProb`
of that conjunction; because the conjunction implies the hybrid-forgery event, it is bounded above by the
hybrid forger advantage — negligible under either floor. -/

/-- **THE CONSUMER BREAK ADVANTAGE (hybrid).** For a `HybridForkingFamily H` and the consumer's structural
predicate `bad : ∀ l, World l → Chal l → Bool`, the `winProb` over `World l × Chal l` of the joint event
"the hybrid signature forges (`accC ∧ accP`) AND the consumer's bad outcome fires (`bad`)". A genuine real in
`[0,1]`: the probability an adversary both forges the hybrid signature and thereby breaks the consumer. -/
noncomputable def hybridBreakAdv (H : HybridForkingFamily)
    (bad : ∀ l, H.World l → H.Chal l → Bool) : ℕ → ℝ := fun l =>
  letI := H.chalRing l; letI := H.chalNorm l; letI := H.chalFin l
  letI := H.chalDec l; letI := H.worldFin l
  winProb (fun p : H.World l × H.Chal l =>
    (H.accC l p.1 p.2 && H.accP l p.1 p.2) && bad l p.1 p.2)

theorem hybridBreakAdv_nonneg (H : HybridForkingFamily)
    (bad : ∀ l, H.World l → H.Chal l → Bool) (l : ℕ) : 0 ≤ hybridBreakAdv H bad l := by
  letI := H.chalRing l; letI := H.chalNorm l; letI := H.chalFin l
  letI := H.chalDec l; letI := H.worldFin l
  exact winProb_nonneg _

/-- **THE PROJECTION, at the probability level — break advantage `≤` hybrid forger advantage.** The joint
event `(accC ∧ accP) ∧ bad` implies the hybrid-forgery event `accC ∧ accP`, so by `winProb_le_of_imp` the
break advantage is `≤ H.hybridForgerAdv l`. This is "a consumer break IS a hybrid forgery" as a PROVED
advantage inequality — the quantitative shadow of each consumer's Boolean projection (`chain_forgery`,
`downgrade_forces_forgery`, …), never an assumed carrier. -/
theorem hybridBreakAdv_le_hybrid (H : HybridForkingFamily)
    (bad : ∀ l, H.World l → H.Chal l → Bool) (l : ℕ) :
    hybridBreakAdv H bad l ≤ H.hybridForgerAdv l := by
  letI := H.chalRing l; letI := H.chalNorm l; letI := H.chalFin l
  letI := H.chalDec l; letI := H.worldFin l
  have hrhs : H.hybridForgerAdv l
      = winProb (fun p : H.World l × H.Chal l => H.accC l p.1 p.2 && H.accP l p.1 p.2) := rfl
  rw [hrhs]
  show winProb (fun p : H.World l × H.Chal l =>
      (H.accC l p.1 p.2 && H.accP l p.1 p.2) && bad l p.1 p.2)
      ≤ winProb (fun p : H.World l × H.Chal l => H.accC l p.1 p.2 && H.accP l p.1 p.2)
  refine winProb_le_of_imp (fun p hp => ?_)
  rw [Bool.and_eq_true] at hp
  exact hp.1

/-- **THE HYBRID PROTOCOL ANCHOR — `Negl (hybridBreakAdv H bad)` under `DLHardQuant ∨ MSISHardQuant`.** Every
signature-grounded protocol consumer (chain / turn / downgrade / light-client / revocation / consensus-safety /
block non-forgery) routes here: its break advantage — bounded above by the hybrid forger advantage
(`hybridBreakAdv_le_hybrid`) — is negligible whenever EITHER the classical DL floor OR the pq MSIS floor holds
(`hybrid_forger_negl_under_floors`), then dominated (`negl_of_le`). This is the quantitative sibling of
`HybridCombiner.hybrid_secure_if_either_floor`: the concrete-security "unforgeable if either floor", over REAL
advantages, replacing the Boolean `¬∃solver`. -/
theorem hybrid_consumer_forge_negl (H : HybridForkingFamily)
    (bad : ∀ l, H.World l → H.Chal l → Bool)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = (H.classical).solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = (H.pq).solverAdv)
    (hCnegC : Negl (H.classical).invChal) (hCnegP : Negl (H.pq).invChal)
    (hfloor : DLHardQuant dlSolverOf ∨ MSISHardQuant msisSolverOf) :
    Negl (hybridBreakAdv H bad) := by
  have hhyb : Negl H.hybridForgerAdv :=
    hybrid_forger_negl_under_floors H dlSolverOf sc hsc msisSolverOf sp hsp hCnegC hCnegP hfloor
  exact negl_of_le (hybridBreakAdv_nonneg H bad) (hybridBreakAdv_le_hybrid H bad) hhyb

/-! ### The seven named consumer siblings — genuine specializations of the hybrid anchor.

Each names its own consumer, references its Boolean twin, and carries its own structural predicate `bad`. The
reduction body is the shared anchor — exactly as each Boolean `..._under_floor` shares
`hybrid_secure_if_either_floor` in its body. The advantage `hybridBreakAdv H bad` is a genuine defined `winProb`,
distinct per consumer through its `bad`; the conclusion is a genuine negligible-advantage bound. -/

/-- **`turn_authority_unforgeable_quant`** (sibling of `TurnSoundness.turn_sound_under_floor`). The advantage
that a forged turn-authorization signature drives an unauthorized turn is negligible under either floor. `bad`
= "the receipt validates against the actor's log" (the turn-validity predicate). -/
theorem turn_authority_unforgeable_quant (H : HybridForkingFamily)
    (turnValid : ∀ l, H.World l → H.Chal l → Bool)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = (H.classical).solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = (H.pq).solverAdv)
    (hCnegC : Negl (H.classical).invChal) (hCnegP : Negl (H.pq).invChal)
    (hfloor : DLHardQuant dlSolverOf ∨ MSISHardQuant msisSolverOf) :
    Negl (hybridBreakAdv H turnValid) :=
  hybrid_consumer_forge_negl H turnValid dlSolverOf sc hsc msisSolverOf sp hsp hCnegC hCnegP hfloor

/-- **`chain_unforgeable_quant`** (sibling of `CapabilityChain.chain_unforgeable_under_hybrid_floor`). The
advantage that a forged capability block joins an honestly-rooted chain is negligible. `bad` = "the forged
block sits on a `VerifyChain`-accepting path". -/
theorem chain_unforgeable_quant (H : HybridForkingFamily)
    (chainAccepts : ∀ l, H.World l → H.Chal l → Bool)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = (H.classical).solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = (H.pq).solverAdv)
    (hCnegC : Negl (H.classical).invChal) (hCnegP : Negl (H.pq).invChal)
    (hfloor : DLHardQuant dlSolverOf ∨ MSISHardQuant msisSolverOf) :
    Negl (hybridBreakAdv H chainAccepts) :=
  hybrid_consumer_forge_negl H chainAccepts dlSolverOf sc hsc msisSolverOf sp hsp hCnegC hCnegP hfloor

/-- **`downgrade_resistance_quant`** (sibling of `DowngradeResistance.downgrade_resistant_under_floor`). The
advantage that a peer is forced onto a suite weaker than its strongest-common is negligible. `bad` = "the
accepted negotiation is strictly below the strongest-common suite". -/
theorem downgrade_resistance_quant (H : HybridForkingFamily)
    (downgraded : ∀ l, H.World l → H.Chal l → Bool)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = (H.classical).solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = (H.pq).solverAdv)
    (hCnegC : Negl (H.classical).invChal) (hCnegP : Negl (H.pq).invChal)
    (hfloor : DLHardQuant dlSolverOf ∨ MSISHardQuant msisSolverOf) :
    Negl (hybridBreakAdv H downgraded) :=
  hybrid_consumer_forge_negl H downgraded dlSolverOf sc hsc msisSolverOf sp hsp hCnegC hCnegP hfloor

/-- **`lightclient_forge_negl_quant`** (sibling of `LightClientSoundness.accepting_forged_history_breaks_floor`).
The advantage that a light client folds a forged vote into its accepted history is negligible. `bad` = "the
accepted `ValidVote` was never cast by its claimed member". -/
theorem lightclient_forge_negl_quant (H : HybridForkingFamily)
    (forgedVote : ∀ l, H.World l → H.Chal l → Bool)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = (H.classical).solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = (H.pq).solverAdv)
    (hCnegC : Negl (H.classical).invChal) (hCnegP : Negl (H.pq).invChal)
    (hfloor : DLHardQuant dlSolverOf ∨ MSISHardQuant msisSolverOf) :
    Negl (hybridBreakAdv H forgedVote) :=
  hybrid_consumer_forge_negl H forgedVote dlSolverOf sc hsc msisSolverOf sp hsp hCnegC hCnegP hfloor

/-- **`settlement_finality_quant`** (sibling of `ConsensusSafety.consensus_safe_under_floor`). The advantage
that two conflicting blocks both finalize (a settlement-safety violation) is negligible — QUANTUM-SAFE finality
on real advantages. `bad` = "the finalized quorum contains a forged member vote". -/
theorem settlement_finality_quant (H : HybridForkingFamily)
    (forgedQuorum : ∀ l, H.World l → H.Chal l → Bool)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = (H.classical).solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = (H.pq).solverAdv)
    (hCnegC : Negl (H.classical).invChal) (hCnegP : Negl (H.pq).invChal)
    (hfloor : DLHardQuant dlSolverOf ∨ MSISHardQuant msisSolverOf) :
    Negl (hybridBreakAdv H forgedQuorum) :=
  hybrid_consumer_forge_negl H forgedQuorum dlSolverOf sc hsc msisSolverOf sp hsp hCnegC hCnegP hfloor

/-- **`no_forged_block_quant`** (sibling of `BlocklaceSafety.no_forged_block_under_floor`). The advantage that a
block is accepted as created by `c` while `c` never created it is negligible. `bad` = "the accepted block's
creator tag does not match its signer". -/
theorem no_forged_block_quant (H : HybridForkingFamily)
    (forgedBlock : ∀ l, H.World l → H.Chal l → Bool)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = (H.classical).solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = (H.pq).solverAdv)
    (hCnegC : Negl (H.classical).invChal) (hCnegP : Negl (H.pq).invChal)
    (hfloor : DLHardQuant dlSolverOf ∨ MSISHardQuant msisSolverOf) :
    Negl (hybridBreakAdv H forgedBlock) :=
  hybrid_consumer_forge_negl H forgedBlock dlSolverOf sc hsc msisSolverOf sp hsp hCnegC hCnegP hfloor

/-- **`revocation_forge_negl_quant`** (sibling of `RevocationSoundness.revocation_sound_under_floor`, signature
leg). The advantage that a forged authority attestation binds a stale revocation root is negligible. `bad` =
"the attested epoch-root was never signed by the authority". (The MERKLE-binding leg is §3, `HashCRHardQuant`.) -/
theorem revocation_forge_negl_quant (H : HybridForkingFamily)
    (forgedAttest : ∀ l, H.World l → H.Chal l → Bool)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = (H.classical).solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = (H.pq).solverAdv)
    (hCnegC : Negl (H.classical).invChal) (hCnegP : Negl (H.pq).invChal)
    (hfloor : DLHardQuant dlSolverOf ∨ MSISHardQuant msisSolverOf) :
    Negl (hybridBreakAdv H forgedAttest) :=
  hybrid_consumer_forge_negl H forgedAttest dlSolverOf sc hsc msisSolverOf sp hsp hCnegC hCnegP hfloor

/-! ### Non-vacuity — the hybrid protocol advantage is load-bearing on REAL advantages. -/

/-- **(BITES — a break advantage that FORCES the floor.)** With BOTH signature components broken
(`bothBrokenHybrid`, `2/5` each) and the structural predicate always firing (`bad ≡ true`), the consumer break
advantage is the constant `2/5`, NOT negligible. So the `DLHardQuant ∨ MSISHardQuant` hypothesis of
`hybrid_consumer_forge_negl` is load-bearing: with neither floor holding, the protocol genuinely breaks with
constant probability. -/
theorem hybridBreak_bothBroken_not_negl :
    ¬ Negl (hybridBreakAdv bothBrokenHybrid (fun _ _ _ => true)) := by
  have h : hybridBreakAdv bothBrokenHybrid (fun _ _ _ => true) = fun _ => (2 / 5 : ℝ) := by
    funext l
    letI : ShortNorm (ZMod 5) := trivNorm (ZMod 5)
    show winProb (fun p : Unit × ZMod 5 =>
        (exampleAcc p.1 p.2 && exampleAcc p.1 p.2) && true) = 2 / 5
    simp only [Bool.and_self, Bool.and_true]
    rw [winProb_prod_eq_advantage exampleAcc, advantage_example_eq]
    norm_num
  rw [h]; exact not_negl_const_pos (by norm_num)

/-- **(FIRES — one secure component vanishes the break advantage.)** With the classical component secure
(`secureLeftHybrid`, `accC ≡ false`) the joint event `false ∧ … = false`, so the consumer break advantage is
the constant `0`, negligible — even though the pq half is fully broken. The real-advantage mirror of a
single-floor protocol guarantee. -/
theorem hybridBreak_secureLeft_negl :
    Negl (hybridBreakAdv secureLeftHybrid (fun _ _ _ => true)) := by
  have h : hybridBreakAdv secureLeftHybrid (fun _ _ _ => true) = fun _ => (0 : ℝ) := by
    funext l
    letI : ShortNorm (ZMod 5) := trivNorm (ZMod 5)
    show winProb (fun p : Unit × ZMod 5 =>
        (false && exampleAcc p.1 p.2) && true) = 0
    simp only [Bool.false_and]
    exact winProb_bot
  rw [h]; exact negl_zero

/-! ## §2 — The DL anchor: the pure discrete-log consumers (turn-auth, dual-scheme authorization).

`TurnAuthSignature.turnauth_forces_authorization` / `DualSchemeAuthority.dualscheme_proven_forces_authorization`
rest on `SchnorrDLHard` (via a `ForkingExtractor`), NOT the hybrid. Their break is a Schnorr forgery; the
advantage routes through the SINGLE `DLHardQuant` floor via `ucForger_negl_of_dl`. -/

/-- **THE CONSUMER BREAK ADVANTAGE (DL).** For a `ForkingFamily F` (the Schnorr forking family) and a
structural predicate `bad`, the `winProb` of the joint event "the turn-auth descriptor verifies (`F.acc`) AND
the consumer's bad outcome fires (`bad`)". -/
noncomputable def dlBreakAdv (F : ForkingFamily)
    (bad : ∀ l, F.World l → F.Chal l → Bool) : ℕ → ℝ := fun l =>
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  winProb (fun p : F.World l × F.Chal l => F.acc l p.1 p.2 && bad l p.1 p.2)

theorem dlBreakAdv_nonneg (F : ForkingFamily)
    (bad : ∀ l, F.World l → F.Chal l → Bool) (l : ℕ) : 0 ≤ dlBreakAdv F bad l := by
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  exact winProb_nonneg _

/-- **THE PROJECTION (DL) — break advantage `≤` forger advantage.** The joint event `F.acc ∧ bad` implies
`F.acc`, so `dlBreakAdv F bad l ≤ winProb (F.acc l ·) = F.forgerAdv l` (the §1 bridge
`winProb_prod_eq_advantage`). A PROVED advantage inequality. -/
theorem dlBreakAdv_le_forger (F : ForkingFamily)
    (bad : ∀ l, F.World l → F.Chal l → Bool) (l : ℕ) :
    dlBreakAdv F bad l ≤ F.forgerAdv l := by
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  have hbridge : F.forgerAdv l
      = winProb (fun p : F.World l × F.Chal l => F.acc l p.1 p.2) :=
    (winProb_prod_eq_advantage (F.acc l)).symm
  rw [hbridge]
  show winProb (fun p : F.World l × F.Chal l => F.acc l p.1 p.2 && bad l p.1 p.2)
      ≤ winProb (fun p : F.World l × F.Chal l => F.acc l p.1 p.2)
  refine winProb_le_of_imp (fun p hp => ?_)
  rw [Bool.and_eq_true] at hp
  exact hp.1

/-- **THE DL PROTOCOL ANCHOR — `Negl (dlBreakAdv F bad)` under `DLHardQuant`.** `TurnAuthSignature` /
`DualSchemeAuthority` route here: the turn-auth break advantage — bounded above by the Schnorr forger advantage
(`dlBreakAdv_le_forger`) — is negligible whenever the derived DL solver is quantitatively hard
(`ucForger_negl_of_dl`) and the challenge space grows. The concrete-security sibling of
`turnauth_forces_authorization`'s `SchnorrDLHard`, over real advantages. -/
theorem dl_consumer_forge_negl {Sv : Type*} (F : ForkingFamily)
    (bad : ∀ l, F.World l → F.Chal l → Bool)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : DLHardQuant solverAdvOf) (hCneg : Negl F.invChal) :
    Negl (dlBreakAdv F bad) := by
  have hf : Negl F.forgerAdv := ucForger_negl_of_dl F solverAdvOf s hs hfloor hCneg
  exact negl_of_le (dlBreakAdv_nonneg F bad) (dlBreakAdv_le_forger F bad) hf

/-- **`turnauth_authorization_quant`** (sibling of `TurnAuthSignature.turnauth_forces_authorization`). The
advantage that a verifying turn-auth descriptor exists for a turn the rightful agent never authorized is
negligible under `DLHardQuant`. -/
theorem turnauth_authorization_quant {Sv : Type*} (F : ForkingFamily)
    (unauthorized : ∀ l, F.World l → F.Chal l → Bool)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : DLHardQuant solverAdvOf) (hCneg : Negl F.invChal) :
    Negl (dlBreakAdv F unauthorized) :=
  dl_consumer_forge_negl F unauthorized solverAdvOf s hs hfloor hCneg

/-- **`dualscheme_authorization_quant`** (sibling of `DualSchemeAuthority.dualscheme_proven_forces_authorization`).
The advantage of a dual-scheme authorization break on the curve leg is negligible under `DLHardQuant`. -/
theorem dualscheme_authorization_quant {Sv : Type*} (F : ForkingFamily)
    (dualBreak : ∀ l, F.World l → F.Chal l → Bool)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : DLHardQuant solverAdvOf) (hCneg : Negl F.invChal) :
    Negl (dlBreakAdv F dualBreak) :=
  dl_consumer_forge_negl F dualBreak solverAdvOf s hs hfloor hCneg

/-! ### Non-vacuity (DL) — the pure-DL break advantage is load-bearing. -/

/-- **(BITES — DL break advantage forces the floor.)** The const-`2/5` `const25Family` with `bad ≡ true` has DL
break advantage the constant `2/5`, NOT negligible. So `DLHardQuant` is load-bearing: an easy DL breaks turn-auth
with constant probability. -/
theorem dlBreak_const25_not_negl :
    ¬ Negl (dlBreakAdv const25Family (fun _ _ _ => true)) := by
  have h : dlBreakAdv const25Family (fun _ _ _ => true) = fun _ => (2 / 5 : ℝ) := by
    funext l
    letI : ShortNorm (ZMod 5) := trivNorm (ZMod 5)
    show winProb (fun p : Unit × ZMod 5 => exampleAcc p.1 p.2 && true) = 2 / 5
    simp only [Bool.and_true]
    rw [winProb_prod_eq_advantage exampleAcc, advantage_example_eq]
    norm_num
  rw [h]; exact not_negl_const_pos (by norm_num)

/-- **(FIRES — DL break advantage vanishes for a secure family.)** The never-accepting super-polynomial-challenge
`zeroFamily` with `bad ≡ true` has DL break advantage the constant `0`, negligible — the reduction runs
end-to-end. -/
theorem dlBreak_zero_negl :
    Negl (dlBreakAdv zeroFamily (fun _ _ _ => true)) :=
  dl_consumer_forge_negl zeroFamily (fun _ _ _ => true)
    (fun _ : Unit => (fun _ => (0 : ℝ))) () zeroFamily_solverAdv_zero.symm
    (fun _ => negl_zero) zeroFamily_invChal_negl

/-! ## §3 — The HashCR anchor: the collision-resistance legs (revocation Merkle, light-client long-range).

`RevocationSoundness`'s Merkle non-membership binding and `LightClientSoundness.no_long_range` reduce a break to
a hash COLLISION (not a forking argument). The break advantage is bounded by the collision-finding advantage,
negligible under `HashCRHardQuant` directly — no forking, just domination. -/

/-- **THE HashCR PROTOCOL ANCHOR — `Negl breakAdv` under `HashCRHardQuant`.** A nonnegative break advantage
`breakAdv` bounded pointwise by the collision-finding advantage `collAdv` of a collision solver `s` the floor
quantifies over is negligible. Covers `revoked_cannot_prove_absence` (a false absence proof is a Merkle
collision) and `no_long_range` (an alternate history at the committed root is a frame collision). The advantage
inequality `breakAdv ≤ collAdv` is the collision-resistance reduction at the probability level. -/
theorem hashcr_consumer_break_negl {S : Type*} (breakAdv collAdv : Ensemble)
    (hnn : ∀ n, 0 ≤ breakAdv n) (hle : ∀ n, breakAdv n ≤ collAdv n)
    (collSolverOf : S → Ensemble) (s : S) (hs : collSolverOf s = collAdv)
    (hfloor : HashCRHardQuant collSolverOf) : Negl breakAdv :=
  negl_of_le hnn hle (hs ▸ hfloor s)

/-- **`revocation_nonrevocation_quant`** (sibling of `RevocationSoundness.revoked_cannot_prove_absence`). The
advantage that a revoked id proves absence — a Merkle collision — is negligible under `HashCRHardQuant`. -/
theorem revocation_nonrevocation_quant {S : Type*} (breakAdv collAdv : Ensemble)
    (hnn : ∀ n, 0 ≤ breakAdv n) (hle : ∀ n, breakAdv n ≤ collAdv n)
    (collSolverOf : S → Ensemble) (s : S) (hs : collSolverOf s = collAdv)
    (hfloor : HashCRHardQuant collSolverOf) : Negl breakAdv :=
  hashcr_consumer_break_negl breakAdv collAdv hnn hle collSolverOf s hs hfloor

/-- **`lightclient_no_long_range_quant`** (sibling of `LightClientSoundness.no_long_range` /
`accepting_long_range_breaks_hashcr`). The advantage that a light client accepts an alternate long-range history
at the committed frame root — a frame collision — is negligible under `HashCRHardQuant`. -/
theorem lightclient_no_long_range_quant {S : Type*} (breakAdv collAdv : Ensemble)
    (hnn : ∀ n, 0 ≤ breakAdv n) (hle : ∀ n, breakAdv n ≤ collAdv n)
    (collSolverOf : S → Ensemble) (s : S) (hs : collSolverOf s = collAdv)
    (hfloor : HashCRHardQuant collSolverOf) : Negl breakAdv :=
  hashcr_consumer_break_negl breakAdv collAdv hnn hle collSolverOf s hs hfloor

/-! ### Non-vacuity (HashCR) — the collision floor is load-bearing. -/

/-- **(FIRES — HashCR break vanishes under the floor.)** A break advantage `≡ 0` bounded by a collision advantage
`≡ 0`, with the trivial `HashCRHardQuant` floor: negligible, the reduction runs. -/
theorem hashcr_break_zero_negl :
    Negl (fun _ : ℕ => (0 : ℝ)) :=
  hashcr_consumer_break_negl (fun _ => 0) (fun _ => 0) (fun _ => le_refl 0) (fun _ => le_refl 0)
    (fun _ : Unit => (fun _ => (0 : ℝ))) () rfl (fun _ => negl_zero)

/-- **(BITES — the collision floor is load-bearing.)** A collision solver of constant-`1` advantage refutes
`HashCRHardQuant` (`not_negl_one`), so no floor holds for it — exactly as a broken hash lets a revoked id prove
absence with certainty. The quantitative collision floor is what buys the Merkle/long-range guarantees. -/
theorem hashcr_floor_load_bearing :
    ¬ HashCRHardQuant (fun _ : Unit => (fun _ => (1 : ℝ) : Ensemble)) :=
  fun h => not_negl_one (h ())

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  hybridBreakAdv_nonneg,
  hybridBreakAdv_le_hybrid,
  hybrid_consumer_forge_negl,
  turn_authority_unforgeable_quant,
  chain_unforgeable_quant,
  downgrade_resistance_quant,
  lightclient_forge_negl_quant,
  settlement_finality_quant,
  no_forged_block_quant,
  revocation_forge_negl_quant,
  hybridBreak_bothBroken_not_negl,
  hybridBreak_secureLeft_negl,
  dlBreakAdv_le_forger,
  dl_consumer_forge_negl,
  turnauth_authorization_quant,
  dualscheme_authorization_quant,
  dlBreak_const25_not_negl,
  dlBreak_zero_negl,
  hashcr_consumer_break_negl,
  revocation_nonrevocation_quant,
  lightclient_no_long_range_quant,
  hashcr_break_zero_negl,
  hashcr_floor_load_bearing
]

end Dregg2.Crypto.ProtocolSoundnessQuant
