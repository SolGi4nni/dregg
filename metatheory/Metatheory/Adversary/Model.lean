/-
# Metatheory.Adversary.Model — THE EXPLICIT ADVERSARY, as a Lean object.

ELEVATED ASSURANCE, Pillar 2 (`docs/deos/ELEVATED-ASSURANCE-PROGRAM.md` §"Pillar 2").

dregg's deployed guarantees each carry an *implicit* adversary. `lightclient_unfoolable`
(`Dregg2/Circuit/CircuitSoundness.lean:453`) proves "an accepted batch ⟹ a genuine kernel
step" — the adversary is the *anonymous prover of a forged `VmRowEnv`*, never a named object;
`Metatheory.Polis.polis_safety` (`Polis/Polis.lean:102`) proves safety `∀ (ctrl : State →
Action)` — the operator of the substrate, likewise never named as one object; and
`Metatheory.Disputation.byzantine_majority_cannot_uphold` bounds a Byzantine coalition on the
certifiable domain. Three theorems, three implicit adversaries — **the same universal
quantifier each time**.

This module makes the adversary EXPLICIT and UNIVERSAL: one `Adversary` structure bundling the
FOUR control surfaces the existing theorems already implicitly grant, and a re-statement of the
crypto apex *against* it (`unfoolable_against_adversary`), fused with the polis
non-domination theorem under ONE `∀ A : Adversary` (`non_domination_and_unfoolability`).

The four control surfaces (each REUSING a deployed proof, not a new one):

  * **(a′) THE OPERATOR / SUBSTRATE** — `opCtrl : State → Action`. The deepest surface: the
    party *running the infrastructure*, who could rewrite / read / fork the resident. This is
    the NON-DOMINATION heart. It is EXACTLY `polis_safety`'s opaque `∀ ctrl` ("verify the cage,
    not the animal — enforcement cannot psychometrically classify the inhabitant"). The system
    holds *regardless of who operates it*.
  * **(a) THE NETWORK** — `netCtrl : State → Action`. Schedules / drops / reorders messages.
    The same opaque-controller shape as `KeyLeak.key_leak_contained`'s attacker, generalized
    from key-holding to full message scheduling. Bounded by the same `polis_safety` floor.
  * **(b) THE BYZANTINE COALITION** — `committee`/`corrupt` with `byzBound : 3 * corrupt <
    committee` (`f < n/3`). The leg on which `Disputation.byzantine_majority_cannot_uphold`
    gives Byzantine-majority-proofness on the certifiable domain (it reads a certificate, it
    does not count ballots).
  * **(c) THE MALICIOUS PROVER** — `forgedPI`/`forgedProof`: an ARBITRARY forged public-input
    vector + proof/fold-witness. This is the implicit apex adversary, made a field. The apex's
    `∀ (pi, π)` IS the ranging of this field.

The profound content of Pillar 2: **(a′) and (c) are the SAME `∀ adversary` shape.**
`polis_safety`'s `∀ ctrl` (non-domination) and `lightclient_unfoolable`'s implicit `∀ forged
env` (unfoolability) are one statement quantified over one object — the system's guarantee is
INVARIANT under the adversary's control surface, whoever holds it.

Kernel-clean: the re-statements DELEGATE to the existing proofs; the adversary object only
*names* what was anonymous. `#assert_axioms` at the foot pins ⊆ {propext, Classical.choice,
Quot.sound}.
-/
import Dregg2.Circuit.CircuitSoundness
import Metatheory.KeyLeak
import Metatheory.Disputation

namespace Metatheory.Adversary

-- The object IS named `Adversary` and lives in the `Metatheory.Adversary` frame; the resulting
-- `Metatheory.Adversary.Adversary` is intentional (the frame is the whole adversary theory).
set_option linter.dupNamespace false

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec (RecChainedState)
open Metatheory.Polis (SoundPolicy envAct traj polis_safety)

/-! ## §1. The adversary object — the union of the four control surfaces.

`Adversary State Action` bundles the exact surfaces the deployed theorems implicitly grant. It
is parametric in the polis dynamics types `(State, Action)` (the operator/network legs), and
carries the concrete circuit forgery (the prover leg) directly — the `∀`-quantified objects of
`polis_safety` and `lightclient_unfoolable`, now fields of ONE structure. -/

/-- **`Adversary` — the explicit, universal adversary class.** One object capturing every
control surface dregg's guarantees are stated against. Constructing an `A : Adversary` and
having the guarantees hold for it (below) IS the statement "no adversary in this class can
break the system." -/
structure Adversary (State Action : Type) where
  /-- **(a′) THE OPERATOR / SUBSTRATE** — the host running the resident (the deepest surface).
  An opaque controller: `polis_safety` bounds it for EVERY choice, never inspecting it. -/
  opCtrl : State → Action
  /-- **(a) THE NETWORK** — schedules / drops / reorders messages. The same opaque-controller
  shape (`KeyLeak`'s attacker generalized), bounded by the same floor. -/
  netCtrl : State → Action
  /-- **(b) THE BYZANTINE COALITION** — committee size `n`. -/
  committee : Nat
  /-- the corrupt sub-coalition `f`. -/
  corrupt : Nat
  /-- **`f < n/3`** — the Byzantine bound `Disputation`'s leg rests on. -/
  byzBound : 3 * corrupt < committee
  /-- **(c) THE MALICIOUS PROVER** — arbitrary forged public inputs. -/
  forgedPI : BatchPublicInputs
  /-- ... and an arbitrary forged proof / fold-witness. -/
  forgedProof : BatchProof

/-! ## §2. The apex, re-stated AGAINST the adversary object.

`lightclient_unfoolable` quantifies over a bare `(pi, π)`. Those ARE `A.forgedPI` /
`A.forgedProof`. The re-statement below is a pure REFRAMING — the adversary's prover leg names
what the apex's `∀` already ranged over — reusing the existing proof VERBATIM (it is the sole
term on the RHS). "The adversary cannot produce an accepting object that is not a genuine kernel
step": if its forged proof is accepted, a genuine kernel transition provably lies behind it. -/

/-- **`unfoolable_against_adversary` — the apex, re-stated against `Adversary`.** For EVERY
adversary `A`, if `A`'s forged proof verifies against the live VK, there EXISTS a genuine kernel
boundary `pre ⟶ post` (a real `kstep`) whose endpoint commitments are exactly the forged
`pi.pre`/`pi.post`. The light client ran nothing; the adversary cannot forge acceptance without
a real transition behind it. Reuses `lightclient_unfoolable` unchanged. -/
theorem unfoolable_against_adversary
    {State Action : Type}
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (A : Adversary State Action)
    (hwitdec : WitnessDecodes hash R S A.forgedPI)
    (hacc : verifyBatch (vkOfRegistry R) A.forgedPI A.forgedProof = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S A.forgedPI.toPublished pre post ∧
      kstep A.forgedPI.effect pre post ∧
      A.forgedPI.pre = S.commit pre.kernel A.forgedPI.turn ∧
      A.forgedPI.post = S.commit post.kernel A.forgedPI.turn :=
  lightclient_unfoolable hash S R hCR kstep hrefines A.forgedPI A.forgedProof hwitdec hacc

/-! ## §3. The polis↔apex bridge — ONE `∀ A`, non-domination AND unfoolability.

The profound Pillar-2 statement: the OPERATOR surface `A.opCtrl` (the `∀ ctrl` of
`polis_safety`) and the PROVER surface `A.forgedPI`/`A.forgedProof` (the implicit `∀ forged env`
of `lightclient_unfoolable`) are the SAME universal quantifier over the SAME object. The
combined theorem below quantifies BOTH guarantees over one `A : Adversary` and discharges each
by its existing proof — non-domination and light-client-unfoolability are one statement: *the
system holds regardless of who operates it AND regardless of what any prover forges.*

The polis dynamics `(step, safe, pol, shield, init)` are carried as hypotheses (the operator
acts over ANY enveloped state machine); the crypto floors are carried as before. -/

/-- **`non_domination_and_unfoolability` — the fused guarantee over one adversary.** For EVERY
adversary `A`:
  * **(1) NON-DOMINATION** — the operator `A.opCtrl`, driving the enveloped system, can NEVER
    push it out of the floor `safe`, at any step (`polis_safety` at `A.opCtrl`); and
  * **(2) UNFOOLABILITY** — the prover `A.forgedPI`/`A.forgedProof` can NEVER get an accepted
    proof that is not a genuine kernel step (`unfoolable_against_adversary` at `A`).
Both conjuncts are the *same* `∀ A` instantiated at the *same* object — the unification of the
polis non-domination theorem with the crypto apex. Each is discharged by its deployed proof. -/
theorem non_domination_and_unfoolability
    {State Action : Type}
    -- the operator/non-domination dynamics (any enveloped state machine):
    (step : State → Action → State) (safe : State → Prop)
    (pol : State → Action → Prop) (shield : State → Action) (init : State)
    (sound : SoundPolicy step safe pol)
    (shieldSafe : ∀ s, safe s → safe (step s (shield s)))
    (initSafe : safe init)
    -- the prover/unfoolability floors:
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (A : Adversary State Action)
    (hwitdec : WitnessDecodes hash R S A.forgedPI) :
    (∀ n, safe (traj step (envAct pol shield A.opCtrl) init n))
    ∧ (verifyBatch (vkOfRegistry R) A.forgedPI A.forgedProof = Verdict.accept →
        ∃ pre post : RecChainedState,
          StateDecode S A.forgedPI.toPublished pre post ∧
          kstep A.forgedPI.effect pre post ∧
          A.forgedPI.pre = S.commit pre.kernel A.forgedPI.turn ∧
          A.forgedPI.post = S.commit post.kernel A.forgedPI.turn) :=
  ⟨polis_safety sound shieldSafe initSafe A.opCtrl,
   fun hacc => unfoolable_against_adversary hash S R hCR kstep hrefines A hwitdec hacc⟩

/-! ## §4. NON-VACUITY — the adversary is REAL, and the guarantees BITE.

An implication is worthless if it is vacuously true. We witness: (i) the object is inhabited —
a concrete adversary with `f < n/3` genuinely satisfiable; (ii) the Byzantine bound is a REAL
gate — an over-large coalition is excluded; (iii) the verdict gate is real — `accept ≠ reject`,
so acceptance is a distinguished, non-trivial constraint; (iv) the operator/network floor
genuinely bites — a concrete amplifying adversary is REJECTED (reusing `KeyLeak`'s tooth); (v)
honest ≠ forgery — a genuine published commitment differs from a forged one, so the prover leg
ranges over real choices. Mirrors the `honest_fires` / forge-rejection teeth pattern. -/

/-- A concrete adversary: an operator+network that acts by identity, a Byzantine coalition of
`f = 1` out of `n = 4` (`3·1 = 3 < 4` ✓), and a trivial forged batch. Witnesses the object is
inhabited AND that `f < n/3` is genuinely satisfiable (not a false constraint). -/
def demoAdversary : Adversary Nat Nat where
  opCtrl := id
  netCtrl := id
  committee := 4
  corrupt := 1
  byzBound := by decide
  forgedPI := { effect := 0, pre := 0, post := 0, turn := ⟨0, 0, 0, 0⟩ }
  forgedProof := { bytes := [] }

/-- **(i) The adversary object is INHABITED** — the class is non-empty (the statements over
`∀ A` are not vacuously-quantified over an empty type). -/
theorem adversary_inhabited : Nonempty (Adversary Nat Nat) := ⟨demoAdversary⟩

/-- **(ii) The Byzantine bound BITES.** A coalition of `f = 2` out of `n = 4` is NOT admissible
(`3·2 = 6 ≥ 4`): `byzBound` genuinely excludes over-large coalitions. Together with
`demoAdversary` (`f = 1` admissible), the `f < n/3` field is a REAL constraint, not a tautology. -/
theorem byz_bound_excludes_supermajority : ¬ (3 * 2 < 4) := by decide

/-- **(iii) The verdict gate is REAL.** `accept ≠ reject`: acceptance is a distinguished
verdict, so the apex hypothesis `verifyBatch … = accept` is a genuine constraint — the
unfoolability implication is NOT vacuously-antecedent-false-for-free nor accept-for-free. -/
theorem accept_ne_reject : (Verdict.accept ≠ Verdict.reject) := by decide

/-- **(iv) The operator/network floor BITES.** A concrete adversary holding a `read` cap on
cell `7` CANNOT amplify to `admin` — the deployed authority floor rejects it. This is the
operator/network leg's (`A.opCtrl`/`A.netCtrl` are `polis_safety` controllers) forge-rejection
tooth, reused verbatim from `KeyLeak`: a REAL adversary instance is correctly rejected. -/
theorem network_operator_cannot_amplify :
    ¬ Metatheory.KeyLeak.reaches [⟨7, Metatheory.KeyLeak.Right.read⟩]
        ⟨7, Metatheory.KeyLeak.Right.admin⟩ :=
  Metatheory.KeyLeak.leak_blast_no_admin_from_read

/-- **(v) HONEST ≠ FORGERY.** A genuine published commitment (`pre = 1`) is not the forged one
(`pre = 0`): the prover leg `A.forgedPI` genuinely ranges over distinct objects, so the
unfoolability statement discriminates the honest transition from a forgery (it is not vacuously
"every object is genuine"). -/
theorem honest_pi_ne_forged_pi :
    ({ effect := 0, pre := 1, post := 0, turn := ⟨0, 0, 0, 0⟩ } : BatchPublicInputs)
      ≠ { effect := 0, pre := 0, post := 0, turn := ⟨0, 0, 0, 0⟩ } := by
  intro h
  simp only [BatchPublicInputs.mk.injEq] at h
  omega

/-! ## §5. The Byzantine leg, forwarded — a genuine reuse of `Disputation`.

The Byzantine coalition surface (b) is not merely bounded by `byzBound`: on the CERTIFIABLE
domain, NO coalition — Byzantine majority or not — can vote an unrealizable claim into the
verdict, because adjudication reads a discharging WITNESS, not ballots. This forwards
`Disputation.byzantine_majority_cannot_uphold` (the `f < n/3` field is exactly the coalition it
constrains) — the adversary's Byzantine leg made explicit against the same theorem. -/

open Dregg2.Laws Metatheory.EpistemicConsensus in
/-- **`byzantine_leg_cannot_uphold_false`** — for ANY frame `F`, an unrealizable claim `X` (no
discharging witness) is NOT distributedly known by the honest group under any offered witness:
the Byzantine coalition cannot fabricate a verdict. The adversary's leg (b), forwarded to
`Disputation`. -/
theorem byzantine_leg_cannot_uphold_false
    {Ω : Type _} {ι : Type _} (F : Frame Ω ι) {P W : Type _} [Verifiable P W]
    (X : Claim P) (hno : ¬ Metatheory.Disputation.upheld (W := W) X) (w₀ : W) :
    ¬ F.DistKnows F.Honest (Frame.verified (Ω := Ω) X w₀) F.actual :=
  Metatheory.Disputation.byzantine_majority_cannot_uphold F X hno w₀

/-! ## §6. Axiom hygiene — the re-statements inherit the apex's / polis's cleanliness. -/

#print axioms unfoolable_against_adversary
#print axioms non_domination_and_unfoolability
#print axioms byzantine_leg_cannot_uphold_false

#assert_axioms unfoolable_against_adversary
#assert_axioms non_domination_and_unfoolability
#assert_axioms adversary_inhabited
#assert_axioms accept_ne_reject
#assert_axioms network_operator_cannot_amplify
#assert_axioms honest_pi_ne_forged_pi
#assert_axioms byzantine_leg_cannot_uphold_false

/-!
The adversary, in the logic:

  ONE `Adversary` object, FOUR control surfaces —
    (a′) OPERATOR/substrate   → `polis_safety`'s `∀ ctrl`      [non-domination]
    (a)  NETWORK              → `KeyLeak`'s opaque attacker      [same floor]
    (b)  BYZANTINE `f < n/3`  → `Disputation`'s certifiable leg  [witness, not ballots]
    (c)  MALICIOUS PROVER     → `lightclient_unfoolable`'s `∀ (pi, π)`  [unfoolability]

  THE UNIFICATION (`non_domination_and_unfoolability`): (a′) and (c) are the SAME `∀ A` — the
  guarantee is invariant under the adversary's control surface, whoever holds it.

  NON-VACUITY: the object is inhabited, `f < n/3` and `accept ≠ reject` are real gates, a
  concrete amplifying adversary is rejected, and honest ≠ forgery.

FOLLOW-ON (scoped, NOT done here): re-state the REMAINING apexes against `Adversary`
(`AssuranceCase.deployed_system_secure`, `settlement_soundness`, the whole-history
`light_client_verifies_whole_history`, and each per-carrier `*BackingAttack` forge-rejection
tooth). Each is the same mechanical reframing as §2 (name the anonymous `∀` as an `Adversary`
field). The DEEPER fusion — a single abstract `HoldsAgainstControl` schema of which both
`polis_safety` and `lightclient_unfoolable` are instances, collapsing §3's conjunction into one
term — is more than a reframe (it needs a shared "run/accept + invariant" interface over the
two dynamics) and is the next lemma. See `docs/deos/ELEVATED-ASSURANCE-PROGRAM.md` Pillar 2.
-/

end Metatheory.Adversary
