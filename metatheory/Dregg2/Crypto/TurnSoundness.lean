/-
# `Dregg2.Crypto.TurnSoundness` — TURN / EFFECT-VM SOUNDNESS: a valid receipt PROVES correct,
authorized state evolution. The TOP of the crypto up-climb — it ties the protocol's core claim
("a turn is the exercise of an attenuable proof-carrying token over owned state, leaving a
verifiable receipt") to the crypto floor.

The whole tower below proves *pieces*: `HybridCombiner.lean` shows the turn's authorization signature
is EUF-CMA-unforgeable if EITHER the discrete-log floor OR the Module-SIS floor holds
(`hybrid_secure_if_either_floor`); `Circuit.lean` shows a satisfying STARK witness PROVES the verified
step invariant (`circuit_sound`). This file WELDS them into the one claim the protocol makes to an
outside observer:

  **a VALID receipt for a turn `(oldState, effect, newState)` ⟹ the actor AUTHORIZED the effect over
  the old state AND `newState` is the CORRECT application of the effect-VM to `oldState`.**

So no adversary can forge a *state evolution* without either (a) forging the actor's signature — which
reduces through `EufCma` down to `SchnorrDLHard ∨ MSISHard` — or (b) exhibiting a false execution proof
— which contradicts the STARK circuit-soundness assumption.

## The model (abstract, honest)

* A **`Turn`** is `(old, eff, new)` — the effect-VM's claimed step. The VM's deterministic transition is
  the parameter `applyEff : Effect → State → State` (the Rust `turn/` interpreter; in-circuit it is the
  kernel AIR of `Circuit.lean`).
* A **`Receipt`** is `(authSig, execProof)`: the actor's signature over the turn's *precondition*
  `(old, eff)`, and the STARK/descriptor proof that the transition was executed correctly.
* **`Valid`** := the effect is AUTHORIZED (`S.verify` of `authSig` over `encMsg old eff` by the actor)
  ∧ the transition is CORRECTLY WITNESSED (`checks execProof old eff new` — the circuit verifier accepts).

## The two obligations, and which floor each rests on

* **Authorization** rests on the HARDNESS floor. The actor's signing oracle is the query set `Q`; the
  actor genuinely authorized the turn iff `Q (encMsg old eff)`. A valid receipt whose message was NEVER
  signed is a `HybridCombiner.Forgery` (fresh + verifying) — refuting `EufCma`, hence
  `SchnorrDLHard ∨ MSISHard`. This is a real cryptographic assumption, discharged to the floor.

* **Correct execution** rests on the CIRCUIT-SOUNDNESS boundary — an EXPLICIT, clearly-labelled
  hypothesis `CircuitSound applyEff checks`: *if the circuit verifier accepts `execProof` for
  `(old, eff, new)` then `new = applyEff eff old`*. This is NOT a hardness carrier and is NOT laundered
  as a proof: it is the honest boundary of this file, the proven-elsewhere circuit floor. For the
  deployed kernel AIR it is discharged by `Dregg2.Circuit.circuit_sound` (a satisfying witness ⟹ the
  verified step invariant); the residual seam it carries (the CR-hash digest binding the Rust prover's
  wires) is `Circuit.lean`'s named `-- PRIMITIVE:` obligation, reducible to `HashCR`, not re-asserted here.

## No named-carrier laundering

`CircuitSound` is a HYPOTHESIS of every theorem, never an `axiom` and never `:= True`; `#assert_axioms`
does not check hypotheses, so it is stated in the open where an auditor reads it. The authorization half
reduces THROUGH `HybridCombiner.hybrid_secure_if_either_floor` to the genuine floors `SchnorrDLHard` /
`MSISHard` (`Lattice.lean`) — the forking reductions are hypotheses (theorems of the existing machinery),
not carriers.

## Teeth (both load-bearing)

* **Unauthorized turn ⟹ no valid receipt** (`unauthorized_rejected`): under `EufCma`, a turn whose
  precondition the actor never signed cannot carry a verifying `authSig`. The forgery tooth: strip
  `EufCma` and a concrete forged receipt on an un-signed turn goes through (`toy_forgery`).
* **Wrong transition ⟹ no execution proof** (`wrong_transition_rejected`): under `CircuitSound`, a turn
  whose `new ≠ applyEff eff old` has no `execProof` the verifier accepts. The circuit tooth: strip
  `CircuitSound` (a checker that accepts anything — `badChecks`, provably NOT `CircuitSound`) and a
  wrong-transition receipt is `Valid` yet the state evolution is false.

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake env lean Dregg2/Crypto/TurnSoundness.lean`.
-/
import Dregg2.Crypto.HybridCombiner
import Dregg2.Tactics

namespace Dregg2.Crypto.TurnSoundness

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField

/-! ## §1 — The turn, the receipt, and validity. -/

/-- **`Turn State Effect`** — the effect-VM's claimed step: an old state, an effect, and the new state
the VM says the effect produces. This is the object a receipt attests. -/
structure Turn (State Effect : Type*) where
  /-- The pre-state the effect acts on. -/
  old : State
  /-- The effect exercised this turn. -/
  eff : Effect
  /-- The post-state the VM claims. -/
  new : State

/-- **`Receipt Sig Proof`** — the verifiable artifact a turn leaves: the actor's authorization signature
over the turn's precondition, and the execution proof that the transition was run correctly. -/
structure Receipt (Sig Proof : Type*) where
  /-- The actor's signature over `encMsg old eff` (the turn's precondition). -/
  authSig : Sig
  /-- The STARK/descriptor proof that `new = applyEff eff old`. -/
  execProof : Proof

variable {State Effect SK PK Msg Sig Proof : Type*}

/-- **`CorrectTransition`** — the turn's post-state is the effect-VM's actual application to the
pre-state. The denotational fact the execution proof must witness. -/
def CorrectTransition (applyEff : Effect → State → State) (t : Turn State Effect) : Prop :=
  t.new = applyEff t.eff t.old

/-- **`Valid`** — a receipt is valid for a turn iff BOTH gates pass: the actor's signature verifies over
the turn precondition `(old, eff)` (AUTHORIZATION), and the execution proof is accepted by the circuit
verifier `checks` for `(old, eff, new)` (CORRECT EXECUTION). This is the verifier's decision — the whole
content of "a verifiable receipt". -/
def Valid (S : SigScheme SK PK Msg Sig) (encMsg : State → Effect → Msg)
    (checks : Proof → State → Effect → State → Prop)
    (actorPk : PK) (t : Turn State Effect) (r : Receipt Sig Proof) : Prop :=
  S.verify actorPk (encMsg t.old t.eff) r.authSig ∧ checks r.execProof t.old t.eff t.new

/-- **`CircuitSound` — the honest circuit-soundness boundary (an explicit hypothesis, NOT a carrier).**
If the circuit verifier `checks` accepts `execProof` for `(old, eff, new)`, then `new` really is the
effect-VM's application `applyEff eff old`. For the deployed kernel AIR this is discharged by
`Dregg2.Circuit.circuit_sound`; here it is the named boundary the turn-soundness theorems rest on for
their EXECUTION half. It is never `:= True` and never an `axiom` — an auditor reads it in each theorem's
hypotheses. -/
def CircuitSound (applyEff : Effect → State → State)
    (checks : Proof → State → Effect → State → Prop) : Prop :=
  ∀ (π : Proof) (old : State) (eff : Effect) (new : State),
    checks π old eff new → new = applyEff eff old

/-! ## §2 — The headline: a valid receipt proves authorized, correct evolution. -/

/-- **THEOREM `turn_sound` (headline).** Under the actor's `EufCma` (its authorization signature is
unforgeable over its signing log `Q`) and the circuit-soundness boundary `CircuitSound applyEff checks`,
a VALID receipt for a turn `(old, eff, new)` proves BOTH:

  1. **AUTHORIZED** — `Q (encMsg old eff)`: the actor genuinely signed this precondition (no forged
     evolution: a receipt on an unsigned precondition would be a `Forgery`, refuting `EufCma`).
  2. **CORRECT** — `new = applyEff eff old`: the post-state is the effect-VM's true application (no false
     evolution: the execution proof witnesses correctness, by circuit soundness).

So no adversary forges a state evolution without breaking the signature OR the circuit. -/
theorem turn_sound
    (S : SigScheme SK PK Msg Sig) (encMsg : State → Effect → Msg)
    (applyEff : Effect → State → State) (checks : Proof → State → Effect → State → Prop)
    (actorPk : PK) (Q : Msg → Prop)
    (heuf : EufCma S actorPk Q)
    (hcs : CircuitSound applyEff checks)
    (t : Turn State Effect) (r : Receipt Sig Proof)
    (hvalid : Valid S encMsg checks actorPk t r) :
    Q (encMsg t.old t.eff) ∧ CorrectTransition applyEff t := by
  obtain ⟨hverify, hchecks⟩ := hvalid
  refine ⟨?_, ?_⟩
  · -- Authorization: if the precondition were unsigned, `(msg, authSig)` is a fresh verifying forgery.
    by_contra hnq
    exact heuf ⟨encMsg t.old t.eff, r.authSig, hnq, hverify⟩
  · -- Correct execution: circuit soundness turns the accepted proof into the denotational equality.
    exact hcs r.execProof t.old t.eff t.new hchecks

/-! ## §3 — The two teeth as standalone rejection lemmas (both load-bearing). -/

/-- **TOOTH 1 (forgery) — an UNAUTHORIZED turn is rejected.** Under `EufCma`, a turn whose precondition
`(old, eff)` the actor never signed (`¬ Q (encMsg old eff)`) has NO valid receipt: a verifying `authSig`
on it would be a fresh forgery. This is where forging a state evolution reduces to forging the signature
(→ `EufCma` → `SchnorrDLHard ∨ MSISHard`). -/
theorem unauthorized_rejected
    (S : SigScheme SK PK Msg Sig) (encMsg : State → Effect → Msg)
    (checks : Proof → State → Effect → State → Prop)
    (actorPk : PK) (Q : Msg → Prop)
    (heuf : EufCma S actorPk Q)
    (t : Turn State Effect) (hnq : ¬ Q (encMsg t.old t.eff)) (r : Receipt Sig Proof) :
    ¬ Valid S encMsg checks actorPk t r := by
  rintro ⟨hverify, _⟩
  exact heuf ⟨encMsg t.old t.eff, r.authSig, hnq, hverify⟩

/-- **TOOTH 2 (circuit) — a WRONG transition has no execution proof.** Under `CircuitSound`, a turn whose
claimed `new ≠ applyEff eff old` has no `execProof` the verifier accepts: acceptance would force the
denotational equality it violates. This is where forging a state evolution reduces to a false execution
proof (→ the circuit-soundness assumption). -/
theorem wrong_transition_rejected
    (applyEff : Effect → State → State) (checks : Proof → State → Effect → State → Prop)
    (hcs : CircuitSound applyEff checks)
    (t : Turn State Effect) (hwrong : t.new ≠ applyEff t.eff t.old) (π : Proof) :
    ¬ checks π t.old t.eff t.new :=
  fun hc => hwrong (hcs π t.old t.eff t.new hc)

/-- Corollary: a wrong transition has no valid receipt (its execution proof cannot be accepted). -/
theorem wrong_transition_no_valid
    (S : SigScheme SK PK Msg Sig) (encMsg : State → Effect → Msg)
    (applyEff : Effect → State → State) (checks : Proof → State → Effect → State → Prop)
    (hcs : CircuitSound applyEff checks) (actorPk : PK)
    (t : Turn State Effect) (hwrong : t.new ≠ applyEff t.eff t.old) (r : Receipt Sig Proof) :
    ¬ Valid S encMsg checks actorPk t r :=
  fun hvalid => wrong_transition_rejected applyEff checks hcs t hwrong r.execProof hvalid.2

/-! ## §4 — The anchor: discharge authorization to the floor via the hybrid combiner.

The turn's authorization signature IS the `ed25519 ∧ ML-DSA` hybrid. So the actor's `EufCma` is not
assumed but DISCHARGED by `HybridCombiner.hybrid_secure_if_either_floor` from `SchnorrDLHard ∨ MSISHard`.
Circuit soundness stays an explicit hypothesis (the honest boundary). The result: a valid receipt proves
authorized, correct evolution under `(SchnorrDLHard ∨ MSISHard) ∧ circuit-soundness`. -/

section UnderFloor
variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {Mod : Type*} [AddCommGroup Mod] [Module Rq Mod] [ShortNorm Mod]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- **THEOREM `turn_sound_under_floor` (the crypto payoff).** The actor's turn-authorization signature is
the hybrid `Cl × Pq` (`ed25519 × ML-DSA`). Given the two forking reductions (theorems of the existing
machinery, `dlFork` / `msisFork`) and the circuit-soundness boundary `CircuitSound applyEff checks`, a
VALID receipt proves the turn was AUTHORIZED by the actor AND its transition is CORRECT — under the single
disjunctive floor `SchnorrDLHard ∨ MSISHard`. Even a quantum adversary that breaks discrete log still
faces Module-SIS; only if BOTH hardness floors fall (or the circuit is unsound) can a state evolution be
forged. -/
theorem turn_sound_under_floor
    (Cl : SigScheme SK PK Msg Sig) (Pq : SigScheme SK PK Msg Sig)
    (pkc pkp : PK) (encMsg : State → Effect → Msg)
    (applyEff : Effect → State → State) (checks : Proof → State → Effect → State → Prop)
    (Q : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    (A : Mod →ₗ[Rq] N) (tgt : N) (β : ℕ)
    (dlFork : Forgery Cl pkc Q → DLSolver C G)
    (msisFork : Forgery Pq pkp Q →
      ∃ (w : N) (c c' : Rq) (z z' : Mod), c ≠ c' ∧
        IsSelfTargetMSISSolution A tgt β z c w ∧ IsSelfTargetMSISSolution A tgt β z' c' w)
    (hcs : CircuitSound applyEff checks)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A tgt) ((β + β) + (β + β)))
    (t : Turn State Effect) (r : Receipt (Sig × Sig) Proof)
    (hvalid : Valid (hybrid Cl Pq) encMsg checks (pkc, pkp) t r) :
    Q (encMsg t.old t.eff) ∧ CorrectTransition applyEff t := by
  have heuf : EufCma (hybrid Cl Pq) (pkc, pkp) Q :=
    hybrid_secure_if_either_floor Cl Pq pkc pkp Q C G A tgt β dlFork msisFork hfloor
  exact turn_sound (hybrid Cl Pq) encMsg applyEff checks (pkc, pkp) Q heuf hcs t r hvalid

end UnderFloor

/-! ## §5 — Teeth on a concrete effect-VM: both gates fire in BOTH directions.

The toy VM: `State = Effect = ℕ`, `applyEff eff old = old + eff` (an additive counter), the precondition
message `encMsg old eff = (old, eff)`. A toy signature scheme `toyS` (`verify pk m sig := sig = pk + m.1 +
m.2`) isolates the authorization gate; a proof-checker `goodChecks` accepts exactly the correct transition
and IS `CircuitSound`, while `badChecks` accepts everything and is provably NOT. -/

/-- The toy effect-VM transition: an additive counter. -/
@[reducible] def toyApply : ℕ → ℕ → ℕ := fun eff old => old + eff

/-- The precondition encoding: the message the actor signs is the pair `(old, eff)`. -/
@[reducible] def toyEnc : ℕ → ℕ → (ℕ × ℕ) := fun old eff => (old, eff)

/-- A toy signature scheme over `ℕ` keys and `ℕ × ℕ` messages: `verify pk m sig := sig = pk + m.1 + m.2`.
Forgeable (verification is public) — exactly why `EufCma` is a real hypothesis, and why the forgery tooth
below bites when it is dropped. -/
@[reducible] def toyS : SigScheme ℕ ℕ (ℕ × ℕ) ℕ where
  pkOf sk := sk
  sign sk m := sk + m.1 + m.2
  verify pk m sig := sig = pk + m.1 + m.2

/-- The actor's public key. -/
@[reducible] def toyActor : ℕ := 5

/-- The actor's signing log: it authorized exactly the precondition `(old = 10, eff = 3)`. -/
def toyQ : (ℕ × ℕ) → Prop := fun m => m = (10, 3)

/-- The CORRECT proof-checker: accepts `π` for `(old, eff, new)` iff `new = old + eff`. This is the
denotational content of the STARK verifier for the toy VM. -/
@[reducible] def goodChecks : Unit → ℕ → ℕ → ℕ → Prop := fun _ old eff new => new = old + eff

/-- The BROKEN proof-checker: accepts everything — the model of an UNSOUND circuit. -/
@[reducible] def badChecks : Unit → ℕ → ℕ → ℕ → Prop := fun _ _ _ _ => True

/-- **`goodChecks` IS circuit-sound** for the toy VM: acceptance entails the true transition. -/
theorem goodChecks_sound : CircuitSound toyApply goodChecks := by
  intro π old eff new h
  simpa [toyApply, goodChecks] using h

/-- **`badChecks` is NOT circuit-sound** — it accepts the wrong transition `0 + 0 ↦ 1`. So the
circuit-soundness boundary is genuine content, not free: drop it and correctness is unprotected. -/
theorem badChecks_not_sound : ¬ CircuitSound toyApply badChecks := by
  intro h
  have hbad : (1 : ℕ) = toyApply 0 0 := h () 0 0 1 trivial
  simp [toyApply] at hbad

/-! ### The honest turn: authorized AND correct → a valid receipt whose soundness conclusions hold. -/

/-- The honest turn `(old = 10, eff = 3, new = 13)` — a correct additive step the actor authorized. -/
def goodTurn : Turn ℕ ℕ := ⟨10, 3, 13⟩

/-- The honest receipt: `authSig = actor + old + eff = 18` (verifies), execution proof `()`. -/
def goodReceipt : Receipt ℕ Unit := ⟨5 + 10 + 3, ()⟩

/-- **RESPECTING INSTANCE.** The honest receipt is `Valid` for the honest turn: the signature verifies
and the correct transition checks. -/
theorem goodReceipt_valid : Valid toyS toyEnc goodChecks toyActor goodTurn goodReceipt := by
  refine ⟨?_, ?_⟩
  · show (5 + 10 + 3 : ℕ) = 5 + 10 + 3
    rfl
  · show (13 : ℕ) = 10 + 3
    rfl

/-- …and its soundness conclusions genuinely hold: the actor authorized `(10, 3)` and `13 = applyEff 3 10`.
(The honest world the headline promises.) -/
theorem goodTurn_authorized_and_correct :
    toyQ (toyEnc goodTurn.old goodTurn.eff) ∧ CorrectTransition toyApply goodTurn := by
  refine ⟨?_, ?_⟩
  · show ((10, 3) : ℕ × ℕ) = (10, 3); rfl
  · show (13 : ℕ) = 10 + 3; rfl

/-! ### Forgery tooth: strip `EufCma` and an unsigned turn gets a verifying receipt. -/

/-- The forged turn `(old = 20, eff = 7, new = 27)` — a *correct* additive step, but on a precondition the
actor NEVER signed (`(20, 7) ∉ toyQ`). -/
def forgedTurn : Turn ℕ ℕ := ⟨20, 7, 27⟩

/-- **FORGERY TOOTH (load-bearing).** Because `toyS` is forgeable (no `EufCma`), the unsigned precondition
`(20, 7)` carries a verifying signature `5 + 20 + 7 = 32` — a `HybridCombiner.Forgery`. So WITHOUT the
`EufCma` hypothesis of `turn_sound`, the AUTHORIZATION conclusion fails: an adversary mints a valid-looking
receipt for a turn the actor never authorized. `unauthorized_rejected` is exactly what `EufCma` buys. -/
theorem toy_forgery : Forgery toyS toyActor toyQ := by
  refine ⟨(20, 7), 5 + 20 + 7, ?_, ?_⟩
  · -- (20, 7) ≠ (10, 3): the actor never signed this precondition.
    intro h; simp [toyQ] at h
  · -- yet the signature verifies.
    show (5 + 20 + 7 : ℕ) = 5 + 20 + 7; rfl

/-! ### Circuit tooth: strip `CircuitSound` and a wrong transition gets a valid receipt. -/

/-- The WRONG turn `(old = 10, eff = 3, new = 999)` — `999 ≠ 10 + 3`: a false state evolution the actor
DID authorize (same precondition `(10, 3)`). -/
def wrongTurn : Turn ℕ ℕ := ⟨10, 3, 999⟩

/-- **CIRCUIT TOOTH (load-bearing).** Under the honest checker `goodChecks` the wrong turn is rejected —
`wrong_transition_rejected` (via `goodChecks_sound`) gives no accepting proof. But under the UNSOUND
`badChecks` the wrong turn's receipt is `Valid` (the actor authorized `(10, 3)`, and `badChecks` accepts
the false `new = 999`). So the CORRECTNESS conclusion of `turn_sound` genuinely rests on `CircuitSound`:
drop it and a forged state evolution verifies. -/
theorem wrong_turn_rejected_when_sound (r : Receipt ℕ Unit) :
    ¬ Valid toyS toyEnc goodChecks toyActor wrongTurn r :=
  wrong_transition_no_valid toyS toyEnc toyApply goodChecks goodChecks_sound toyActor
    wrongTurn (by show (999 : ℕ) ≠ 10 + 3; decide) r

/-- The wrong turn IS `Valid` under the unsound checker — the tooth: without circuit-soundness a false
evolution goes through. The receipt reuses the actor's honest authorization over the (authorized) precondition
`(10, 3)`. -/
theorem wrong_turn_valid_when_unsound :
    Valid toyS toyEnc badChecks toyActor wrongTurn ⟨5 + 10 + 3, ()⟩ := by
  refine ⟨?_, ?_⟩
  · show (5 + 10 + 3 : ℕ) = 5 + 10 + 3; rfl
  · trivial

-- The honest signature verifies over the AUTHORIZED precondition (10, 3)…
#guard decide (toyS.verify toyActor (toyEnc 10 3) (5 + 10 + 3))
-- …and a FORGED signature also verifies over an UN-signed precondition (20, 7) — EufCma is load-bearing.
#guard decide (toyS.verify toyActor (toyEnc 20 7) (5 + 20 + 7))
-- The correct transition checks under the sound checker…
#guard decide (goodChecks () 10 3 13)
-- …the WRONG transition does NOT (999 ≠ 10 + 3) — the sound checker rejects it…
#guard decide (¬ goodChecks () 10 3 999)
-- …but the UNSOUND checker accepts it — CircuitSound is load-bearing.
#guard decide (badChecks () 10 3 999)

/-! ## §6 — Axiom hygiene: every turn-soundness keystone is kernel-clean. The standing obligations are the
NAMED objects — the hardness floors `SchnorrDLHard` / `MSISHard` (through `HybridCombiner`) and the
explicitly-labelled `CircuitSound` boundary (discharged for the deployed AIR by `Dregg2.Circuit.circuit_sound`). -/

#assert_all_clean [
  turn_sound,
  unauthorized_rejected,
  wrong_transition_rejected,
  wrong_transition_no_valid,
  turn_sound_under_floor,
  goodChecks_sound,
  badChecks_not_sound,
  goodReceipt_valid,
  goodTurn_authorized_and_correct,
  toy_forgery,
  wrong_turn_rejected_when_sound,
  wrong_turn_valid_when_unsound
]

end Dregg2.Crypto.TurnSoundness
