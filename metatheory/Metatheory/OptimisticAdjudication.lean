/-
# Metatheory.OptimisticAdjudication — "FIGHTABLE DISPROOF" AS A DIFFERENT OBJECT FROM "CHECKABLE PROOF".

`Metatheory.Disputation` builds the witness-fibre reflector `R_witness`: a verdict is read off a
**positive discharging witness**, never off a vote, and it escapes the judgment-aggregation
impossibility (Arrow / List–Pettit) precisely by restricting to the **certifiable domain** — you only
adjudicate what admits a certificate. Its whole constructive character is that **it never infers from
an absence.**

An *optimistic* / naysayer settlement inverts that polarity: the verdict is upheld-by-silence and is
flipped by a **refutation** certificate, so it is decided by the ABSENCE of a certificate within a
window. This module is the honest account of what that swap costs. It does NOT claim optimistic
settlement is sound; it isolates exactly which obligations are free, which must be assumed, and it
PROVES the load-bearing assumption is not removable.

## The three regimes, named

| regime            | the verdict is                                    | Byzantine-proof?                      |
|-------------------|---------------------------------------------------|---------------------------------------|
| validity proof    | `∃ w. Discharged` — a realizability fact          | yes (`byzantine_majority_cannot_uphold`) |
| **optimistic**    | **`¬∃` refutation OBSERVED in the window**        | **not a realizability fact at all**   |
| political/ballot  | an aggregation of assertions                      | no — Arrow / List–Pettit              |

The optimistic regime is genuinely a THIRD thing: it is not an aggregation, so the Arrow obstruction
does not apply to it; but it is not a realizability fact either, so `R_witness`'s Byzantine-proofness
does not transfer. This module gives it its own name rather than laundering it as either neighbour.

## What is proved here

* **§2 free half — `upheld_optimisticallyUpheld`.** If a claim genuinely holds, NO sound refutation can
  be observed, so the optimistic verdict never wrongly rejects an honest settlement. This direction is
  free from `refutes_sound` alone. It is the *safety-for-the-honest-prover* half and it costs nothing.
* **§3 costly half — `optimistic_sound`.** The converse needs TWO further obligations, both carried
  EXPLICITLY as hypotheses in the style of the apex's `hfri`, never silently discharged:
  `RefutationComplete` (every false claim admits *some* certificate) and `Actuated` (every certificate
  that exists is actually *observed* in the window).
* **§4 the floor is FALSE without `Actuated` — `optimistic_unsound_without_actuation`.** A concrete,
  fully-inhabited instance where the optimistic verdict UPHOLDS a claim that does NOT hold. Per
  `feedback-prove-the-floor-false`: a floor must be satisfiable and REFUTABLE but not provable. This is
  the refutation. `Actuated` is not a technical convenience — dropping it makes the statement false.
* **§5 the challenger-strength gap — `distKnows_honest_does_not_give_a_challenger`.** The natural
  epistemic reading of the naysayer obligation is *"if the claim is false, the honest group
  distributedly knows a refutation"* (`DistKnows F.Honest`). This section proves that obligation is
  **too weak**: a concrete frame in which the honest group distributedly knows `φ` while NO single
  honest agent knows it. A challenger must be one agent who can act, so the correct obligation is
  `∃ i, Honest i ∧ Knows i`, which is strictly stronger (`knows_imp_distKnows` runs one way only).

## The seam this module exists to make visible

`Actuated` is **not an epistemic fact and not a cryptographic one.** `Frame` has no time, no
scheduling, no message delivery — the gap between *"an honest agent could refute"* and *"an honest
agent will, in time"* is not expressible here at all. That gap is the entire trust delta of an
optimistic construction, which is why no amount of cryptographic engineering closes it. Stating it as
a carried hypothesis, and proving the theorem false without it, is the most this layer can honestly do.

⚠ HISTORY, read before extending: `Metatheory.Disputation`'s own header records that a four-lens
adversarial review refuted the previous headline in this exact conceptual neighbourhood **4/4** (the
`Predicate ⊣ Witness` adjunction thesis, `project-adjunction-thesis-verdict`). This area has already
produced one elegant falsehood. Nothing here should be cited as "optimistic settlement is sound".
-/
import Metatheory.Disputation

namespace Metatheory.OptimisticAdjudication

open Dregg2.Laws Metatheory Metatheory.EpistemicConsensus Metatheory.Disputation

universe u v

/-! # §1. The negative certificate — `Refutable`, the dual of `Verifiable` -/

/-- A **refutation system** for claims in `P` against witness type `W`: a decidable checker
`Refutes : P → R → Bool` for *negative* certificates.

⚑ **`refutes_sound` IS a field, and that asymmetry with `Searchable` is deliberate.**
`Dregg2.Laws.Searchable` pointedly has NO soundness field, so that adversarial prover plugins remain
legal instances — consumers re-`Verify` whatever `find` returns and never trust it. A refutation
checker cannot be treated that way: in an optimistic settlement the refutation is *acted upon*, so an
unsound checker lets a naysayer grief honest settlements with no recourse. The positive side can
afford untrusted search because the verdict re-checks; the negative side cannot, because the verdict
IS the check. -/
class Refutable (P : Type u) (W : Type u) (R : Type u) [Verifiable P W] where
  /-- The decidable checker for negative certificates. -/
  Refutes : P → R → Bool
  /-- **Soundness of refutation**: a certificate the checker accepts genuinely establishes that no
  discharging witness exists. Without this an optimistic verdict is not even safe for honest provers. -/
  refutes_sound : ∀ (p : P) (r : R), Refutes p r = true → ¬ ∃ w : W, Discharged (P := P) (W := W) p w

/-- `Refuted p r` — the proof-relevant statement that `r` refutes `p`. Dual of `Discharged`. -/
def Refuted {P W R : Type u} [Verifiable P W] [Refutable P W R] (p : P) (r : R) : Prop :=
  Refutable.Refutes (W := W) p r = true

variable {P W R : Type u} [Verifiable P W] [Refutable P W R]

/-- **`refuted_not_upheld`** — an accepted refutation certificate defeats the claim outright. This is
the whole content of `refutes_sound`, stated in the adjudication vocabulary of `Disputation.upheld`. -/
theorem refuted_not_upheld (X : Claim P) (r : R) (h : Refuted (P := P) (W := W) X.stmt r) :
    ¬ upheld (P := P) (W := W) X :=
  Refutable.refutes_sound (W := W) X.stmt r h

/-! # §2. The optimistic verdict, and the half that is free -/

/-- **The optimistic (naysayer) verdict.** A claim stands unless a refutation certificate is
*observed* — `observed r` means "certificate `r` was actually delivered inside the challenge window".

Note what this does NOT say: it does not quantify over certificates that *exist*, only over those that
were *seen*. That distinction is the entire subject of this module. -/
def optimisticallyUpheld (X : Claim P) (observed : R → Prop) : Prop :=
  ¬ ∃ r : R, observed r ∧ Refuted (P := P) (W := W) X.stmt r

/-- **`upheld_optimisticallyUpheld` — THE FREE HALF: optimistic settlement never wrongly rejects an
honest prover.** If the claim genuinely holds, no sound refutation of it can exist, hence none can be
observed. This needs only `refutes_sound`: no completeness assumption, no liveness assumption, no
synchrony. It is the direction an optimistic scheme gets for nothing. -/
theorem upheld_optimisticallyUpheld (X : Claim P) (observed : R → Prop)
    (h : upheld (P := P) (W := W) X) :
    optimisticallyUpheld (P := P) (W := W) X observed := by
  rintro ⟨r, -, hr⟩
  exact refuted_not_upheld (W := W) X r hr h

/-! # §3. The costly half — the two obligations, carried explicitly -/

/-- **`RefutationComplete`** — every false claim admits *some* refutation certificate. This is a
property of the refutation SYSTEM (is the negative certificate expressive enough?), and it is a real
design obligation: a refutation language that cannot express some failure mode silently upgrades that
failure mode into an unchallengeable one. -/
def RefutationComplete (X : Claim P) : Prop :=
  ¬ upheld (P := P) (W := W) X → ∃ r : R, Refuted (P := P) (W := W) X.stmt r

/-- **`Actuated`** — every refutation certificate that EXISTS is actually OBSERVED within the window.

⚑ This is the load-bearing assumption and it is **neither cryptographic nor epistemic**. `Frame`
carries no time, no scheduling and no message delivery, so this proposition cannot even be stated in
the epistemic layer, let alone discharged there. It is a synchrony/liveness assumption about the
deployment, and it is carried explicitly here — in the style of the apex's `hfri` — so that no
consumer can mistake it for something proved. §4 shows it is not removable. -/
def Actuated (X : Claim P) (observed : R → Prop) : Prop :=
  ∀ r : R, Refuted (P := P) (W := W) X.stmt r → observed r

/-- **`optimistic_gives_double_negation` — THE CONSTRUCTIVE CORE, and it is exactly `¬¬`.**

Under both obligations, an unrefuted claim is **not-not** upheld. This is the whole constructive
content of optimistic settlement, and it costs **no axioms at all** (`#print axioms` reports none).

Everything the scheme actually establishes stops here. The step from `¬¬upheld` to `upheld` is
double-negation elimination — see `optimistic_sound` below. -/
theorem optimistic_gives_double_negation (X : Claim P) (observed : R → Prop)
    (hcomplete : RefutationComplete (P := P) (W := W) (R := R) X)
    (hact : Actuated (P := P) (W := W) X observed)
    (hopt : optimisticallyUpheld (P := P) (W := W) X observed) :
    ¬¬ upheld (P := P) (W := W) X := by
  intro hno
  obtain ⟨r, hr⟩ := hcomplete hno
  exact hopt ⟨r, hact r hr, hr⟩

/-- **`optimistic_sound_of_decided` — constructive WHEN the verdict is decided.** If the claim's
status is settled one way or the other, no classical principle is needed: the `¬¬` collapses.
Axiom-free. This isolates precisely what `optimistic_sound` is buying with `Classical.choice`. -/
theorem optimistic_sound_of_decided (X : Claim P) (observed : R → Prop)
    (hdec : upheld (P := P) (W := W) X ∨ ¬ upheld (P := P) (W := W) X)
    (hcomplete : RefutationComplete (P := P) (W := W) (R := R) X)
    (hact : Actuated (P := P) (W := W) X observed)
    (hopt : optimisticallyUpheld (P := P) (W := W) X observed) :
    upheld (P := P) (W := W) X :=
  hdec.elim id (fun hno =>
    absurd hno (optimistic_gives_double_negation (W := W) X observed hcomplete hact hopt))

/-- **`optimistic_sound` — the costly half, with both obligations visible in the type.**

⚑ **THIS IS THE ONE THEOREM IN THE MODULE THAT USES `Classical.choice`, AND THAT IS NOT AN ARTIFACT
OF HOW IT IS PROVED.** `upheld_optimisticallyUpheld` (the honest-prover direction) is axiom-free;
so are the §4 counterexample and the §5 separation. The classical step appears *here* and only here,
because *"nothing refuted it, therefore it holds"* **is double-negation elimination**. The
constructive core stops at `optimistic_gives_double_negation`; `Holds` is `∃ w : W, Discharged …`,
an existential over an arbitrary witness type, so it is not decidable in general and the collapse
cannot be earned back (`optimistic_sound_of_decided` shows exactly what would earn it).

So the induction/coinduction reading has a proof-theoretic twin, and the kernel checks it: a validity
proof is constructive; **an optimistic verdict is classical reasoning, deployed.** That is a precise,
machine-checked statement of what the polarity swap costs — and it is emphatically NOT a security
claim. `Classical.choice` is not an adversary; nobody steals a wallet with Hilbert choice. It is a
DIAGNOSTIC: its appearance in exactly one of these theorems tells you which regime you are in. -/
theorem optimistic_sound (X : Claim P) (observed : R → Prop)
    (hcomplete : RefutationComplete (P := P) (W := W) (R := R) X)
    (hact : Actuated (P := P) (W := W) X observed)
    (hopt : optimisticallyUpheld (P := P) (W := W) X observed) :
    upheld (P := P) (W := W) X :=
  optimistic_sound_of_decided (W := W) X observed
    (Classical.em _) hcomplete hact hopt

/-- **`optimistic_iff` — the full characterisation under both obligations.** -/
theorem optimistic_iff (X : Claim P) (observed : R → Prop)
    (hcomplete : RefutationComplete (P := P) (W := W) (R := R) X)
    (hact : Actuated (P := P) (W := W) X observed) :
    optimisticallyUpheld (P := P) (W := W) X observed ↔ upheld (P := P) (W := W) X :=
  ⟨optimistic_sound (W := W) X observed hcomplete hact,
   upheld_optimisticallyUpheld (W := W) X observed⟩

/-! # §3b. THE THIRD GAP — findability, and the fact that it does NOT rescue the logic

There are **three** distinct gaps between *"a refutation exists"* and *"the chain sees one"*, and §3
models only the outer two:

1. **existence** — `RefutationComplete`, a bare `∃ r, Refuted`. It may be a *classical* existential:
   true, with no algorithm attached.
2. **findability** — someone can actually COMPUTE the certificate. Modelled here.
3. **delivery** — `Actuated`. It reaches the chain inside the window.

Gap 2 is where a classically-proved `RefutationComplete` would bite hardest, and the bite is not a
security failure but a VACUITY: the safety argument goes through while nobody can construct the
challenge it promises. `Dregg2.Laws` already has exactly the right shape on the positive side
(`Searchable`, an `Option`-valued untrusted plugin with no soundness field); this section supplies the
dual, and then records the negative result that closing gap 2 does NOT buy back the constructivity
that §3 lost. -/

/-- The **untrusted refutation searcher** — dual of `Dregg2.Laws.Searchable`, and deliberately
carrying **no soundness field**, for exactly the reason `Searchable` carries none: an adversarial or
broken searcher must remain a legal instance. Soundness is recovered by RE-CHECKING with `Refutes`,
never by trusting `findRefutation`. -/
class RefutationSearchable (P : Type u) (W : Type u) (R : Type u)
    [Verifiable P W] [Refutable P W R] where
  /-- Try to produce a refutation certificate. No completeness or termination promise. -/
  findRefutation : P → Option R

/-- **`searched_refutation_sound_when_checked` — the search result is irrelevant; the CHECK is
everything.** Note that `_hfound` is unused in the proof, and that is the content of the lemma: no
property of the searcher is needed, because the consumer re-`Refutes` whatever came back. This is the
`Searchable` discipline transported to the negative side. -/
theorem searched_refutation_sound_when_checked [RefutationSearchable P W R]
    (p : P) (r : R)
    (_hfound : RefutationSearchable.findRefutation (P := P) (W := W) (R := R) p = some r)
    (hchecked : Refuted (P := P) (W := W) p r) :
    ¬ ∃ w : W, Discharged (P := P) (W := W) p w :=
  Refutable.refutes_sound (W := W) p r hchecked

/-- **`RefutationEffective`** — constructive completeness: an actual FUNCTION producing the
certificate, not a bare existential. This is `Type`-valued because it is DATA. It is what an optimistic
scheme actually needs from its refutation system, and what a classical `RefutationComplete` proof does
not supply. -/
def RefutationEffective (X : Claim P) : Type u :=
  ¬ upheld (P := P) (W := W) X → {r : R // Refuted (P := P) (W := W) X.stmt r}

/-- Effectiveness implies existence. **One way only** — the converse is exactly the gap. -/
def refutationEffective_imp_complete (X : Claim P)
    (h : RefutationEffective (P := P) (W := W) (R := R) X) :
    RefutationComplete (P := P) (W := W) (R := R) X :=
  fun hno => ⟨(h hno).1, (h hno).2⟩

/-- **`optimistic_dne_effective` — closing gap 2 leaves the constructive core exactly where it was.**
With a genuine refutation ALGORITHM, an unrefuted claim is still only `¬¬upheld`, and this is still
axiom-free. Findability was never what the collapse needed. -/
theorem optimistic_dne_effective (X : Claim P) (observed : R → Prop)
    (heff : RefutationEffective (P := P) (W := W) (R := R) X)
    (hact : Actuated (P := P) (W := W) X observed)
    (hopt : optimisticallyUpheld (P := P) (W := W) X observed) :
    ¬¬ upheld (P := P) (W := W) X :=
  optimistic_gives_double_negation (W := W) X observed
    (refutationEffective_imp_complete (W := W) X heff) hact hopt

/-- **`optimistic_sound_effective` — and the collapse is STILL classical.**

⚑ THE NEGATIVE RESULT, and it is the point of §3b: an effective refuter does NOT restore
constructivity. The reason is structural, not incidental — `RefutationEffective` is a function OF
`¬ upheld X`, and the scheme never has `¬ upheld X`; it only ever has `¬¬ upheld X`. So the algorithm
can never be RUN by the soundness argument, however constructive the algorithm itself is.

Read `#print axioms` on this and on `optimistic_dne_effective` together: the three gaps are
INDEPENDENT. Closing findability buys a usable challenger and buys nothing logically. -/
theorem optimistic_sound_effective (X : Claim P) (observed : R → Prop)
    (heff : RefutationEffective (P := P) (W := W) (R := R) X)
    (hact : Actuated (P := P) (W := W) X observed)
    (hopt : optimisticallyUpheld (P := P) (W := W) X observed) :
    upheld (P := P) (W := W) X :=
  optimistic_sound (W := W) X observed
    (refutationEffective_imp_complete (W := W) X heff) hact hopt

/-! # §4. PROVING THE FLOOR FALSE — `Actuated` is not removable

`feedback-prove-the-floor-false`: a floor must be SATISFIABLE and REFUTABLE but not PROVABLE. §3 shows
it is satisfiable. This section refutes it: a fully-inhabited instance in which the optimistic verdict
UPHOLDS a claim that does not hold, purely because nothing was observed. Refutation-completeness even
HOLDS here — the certificate exists and is sound. The only failure is that it was never delivered. -/

namespace Silence

/-- Statements: a single trivial statement. -/
abbrev Stmt := Unit

/-- Witnesses: **none**. `Holds` is therefore uninhabited — the claim is FALSE. -/
abbrev Wit := Empty

/-- Refutation certificates: one, and it is sound (vacuously, since `Wit` is empty). -/
abbrev Cert := Unit

instance : Verifiable Stmt Wit where
  Verify := fun _ w => Empty.elim w

instance : Refutable Stmt Wit Cert where
  Refutes := fun _ _ => true
  refutes_sound := by rintro _ _ _ ⟨w, -⟩; exact Empty.elim w

/-- The claim under dispute. -/
def X : Claim Stmt := ⟨()⟩

/-- **Nothing is observed** — the challenge window closes with no certificate delivered. This is the
whole of the counterexample: the certificate EXISTS, it is SOUND, and it is not SEEN. -/
def observedNothing : Cert → Prop := fun _ => False

/-- The claim genuinely does NOT hold: there is no witness at all. -/
theorem X_not_upheld : ¬ upheld (P := Stmt) (W := Wit) X := by
  rintro ⟨w, -⟩; exact Empty.elim w

/-- Refutation-completeness DOES hold here — the sound certificate exists. So the counterexample is
not smuggled in through an inexpressive refutation language. -/
theorem X_refutation_complete :
    RefutationComplete (P := Stmt) (W := Wit) (R := Cert) X := fun _ => ⟨(), rfl⟩

/-- Yet the optimistic verdict UPHOLDS it, because nothing was observed. -/
theorem X_optimistically_upheld :
    optimisticallyUpheld (P := Stmt) (W := Wit) X observedNothing := by
  intro h
  obtain ⟨_, hobs, _⟩ := h
  exact hobs

/-- **`optimistic_unsound_without_actuation` — THE FLOOR IS FALSE WITHOUT `Actuated`.**
Optimistic upholding, refutation-completeness, and the claim's genuine FAILURE hold simultaneously.
So `optimistic_sound` cannot be strengthened by dropping `hact`: silence is not evidence, and the
liveness assumption is doing real work rather than decorating the statement. -/
theorem optimistic_unsound_without_actuation :
    optimisticallyUpheld (P := Stmt) (W := Wit) X observedNothing
      ∧ RefutationComplete (P := Stmt) (W := Wit) (R := Cert) X
      ∧ ¬ upheld (P := Stmt) (W := Wit) X :=
  ⟨X_optimistically_upheld, X_refutation_complete, X_not_upheld⟩

/-- And `Actuated` is exactly what fails in this instance — pinning the blame precisely. -/
theorem actuation_is_what_fails :
    ¬ Actuated (P := Stmt) (W := Wit) X observedNothing := fun h => h () rfl

/-! ## §4b. …and the floor is SATISFIABLE — the SAME instance, with only `observed` changed

`feedback-prove-the-floor-false` demands both halves: a floor must be REFUTABLE (§4) **and**
SATISFIABLE, or `optimistic_sound` could be green because its hypotheses are jointly unsatisfiable.
Everything below is the identical instance; the only thing that moves is what the window observes. -/

/-- **Everything is observed** — the challenge window actually delivers. -/
def observedAll : Cert → Prop := fun _ => True

/-- Now `Actuated` holds. -/
theorem actuated_when_delivered : Actuated (P := Stmt) (W := Wit) X observedAll :=
  fun _ _ => trivial

/-- **The verdict BITES: with actuation the same false claim is correctly REJECTED.** In §4 silence
upheld it; here the certificate lands and the optimistic verdict fails, matching `upheld`. So
`optimistic_sound` is not vacuously green — its hypotheses are jointly satisfiable and the conclusion
tracks the realizability fact. -/
theorem optimistic_verdict_bites :
    ¬ optimisticallyUpheld (P := Stmt) (W := Wit) X observedAll := by
  intro h
  exact h ⟨(), trivial, rfl⟩

/-- **`floor_is_satisfiable_and_refutable`** — the two halves side by side, over ONE instance whose
only varying input is the observation set. Actuation is exactly the hinge: with it the verdict tracks
truth, without it the verdict is silence. -/
theorem floor_is_satisfiable_and_refutable :
    (Actuated (P := Stmt) (W := Wit) X observedAll
      ∧ ¬ optimisticallyUpheld (P := Stmt) (W := Wit) X observedAll)
    ∧ (¬ Actuated (P := Stmt) (W := Wit) X observedNothing
      ∧ optimisticallyUpheld (P := Stmt) (W := Wit) X observedNothing) :=
  ⟨⟨actuated_when_delivered, optimistic_verdict_bites⟩,
   ⟨actuation_is_what_fails, X_optimistically_upheld⟩⟩

end Silence

/-! # §5. The challenger-strength gap — `DistKnows Honest` does not give you a challenger

The natural epistemic reading of the naysayer safety obligation is the dual of
`no_dist_knowledge_of_unrealizable`: *"if the claim is false, the honest group DISTRIBUTEDLY KNOWS a
refutation"* — `F.DistKnows F.Honest`. This section proves that reading is **too weak to be useful**.

Distributed knowledge is the group's POOLED perspective; it may be held by no individual. A challenger
in an optimistic scheme must be a single agent who can act. So the obligation an optimistic settlement
actually needs is `∃ i, F.Honest i ∧ F.Knows i`, and `knows_imp_distKnows` runs only in the unhelpful
direction. The frame below separates them with every agent HONEST, so the gap is not an artifact of
Byzantine agents — it is intrinsic to the modality. -/

namespace ChallengerGap

/-- Two honest agents with orthogonal views. Worlds are pairs; agent `true` sees only the first
component, agent `false` only the second; the actual world is `(true, true)`. Nobody is Byzantine. -/
def CF : Frame (Bool × Bool) Bool where
  actual := (true, true)
  Indist := fun i w w' => if i then w.1 = w'.1 else w.2 = w'.2
  indist_refl := by intro i w; cases i <;> simp
  Alive := fun _ _ => True
  Faulty := fun _ => False

/-- The proposition to be known: *"the actual world is exactly `(true, true)`"* — the shape of "a
refutation certificate for this exact claim is available". -/
def φ : Frame.Prop' (Bool × Bool) := fun w => w = (true, true)

/-- Every agent is honest in this frame — the gap below is NOT caused by Byzantine faults. -/
theorem all_honest (i : Bool) : CF.Honest i := fun h => h

/-- **The honest group DOES distributedly know `φ`.** Pooling the two views pins both components. -/
theorem honest_group_distKnows : CF.DistKnows CF.Honest φ CF.actual := by
  intro w' hall
  have h1 : w'.1 = true := by
    have := hall true (all_honest true)
    simpa [CF, Frame.Indist] using this
  have h2 : w'.2 = true := by
    have := hall false (all_honest false)
    simpa [CF, Frame.Indist] using this
  show w' = (true, true)
  exact Prod.ext h1 h2

/-- **But NO single honest agent knows it.** Each agent is blind to the other component, so each can
confuse the actual world with one where `φ` fails. -/
theorem no_single_honest_agent_knows : ¬ ∃ i, CF.Honest i ∧ CF.Knows i φ CF.actual := by
  rintro ⟨i, -, hk⟩
  cases i with
  | true =>
      -- agent `true` cannot rule out `(true, false)`.
      have : φ (true, false) := hk (true, false) (by simp [CF])
      simp [φ] at this
  | false =>
      -- agent `false` cannot rule out `(false, true)`.
      have : φ (false, true) := hk (false, true) (by simp [CF])
      simp [φ] at this

/-- **`distKnows_honest_does_not_give_a_challenger`** — the two hold together, with every agent honest.

Consequence for optimistic settlement: an obligation phrased as `DistKnows F.Honest (refutation)` is
satisfiable in worlds where **no one can actually file the challenge**. The correct obligation is the
strictly stronger `∃ i, Honest i ∧ Knows i`, and any design document that states the group version has
understated what it needs. -/
theorem distKnows_honest_does_not_give_a_challenger :
    CF.DistKnows CF.Honest φ CF.actual ∧ ¬ ∃ i, CF.Honest i ∧ CF.Knows i φ CF.actual :=
  ⟨honest_group_distKnows, no_single_honest_agent_knows⟩

end ChallengerGap

end Metatheory.OptimisticAdjudication

#assert_axioms Metatheory.OptimisticAdjudication.upheld_optimisticallyUpheld
#assert_axioms Metatheory.OptimisticAdjudication.optimistic_gives_double_negation
#assert_axioms Metatheory.OptimisticAdjudication.optimistic_sound_of_decided
#assert_axioms Metatheory.OptimisticAdjudication.optimistic_sound
#assert_axioms Metatheory.OptimisticAdjudication.optimistic_iff
#assert_axioms Metatheory.OptimisticAdjudication.Silence.optimistic_unsound_without_actuation
#assert_axioms Metatheory.OptimisticAdjudication.Silence.actuation_is_what_fails
#assert_axioms Metatheory.OptimisticAdjudication.Silence.optimistic_verdict_bites
#assert_axioms Metatheory.OptimisticAdjudication.Silence.floor_is_satisfiable_and_refutable
#assert_axioms Metatheory.OptimisticAdjudication.ChallengerGap.distKnows_honest_does_not_give_a_challenger
