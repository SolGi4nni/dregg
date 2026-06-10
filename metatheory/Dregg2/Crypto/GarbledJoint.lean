/-
# Dregg2.Crypto.GarbledJoint — the two-party private joint-predicate gate (§8 privacy floor).

Two cells transition together (the proven-atomic JOINT TURN of `Distributed/EntangledJoint.lean`),
their admission gated by a predicate `P(a, b)` over BOTH cells' *private* state — and only the
OUTCOME of that predicate is revealed, neither party's input. This is private bilateral settlement:
two parties compute a joint condition, each keeping their input private, learning only whether the
condition held. It is the bottom rung of the DREGG3 §8 privacy ladder (the secure-two-party-
computation primitive that the joint turn admits against).

This is the LEAN SPEC that the Rust garbled-circuit machinery (`circuit/src/garbled.rs`,
`circuit/src/dsl/garbled.rs`, `circuit/src/garbled_air.rs`) must meet. That machinery implements
Yao's garbled circuits with Poseidon2 as the garbling hash: a garbler wires one party's secret into
custom truth tables, the evaluator obtains its input labels (via oblivious transfer, modeled here as
a parameter) and decrypts the circuit gate-by-gate, learning ONLY the output label — pass or fail.
The garbled tables are random pads (the `test_prover_cannot_learn_threshold` property): a different
secret produces an indistinguishable circuit, which is exactly the input-privacy carrier below.

We model the two guarantees a 2PC kernel must carry:

* `garbled_correct`   — the evaluation yields exactly `P(a, b)` (Yao correctness);
* `garbled_input_private` — the evaluator's transcript is *simulatable from the output bit alone*:
  it reveals nothing about either party's input beyond `P(a, b)` (Yao obliviousness / privacy).

Then `joint_turn_private_gate` welds it to the JOINT TURN: a joint turn whose admission gate IS a
`GarbledKernel`-evaluated predicate over both cells' private state commits IFF `P(a, b)` holds, and
the gate's transcript leaks only that one bit — the joint turn never sees either private input.

DISCIPLINE: candidate-independent carriers (abstract `Prop`s, never `True`-aliases on the load-
bearing path); the dial floor is `acceptanceOnly` (the verifier learns one bit). Non-vacuity is a
reference kernel that FIRES the cascade (a real `>=` predicate admitting one `(a,b)` and rejecting
another) with input-privacy stated, and an ANTI carrier that FALSIFIES privacy when the simulator is
allowed to peek (so the carrier is not vacuously `True`).
-/
import Dregg2.Distributed.EntangledJoint
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.GarbledJoint

open Dregg2.Exec Dregg2.Distributed.EntangledJoint Metatheory

universe u

/-! ## 1. The 2PC kernel — garble / evaluate, with correctness + privacy as Prop carriers.

A `GarbledKernel` over private-state types `A` (party-a, the "garbler"/threshold holder) and `B`
(party-b, the "evaluator"/value holder) models the secure evaluation of a fixed joint predicate
`P : A → B → Bool`. The `garble`/`eval` interface mirrors `garble_comparison_circuit` /
`evaluate_garbled_circuit`; the `transcript` is what the evaluator observes during evaluation (the
garbled tables + decrypted labels — everything a real-world adversary in party-b's seat sees). -/

/-- **`GarbledKernel`** — a two-party secure-evaluation kernel for a fixed joint predicate `P`.

* `Garbled`    — the garbled-circuit artifact party-a hands to party-b (the random tables);
* `Transcript` — what party-b observes while evaluating (its complete view);
* `garble`     — party-a garbles `P` with its private input `a` wired in;
* `eval`       — party-b evaluates with its private input `b`, producing `(bit, transcript)`;
* `correct`    — Yao CORRECTNESS: the bit equals `P a b` (carrier, never assumed `True` on the path);
* `simulator`  — a function producing a transcript FROM THE OUTPUT BIT ALONE (no access to `a`/`b`);
* `private`    — Yao PRIVACY: the real transcript equals the simulator's — party-b's view is a
  function of the output bit only, so it leaks nothing about either input beyond `P a b`.
-/
structure GarbledKernel (A B : Type u) where
  /-- The joint predicate the two parties evaluate (e.g. `a ≥ b`, `a ∧ b`, settlement-admissible). -/
  P : A → B → Bool
  /-- The garbled artifact party-a sends to party-b (random Poseidon2 tables in the Rust impl). -/
  Garbled : Type u
  /-- What party-b observes during evaluation — its COMPLETE view of the protocol. -/
  Transcript : Type u
  /-- Party-a garbles `P` with its private `a` wired in. -/
  garble : A → Garbled
  /-- Party-b evaluates with its private `b`; yields the output bit and its observed transcript. -/
  eval : Garbled → B → Bool × Transcript
  /-- **CORRECTNESS carrier:** the evaluated bit IS `P a b`. -/
  correct : ∀ a b, (eval (garble a) b).1 = P a b
  /-- A simulator that fabricates a transcript from the OUTPUT BIT ALONE — no input access. -/
  simulator : Bool → Transcript
  /-- **PRIVACY carrier (obliviousness):** the real transcript equals what a bit-only simulator
  produces, so party-b's view is a function of `P a b` alone — neither input leaks beyond the bit. -/
  private_sim : ∀ a b, (eval (garble a) b).2 = simulator ((eval (garble a) b).1)

variable {A B : Type u}

/-! ## 2. Correctness + input-privacy, as standalone theorems off the carriers. -/

/-- **`garbled_correct` — the evaluation yields `P(a, b)` (from the kernel's carrier).** The output
bit party-b learns is exactly the joint predicate over the two private inputs — Yao correctness. -/
theorem garbled_correct (K : GarbledKernel A B) (a : A) (b : B) :
    (K.eval (K.garble a) b).1 = K.P a b :=
  K.correct a b

/-- **`garbled_input_private` — neither input is revealed beyond the output bit (PROVED off the
carrier).** Party-b's transcript is exactly `simulator (P a b)`: a function of the OUTPUT BIT ALONE.
So two scenarios with the SAME outcome produce IDENTICAL transcripts — party-b (and any observer in
its seat) cannot distinguish them, hence learns nothing about either private input beyond `P a b`.
This is the obliviousness/zero-knowledge statement for the 2PC gate. -/
theorem garbled_input_private (K : GarbledKernel A B) (a : A) (b : B) :
    (K.eval (K.garble a) b).2 = K.simulator (K.P a b) := by
  rw [K.private_sim a b, K.correct a b]

/-- **`garbled_input_private_indistinguishable` — same-outcome ⇒ same-transcript (PROVED).** If two
input pairs `(a₁,b₁)` and `(a₂,b₂)` agree on the predicate's outcome, party-b's transcript is
IDENTICAL across them. This is the sharpest privacy tooth: a different secret with the same result is
unobservable — exactly `test_prover_cannot_learn_threshold`. -/
theorem garbled_input_private_indistinguishable (K : GarbledKernel A B)
    (a₁ a₂ : A) (b₁ b₂ : B) (hsame : K.P a₁ b₁ = K.P a₂ b₂) :
    (K.eval (K.garble a₁) b₁).2 = (K.eval (K.garble a₂) b₂).2 := by
  rw [garbled_input_private, garbled_input_private, hsame]

/-! ## 3. The §8 dial floor — the 2PC gate discloses at `acceptanceOnly` (one bit).

A garbled-circuit private predicate sits at the BOTTOM of the epistemic dial: the verifier (and the
counterparty) learns one bit — *the joint condition held* — and nothing else. Same floor as Merkle
membership (`PredicateKernel.merkleKindObligation`) and `BlindedSet`. -/

/-- The disclosure floor of any garbled 2PC gate: `acceptanceOnly` — only the outcome bit is
revealed. (`Metatheory.Dial`; `acceptanceOnly` is the `⊥` notch of the dial.) -/
def garbledDialFloor : Dial := Dial.acceptanceOnly

@[simp] theorem garbledDialFloor_eq : garbledDialFloor = Dial.acceptanceOnly := rfl

/-- The floor is the dial's BOTTOM — formally `acceptanceOnly = ⊥` (the zero-knowledge notch). -/
theorem garbledDialFloor_is_bot : garbledDialFloor = (⊥ : Dial) := rfl

/-! ## 4. The JOINT TURN private gate — admission over BOTH cells' private state.

Wire the kernel onto `EntangledJoint`. A `PrivateJointGate` couples a `JointTurn` with the two
cells' private states `a`, `b` and a `GarbledKernel` whose predicate gates admission. The joint turn
ADMITS (its all-or-none fold may run) iff `P a b` — and the admission gate's transcript reveals only
that bit. The atomicity / conservation / no-amplification of the admitted turn are inherited verbatim
from `EntangledJoint`; this layer adds the *private bilateral condition* on top. -/

/-- **`PrivateJointGate`** — a two-party joint turn admitted by a private predicate over both cells'
secret state. `a`/`b` are the two cells' private inputs; `K` the 2PC kernel; `jt` the joint turn the
gate guards (the proven-atomic tensor of the two cells). -/
structure PrivateJointGate (A B : Type u) where
  /-- The proven-atomic joint turn this gate guards. -/
  jt : JointTurn
  /-- Party-a's (first cell's) private state. -/
  a  : A
  /-- Party-b's (second cell's) private state. -/
  b  : B
  /-- The 2PC kernel whose predicate decides admission. -/
  K  : GarbledKernel A B

/-- Whether the private gate ADMITS — the joint condition `P a b` evaluated through the garbled
circuit (the bit party-b decrypts). By construction this is the gate's only observable. -/
def PrivateJointGate.admits (g : PrivateJointGate A B) : Bool :=
  (g.K.eval (g.K.garble g.a) g.b).1

/-- The transcript the gate exposes to party-b during admission — its complete observable view. -/
def PrivateJointGate.transcript (g : PrivateJointGate A B) : g.K.Transcript :=
  (g.K.eval (g.K.garble g.a) g.b).2

/-- **`joint_turn_private_gate` — THE WELD (PROVED).** For a joint turn guarded by a `GarbledKernel`
predicate over both cells' private state:

1. **admission ⇔ the joint condition:** the gate admits IFF `P a b` holds — the two cells transition
   together exactly when their joint private condition is met;
2. **output-only disclosure:** the gate's entire transcript is `simulator (P a b)` — a function of
   the ONE admission bit, so neither cell's private input leaks beyond the outcome;
3. **atomicity is inherited:** IF the guarded joint turn additionally commits over the machine, every
   leg committed atomically (all-or-none) — the `EntangledJoint` keystone, unchanged.

The private gate adds a bilateral secret condition WITHOUT widening disclosure past one bit, and
WITHOUT weakening the joint turn's atomicity. -/
theorem joint_turn_private_gate (g : PrivateJointGate A B) :
    -- (1) admission ⇔ the joint private condition
    (g.admits = true ↔ g.K.P g.a g.b = true)
    -- (2) output-only disclosure: the transcript is a function of the admission bit ALONE
    ∧ g.transcript = g.K.simulator (g.K.P g.a g.b)
    -- (3) inherited atomicity for the guarded turn, IF it commits over the machine
    ∧ (∀ k k' : RecordKernelState, jointApplyAll k g.jt.legs = some k' →
        ∀ l ∈ g.jt.legs, ∃ ka kb, applyLeg ka l = some kb) := by
  refine ⟨?_, ?_, ?_⟩
  · -- admits = (eval …).1 = P a b by correctness
    unfold PrivateJointGate.admits
    rw [garbled_correct]
  · -- transcript = simulator (P a b) by privacy
    unfold PrivateJointGate.transcript
    exact garbled_input_private g.K g.a g.b
  · -- atomicity straight from EntangledJoint
    intro k k' h l hmem
    exact jointApplyAll_atomic g.jt.legs k k' h l hmem

/-- **`private_gate_reveals_only_outcome` — the ANTI-GHOST privacy tooth (PROVED).** Under a FIXED
garbled scheme `K`, two private input pairs `(a₁,b₁)` and `(a₂,b₂)` that reach the SAME admission
outcome expose IDENTICAL transcripts — even with entirely different private inputs. An observer in
party-b's seat cannot tell which secret pair produced an admission: the only thing the gate discloses
is the outcome bit. (Stated over one `K` so the `Transcript` type is shared — the realistic "two
runs of the same private gate" scenario.) -/
theorem private_gate_reveals_only_outcome
    (K : GarbledKernel A B) (a₁ a₂ : A) (b₁ b₂ : B)
    (hsame : K.P a₁ b₁ = K.P a₂ b₂) :
    (K.eval (K.garble a₁) b₁).2 = (K.eval (K.garble a₂) b₂).2 :=
  garbled_input_private_indistinguishable K a₁ a₂ b₁ b₂ hsame

/-! ## 5. NON-VACUITY — a reference kernel that FIRES the cascade (and an ANTI that BREAKS privacy).

The reference 2PC kernel is the `a ≥ b` comparison `circuit/src/garbled.rs` actually garbles
(party-a's threshold `a`, party-b's value `b`; admit iff `b ≥ a`). Its transcript is modeled as the
single output bit (what `evaluate_garbled_circuit` ultimately yields a verifier), with the simulator
the identity on that bit — so the privacy carrier HOLDS and is witnessed true. The predicate ADMITS
for one `(a,b)` and REJECTS another (the non-vacuity teeth). -/

namespace Reference

/-- The reference predicate: party-b's value meets party-a's threshold (`b ≥ a`), the exact
condition `garble_comparison_circuit` wires in. -/
def geKernel : GarbledKernel ℕ ℕ where
  P := fun a b => decide (a ≤ b)
  Garbled := ℕ                       -- party-a's wired threshold (random tables abstracted away)
  Transcript := Bool                 -- party-b observes ONLY the output bit (the §8 floor)
  garble := fun a => a
  eval := fun a b => (decide (a ≤ b), decide (a ≤ b))
  correct := fun _ _ => rfl
  simulator := fun bit => bit        -- the transcript IS the bit: nothing more is observed
  private_sim := fun _ _ => rfl

/-- Non-vacuity (CORRECTNESS): the reference kernel admits `b = 150 ≥ a = 100` — `P` fires true. -/
example : geKernel.P 100 150 = true := by decide

/-- Non-vacuity (REJECTION tooth): the reference kernel rejects `b = 50 < a = 100` — `P` fires
false. So the carrier is not vacuously-admitting; the gate genuinely discriminates. -/
example : geKernel.P 100 50 = false := by decide

/-- Non-vacuity (CORRECTNESS welded): evaluation yields exactly `P a b`. -/
example : (geKernel.eval (geKernel.garble 100) 150).1 = geKernel.P 100 150 :=
  garbled_correct geKernel 100 150

/-- Non-vacuity (PRIVACY HOLDS): the transcript is a function of the output bit alone — two DIFFERENT
threshold/value pairs with the SAME outcome (`100≤150` and `7≤9`, both admit) expose the SAME
transcript. The privacy carrier is witnessed TRUE, not assumed. -/
example : (geKernel.eval (geKernel.garble 100) 150).2
        = (geKernel.eval (geKernel.garble 7) 9).2 :=
  garbled_input_private_indistinguishable geKernel 100 7 150 9 (by decide)

/-- A reference private joint gate over the 3-cell ring of `EntangledJoint`, admitted by `b ≥ a`. -/
def refGate : PrivateJointGate ℕ ℕ :=
  { jt := ringJoint, a := 100, b := 150, K := geKernel }

/-- Non-vacuity (THE WELD fires): the reference gate ADMITS iff its joint private condition holds,
discloses only the outcome bit, and the guarded ring turn is atomic. -/
example :
    (refGate.admits = true ↔ refGate.K.P refGate.a refGate.b = true)
    ∧ refGate.transcript = refGate.K.simulator (refGate.K.P refGate.a refGate.b)
    ∧ (∀ k k' : RecordKernelState, jointApplyAll k refGate.jt.legs = some k' →
        ∀ l ∈ refGate.jt.legs, ∃ ka kb, applyLeg ka l = some kb) :=
  joint_turn_private_gate refGate

/-- The reference gate ADMITS (150 ≥ 100). -/
example : refGate.admits = true := by decide

/-- A non-admitting reference gate (`b = 50 < a = 100`) — the joint condition fails, so the private
turn would NOT admit. The gate discriminates on the secret condition. -/
def refGateReject : PrivateJointGate ℕ ℕ :=
  { jt := ringJoint, a := 100, b := 50, K := geKernel }

example : refGateReject.admits = false := by decide

/-- The dial floor of the reference gate is `acceptanceOnly` — one bit disclosed. -/
example : garbledDialFloor = Dial.acceptanceOnly := rfl

/-! ### The ANTI carrier — a kernel whose "simulator" PEEKS at the input ⇒ privacy is FALSE.

To prove the privacy carrier is load-bearing (not vacuously `True`), here is a would-be kernel whose
transcript leaks party-b's input. It CANNOT satisfy `private_sim` with a bit-only simulator: we
exhibit two same-outcome inputs whose transcripts DIFFER, refuting the indistinguishability the real
kernel enjoys. This is why `private_sim` is a genuine obligation. -/

/-- A LEAKY evaluation: the "transcript" is party-b's raw input `b`. -/
def leakyEval (_a b : ℕ) : Bool × ℕ := (decide (_a ≤ b), b)

/-- The leak is observable: two inputs with the SAME outcome (`100≤150` and `100≤200`, both admit)
produce DIFFERENT transcripts (`150 ≠ 200`). No bit-only simulator can reproduce both — so a kernel
built on `leakyEval` FAILS `private_sim`. The privacy carrier is therefore non-vacuous. -/
example : (leakyEval 100 150).1 = (leakyEval 100 200).1 ∧ (leakyEval 100 150).2 ≠ (leakyEval 100 200).2 :=
  ⟨by decide, by decide⟩

end Reference

/-! ## 6. Axiom-hygiene tripwires (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms garbled_correct
#assert_axioms garbled_input_private
#assert_axioms garbled_input_private_indistinguishable
#assert_axioms joint_turn_private_gate
#assert_axioms private_gate_reveals_only_outcome

end Dregg2.Crypto.GarbledJoint
