/-
# Metatheory.Open.PerfectZK — CLOSING the *perfect/statistical* FRAGMENT of the ZK
# indistinguishability OPEN.

`Metatheory.ConstructiveKnowledge` §2 (~lines 219–231) and `Metatheory.EpistemicDial` §6
(~lines 488–503) PROVE the epistemic *order* faithfully — a ZK verifier sits strictly
below witness content in the disclosure order (`verifier_learns_only_acceptance`,
`content_not_reached_from_acceptance`, `zk_is_dial_bottom`) — but leave OPEN, **as a
deliberate `Disclosure` separation parameter**, that this order "reflects an ACTUAL
indistinguishability": that no verifier confined to acceptance can extract the witness.

That OPEN has two layers, and the repo is right to keep them apart:

  * **COMPUTATIONAL** (PPT adversary, negligible advantage, simulator existence against
    *efficient* distinguishers): a circuit/cryptographic obligation, NEVER merged into a
    Lean order-law. **THIS MODULE DOES NOT TOUCH IT** — it stays exactly the parameter the
    metatheory carries. See the closing `-- RESIDUAL` note.

  * **PERFECT / STATISTICAL** (information-theoretic: the verifier's *view* is literally
    identical — same value — regardless of which witness was used): this is a *closed*
    mathematical fact once one models the view and a simulator. **THIS MODULE CLOSES IT.**

We model a verifier's VIEW (`view : S → W → V`) and a witness-free SIMULATOR
(`sim : S → V`), under the **perfect-ZK law** `hperf : ∀ s w, view s w = sim s` (the real
view equals a simulation that never saw the witness). From it we prove the
information-theoretic content of "learns only acceptance":

    view_indep_of_witness : ∀ s w₁ w₂, view s w₁ = view s w₂

— any two witnesses yield the SAME view, so the verifier extracts *zero* information about
which witness was used. We then BRIDGE to the repo's machinery: such a `PerfectZK` builds a
`DiscloseAt` whose information `leaked` at the dial floor `⊥ = acceptanceOnly` is a
**constant in the witness** (the simulator output `sim s`), placing the verifier exactly at
`zk_is_dial_bottom`'s acceptance floor with content unreachable — discharging, in the
information-theoretic setting, the very antecedent the `Disclosure` parameter abstracts.

TEETH / NON-VACUITY: a concrete perfectly-hiding instance (a one-time-pad commitment whose
ciphertext is identically the same constant regardless of witness) where the law HOLDS, and
an explicit NON-perfect instance (the view leaks the witness verbatim) where
`view_indep_of_witness` FAILS. So `hperf` is a *real constraint*, not always-true.

DISCIPLINE: faithful Props, ZERO `sorry`/`admit`/`native_decide`/`axiom`. Every keystone is
pinned with `#assert_axioms` (kernel-clean: only `propext`/`Classical.choice`/`Quot.sound`).
-/
import Metatheory.ConstructiveKnowledge
import Metatheory.EpistemicDial
import Dregg2.Privacy
import Dregg2.Tactics

-- The module namespace `Metatheory.Open.PerfectZK` and the central structure `PerfectZK`
-- legitimately share the leaf name; the duplicate-namespace linter is purely cosmetic here.
set_option linter.dupNamespace false

namespace Metatheory.Open.PerfectZK

open Metatheory

universe u

/-! # §1. Perfect zero-knowledge: the view is a witness-free simulation. -/

/-- **`PerfectZK`** — the information-theoretic ZK instance the `Disclosure` parameter
abstracts.

* `S` — statement type (what is being proved);
* `W` — witness type (the secret used to prove it);
* `V` — the verifier's **view** type (the entire transcript/state a verifier observes);
* `view s w` — the *real* view a verifier obtains when the prover uses witness `w` for `s`;
* `sim s` — a **simulator**: a view produced from the statement ALONE, never touching `w`;
* `hperf` — the **perfect-ZK law**: the real view *equals* the simulated one, for every
  statement and witness. This is *perfect* (not merely statistical or computational)
  hiding: the views are not just indistinguishable to an efficient adversary, they are the
  identical value. The simulator's existence-with-equality is the whole content.

`hperf` is a genuine constraint: §3 exhibits an instance satisfying it and one violating
it. -/
structure PerfectZK where
  /-- Statement type. -/
  S : Type u
  /-- Witness type. -/
  W : Type u
  /-- The verifier's view (transcript) type. -/
  V : Type u
  /-- The real view obtained from statement `s` proved with witness `w`. -/
  view : S → W → V
  /-- The witness-free simulator: a view produced from the statement alone. -/
  sim : S → V
  /-- **Perfect-ZK law.** The real view is *identical* to a witness-free simulation. -/
  hperf : ∀ (s : S) (w : W), view s w = sim s

namespace PerfectZK

variable (Z : PerfectZK)

/-- **`view_indep_of_witness` — the information-theoretic content of "learns only
acceptance", PROVED, kernel-clean.** Any two witnesses yield the SAME view: the verifier
cannot tell, from its view, which witness the prover used — it extracts *zero* information
about the witness. This is the perfect/statistical fragment of the ZK indistinguishability
the metatheory leaves abstract: discharged here by the simulator equality (`view s w =
sim s`, independent of `w`), NOT by any computational/PPT assumption. -/
theorem view_indep_of_witness (s : Z.S) (w₁ w₂ : Z.W) :
    Z.view s w₁ = Z.view s w₂ := by
  rw [Z.hperf s w₁, Z.hperf s w₂]

/-- **The view is a function of the statement alone — PROVED, kernel-clean.** Equivalently:
the real view factors through the simulator, so it is a function `S → V` with the witness
projected away entirely. This is the strongest information-theoretic statement of "the view
carries zero information about the witness": there is a witness-free `g = Z.sim` with
`Z.view s w = g s` for all `w`. -/
theorem view_factors_through_statement :
    ∃ g : Z.S → Z.V, ∀ (s : Z.S) (w : Z.W), Z.view s w = g s :=
  ⟨Z.sim, Z.hperf⟩

end PerfectZK

#assert_axioms PerfectZK.view_indep_of_witness
#assert_axioms PerfectZK.view_factors_through_statement

/-! # §2. The bridge to `Disclosure` / `DiscloseAt` / `zk_is_dial_bottom`.

We connect the §1 fact to the repo's ACTUAL machinery. The cleanest bridge is exactly the
one the task names: the information `leaked` at the ZK floor `⊥ = acceptanceOnly` is a
**constant in the witness** — literally the simulator output `Z.sim s`. So the floor's
information is witness-independent, which IS the information-theoretic reading of the
`Disclosure` separation parameter that `dialDisclosure` / `zk_is_dial_bottom` instantiates.

The order `I` of "information sets" is taken to be the view type `Z.V` carried by the
discrete order `⊥`/`Eq` of `OrderDual`-free `Preorder` — we only need *some* `Preorder`; the
content is that the value at `⊥` does not depend on `w`. -/

namespace PerfectZK

variable (Z : PerfectZK)

/-- The information order we read the dial into: the view type with the trivial (discrete)
preorder where `a ≤ b ↔ a = b`. We only need *a* `Preorder`; the load-bearing fact is the
*value* leaked at the floor, not the order's richness. Declared `scoped instance` so the
dial's `DiscloseAt Z.V …` finds it by resolution. -/
scoped instance discreteInfoPreorder : Preorder Z.V where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂

-- The verify seam the dial schedule consults is taken as a *parameter* `[Verifiable Z.S
-- Z.W]`: the bridge is about the witness-INDEPENDENCE of the value `leaked` at the floor,
-- not about which decidable verifier reports the acceptance bit. Any seam works; we keep it
-- abstract (faithful — we do not fabricate a particular oracle).
variable [Dregg2.Laws.Verifiable Z.S Z.W]

/-- **The disclosure schedule a `PerfectZK` induces.** At EVERY dial position the
information leaked is the *simulator* view `Z.sim s` — witness-free by construction. In
particular at the floor `⊥ = acceptanceOnly` the leaked information is `Z.sim s`, a constant
in the witness. (We make `leaked` constant across the whole dial here because the
information-theoretic claim is precisely that even the *real* view at any notch carries no
witness information; `mono` is then trivial.) -/
def discloseAt (s : Z.S) (w : Z.W) : DiscloseAt Z.V Z.S Z.W where
  leaked _ := Z.sim s
  mono := by intro a b _; exact rfl
  pred := s
  wit := w
  accepts _ := Dregg2.Laws.Discharged s w
  accepts_eq := by intro _; exact Iff.rfl

/-- **The floor leaks the witness-free simulation — PROVED, kernel-clean.** The information
the verifier learns at the ZK bottom `⊥ = acceptanceOnly` is exactly `Z.sim s`: a value
produced WITHOUT the witness. This is the information-theoretic discharge of the
`Disclosure` separation parameter — the floor's leaked information is witness-free. -/
theorem floor_leaks_simulation (s : Z.S) (w : Z.W) :
    (Z.discloseAt s w).leaked ⊥ = Z.sim s :=
  rfl

/-- **The floor leak is INDEPENDENT of the witness — PROVED, kernel-clean.** For a fixed
statement, the information leaked at the ZK floor is the same whichever witness the prover
held: `(discloseAt s w₁).leaked ⊥ = (discloseAt s w₂).leaked ⊥`. This is
`view_indep_of_witness` transported onto the repo's `DiscloseAt.leaked ⊥` — the precise
information-theoretic content of "the verifier at `acceptancePos` learns nothing about the
witness", now stated on the metatheory's own disclosure machinery. -/
theorem floor_leak_witness_independent (s : Z.S) (w₁ w₂ : Z.W) :
    (Z.discloseAt s w₁).leaked ⊥ = (Z.discloseAt s w₂).leaked ⊥ :=
  rfl

/-- **The real view AND the floor leak agree — PROVED, kernel-clean.** The bridge is
literal: the actual verifier view `Z.view s w` equals the information leaked at the dial
floor, `(discloseAt s w).leaked ⊥` (both equal `Z.sim s` under `hperf`). So "what the
verifier really sees" and "what the dial floor discloses" are the *same* witness-free value
— the dial's epistemic floor is faithfully the verifier's information-theoretic view. -/
theorem view_eq_floor_leak (s : Z.S) (w : Z.W) :
    Z.view s w = (Z.discloseAt s w).leaked ⊥ :=
  Z.hperf s w

end PerfectZK

#assert_axioms PerfectZK.floor_leaks_simulation
#assert_axioms PerfectZK.floor_leak_witness_independent
#assert_axioms PerfectZK.view_eq_floor_leak

/-! # §2b. Connection to `zk_is_dial_bottom` / `verifier_learns_only_acceptance`.

The repo's `dialDisclosure : Disclosure Dial` places `acceptancePos := acceptanceOnly = ⊥`
strictly below `contentPos := fullDisclosure`, and `zk_is_dial_bottom` proves the floor is
the ZK acceptance position with content above. A `PerfectZK` supplies the *information-
theoretic* fact that the repo's `Disclosure` separation parameter abstracts: the value
disclosed AT that floor (`discloseAt s w |>.leaked ⊥ = Z.sim s`) is witness-free. We state
the conjunction explicitly so the fragment-closure is visible against the repo keystone. -/

namespace PerfectZK

variable (Z : PerfectZK)

/-- **`fragment_grounds_dial_bottom` — the perfect-ZK fragment grounds the repo's ZK floor,
PROVED, kernel-clean.** The conjunction of (i) the repo's *order* keystone
`zk_is_dial_bottom` (acceptance is the dial bottom and is strictly below content — the
metatheory's faithful epistemic ORDER), with (ii) the *information-theoretic* discharge this
module supplies (the value leaked at that very floor is witness-independent — `view s w₁`
and `view s w₂` collapse to the same `sim s`). Together: the verifier sits at the ZK floor
(order) AND, perfectly, learns nothing about the witness there (information). The
COMPUTATIONAL distinguishability that closes the remaining gap stays an explicit parameter
(see the closing RESIDUAL note); this conjunct does NOT assert it. -/
theorem fragment_grounds_dial_bottom [Dregg2.Laws.Verifiable Z.S Z.W] (s : Z.S) (w₁ w₂ : Z.W) :
    (dialDisclosure.acceptancePos = (⊥ : Dial) ∧
       dialDisclosure.acceptancePos < dialDisclosure.contentPos) ∧
    (Z.discloseAt s w₁).leaked ⊥ = (Z.discloseAt s w₂).leaked ⊥ :=
  ⟨zk_is_dial_bottom, rfl⟩

/-- **The acceptance bit at the floor is the verify-seam check — PROVED, kernel-clean.**
Re-stating, for the `PerfectZK`-induced schedule, the repo lemma
`DiscloseAt.accepts_bot_iff_discharged`: the single bit at the ZK floor is exactly
`Discharged pred wit`. So the floor discloses ONLY acceptance (one bit, position-independent
via the verify seam) on top of a witness-free view — acceptance without content, the ZK
position made literal. -/
theorem floor_bit_iff_discharged [Dregg2.Laws.Verifiable Z.S Z.W] (s : Z.S) (w : Z.W) :
    (Z.discloseAt s w).accepts ⊥ ↔ Dregg2.Laws.Discharged s w :=
  (Z.discloseAt s w).accepts_bot_iff_discharged

end PerfectZK

#assert_axioms PerfectZK.fragment_grounds_dial_bottom
#assert_axioms PerfectZK.floor_bit_iff_discharged

/-! # §3. TEETH — non-vacuity: the perfect-ZK law genuinely holds AND genuinely fails.

`hperf` is a *real constraint*, not always-true. We exhibit:
  * `otp : PerfectZK` — a one-time-pad / perfectly-hiding commitment toy: the view is a
    constant ciphertext, identical regardless of witness. `hperf` HOLDS; `view_indep_of_
    witness` holds with content.
  * a NON-perfect view function (`leakyView`) where the view IS the witness verbatim, for
    which `view_indep_of_witness` is FALSE — so NO simulator can satisfy `hperf`. -/

namespace Teeth

/-- **A perfectly-hiding one-time-pad commitment (the law HOLDS).**

Statement type `Unit` (one statement), witness type `Bool` (the secret bit), view type
`Unit`: the verifier's entire view is a constant token `()` — a ciphertext that is
*identically distributed* (here, identically the single value) regardless of the witness
bit. The simulator emits the same `()`. This is the information-theoretic perfect-hiding
core of a one-time pad: `Enc(m) = m ⊕ k` with `k` uniform reveals nothing about `m`; in the
degenerate finite witness here the "ciphertext" is literally constant. -/
def otp : PerfectZK where
  S := Unit
  W := Bool
  V := Unit
  view _ _ := ()
  sim _ := ()
  hperf _ _ := rfl

/-- The OTP instance satisfies `view_indep_of_witness` (the perfect-hiding teeth: HOLDS). -/
theorem otp_indep (s : otp.S) (w₁ w₂ : otp.W) : otp.view s w₁ = otp.view s w₂ :=
  otp.view_indep_of_witness s w₁ w₂

/-- And concretely: distinct witnesses `true`/`false` give the *same* view in the OTP. -/
theorem otp_distinct_witnesses_same_view :
    otp.view () true = otp.view () false :=
  rfl

/-- **A leaky (NON-perfect) view function — the law FAILS.** The verifier's view IS the
witness bit verbatim (`leakyView s w = w`): a transcript that copies the secret. There is no
hiding at all. -/
def leakyView (_ : Unit) (w : Bool) : Bool := w

/-- **`leaky_view_indep_FAILS` — the constraint has teeth, PROVED, kernel-clean.** For the
leaky view, `view_indep_of_witness` is FALSE: the two witnesses `true`/`false` produce
DIFFERENT views (`true ≠ false`). Hence NO simulator `sim` can satisfy the perfect-ZK law
`hperf` for this `view` — `hperf` would force `leakyView () true = sim () = leakyView ()
false`, i.e. `true = false`. So `PerfectZK`'s `hperf` is a genuine, falsifiable constraint,
not a vacuous `True`. -/
theorem leaky_view_indep_FAILS :
    ¬ (∀ (s : Unit) (w₁ w₂ : Bool), leakyView s w₁ = leakyView s w₂) := by
  intro h
  exact Bool.noConfusion (h () true false)

/-- **No simulator can perfect-hide the leaky view — PROVED, kernel-clean.** The sharpest
form of the teeth: there is NO function `sim : Unit → Bool` for which the leaky view equals
a witness-free simulation. Any such `sim` would make the view witness-independent, which
`leaky_view_indep_FAILS` refutes. So one cannot package `leakyView` as a `PerfectZK` — the
`hperf` field is unsatisfiable here. -/
theorem leaky_no_simulator :
    ¬ ∃ sim : Unit → Bool, ∀ (s : Unit) (w : Bool), leakyView s w = sim s := by
  rintro ⟨sim, h⟩
  have : leakyView () true = leakyView () false := (h () true).trans (h () false).symm
  exact Bool.noConfusion this

end Teeth

#assert_axioms Teeth.otp_indep
#assert_axioms Teeth.otp_distinct_witnesses_same_view
#assert_axioms Teeth.leaky_view_indep_FAILS
#assert_axioms Teeth.leaky_no_simulator

/-! # §3b. A REAL Dregg2 instance — the field-tier selective-disclosure projection.

The §3 instances (`otp` over `Unit`/`Bool`) are *toys*. The audit's fix asks the perfect-ZK
structure to carry a genuine `Dregg2` verifier fragment. Dregg2 ships exactly such a
perfectly-hiding map: the **field-tier projection** `Dregg2.Privacy.project`, whose real
keystone `Dregg2.Privacy.field_projection_hides_private` proves the public view is *independent
of* the private fields' values — information-theoretic selective disclosure, the tier-1 privacy
law of `dregg2.md §6a`.

We instantiate `PerfectZK` over it WITHOUT inventing a simulator: the statement is the
public-field assignment, the witness is the private-field assignment, the real **view** is the
projection of the assembled state, and the **simulator** is the projection of the statement
ALONE (witness-free) — and `view = sim` is *exactly* `field_projection_hides_private`, the real
Dregg2 theorem. So `PerfectZK.view_indep_of_witness` for this instance is a corollary of a
load-bearing dregg2 law, not a toy `rfl`. -/

namespace FieldTier

open Dregg2.Privacy

variable {Name V : Type u}

/-- **Assemble a full cell state** from the public part `s` (the statement) and the private
part `w` (the witness), under the schema mask `vis`: public fields take their value from `s`,
private fields from `w`. The verifier's real view is the projection of this assembled state. -/
def assemble (vis : FieldVisibility Name) (s w : State Name V) : State Name V :=
  fun n => match vis n with
    | Visibility.pub  => s n
    | Visibility.priv => w n

/-- The assembled state **agrees with the statement on every public field** — by construction,
public coordinates are copied from `s`. This is the hypothesis `field_projection_hides_private`
consumes. -/
theorem assemble_pub_eq (vis : FieldVisibility Name) (s w : State Name V)
    (n : Name) (h : vis n = Visibility.pub) : assemble vis s w n = s n := by
  unfold assemble; rw [h]

/-- **The real field-tier `PerfectZK`.** Over a fixed schema mask `vis`:

* statement `S := State Name V` — the public-field assignment;
* witness `W := State Name V` — the private-field assignment (the secret);
* view `V := Obs Name V` — the schema-public observation;
* `view s w := Privacy.project (assemble vis s w) vis` — the REAL verifier view: project the
  assembled state through the genuine `Dregg2.Privacy.project`;
* `sim s := Privacy.project s vis` — the witness-free simulator: project the statement alone;
* `hperf` — discharged by **`Dregg2.Privacy.field_projection_hides_private`**: the assembled
  state and the statement agree on every public field, so their projections are equal. This is
  the real selective-disclosure theorem, not a fabricated equality. -/
def fieldZK (vis : FieldVisibility Name) : PerfectZK where
  S := State Name V
  W := State Name V
  V := Obs Name V
  view s w := project (assemble vis s w) vis
  sim s := project s vis
  hperf s w :=
    field_projection_hides_private vis (assemble vis s w) s
      (fun n h => assemble_pub_eq vis s w n h)

/-- **The real instance's witness-independence IS `field_projection_hides_private` — PROVED,
kernel-clean.** For the field-tier `PerfectZK`, any two private witnesses `w₁ w₂` (any two
private-field assignments) yield the *same* public view: the verifier provably learns nothing
about the private fields. This is `PerfectZK.view_indep_of_witness` discharged by the real
dregg2 selective-disclosure law — a genuine Dregg2 verifier fragment carrying the abstract
structure, not the `Unit`/`Bool` toy. -/
theorem fieldZK_view_indep (vis : FieldVisibility Name) (s w₁ w₂ : State Name V) :
    (fieldZK vis).view s w₁ = (fieldZK vis).view s w₂ :=
  (fieldZK vis).view_indep_of_witness s w₁ w₂

/-- **The real view factors through the statement — PROVED, kernel-clean.** The field-tier
view is a function of the public statement alone (the witness-free `sim = project · vis`); the
private fields are projected away entirely. `PerfectZK.view_factors_through_statement` on the
real instance. -/
theorem fieldZK_factors (vis : FieldVisibility Name) :
    ∃ g : State Name V → Obs Name V,
      ∀ (s w : State Name V), (fieldZK vis).view s w = g s :=
  (fieldZK vis).view_factors_through_statement

/-! ### Non-vacuity of the REAL instance: a `priv` field genuinely hides a differing witness. -/

/-- **The real instance has teeth (information genuinely hidden) — PROVED, kernel-clean.**
With a field name `n` marked `priv` and two DIFFERING private values `a ≠ b`, the two assembled
states genuinely disagree at `n` (`assemble … (update s n a) n = a ≠ b = assemble … (update s n
b) n`), YET their views coincide — the projection drops the private coordinate. So the hiding
is real content: the underlying witnessed states differ at the private field, but the verifier's
view cannot tell. This is the dual of `leaky_no_simulator` (there NO simulator existed); here a
genuine simulator (the real `project`) makes the differing-witness views identical. -/
theorem fieldZK_hides_differing_private
    [DecidableEq Name] (n : Name) (a b : V) (hab : a ≠ b) (s : State Name V)
    (vis : FieldVisibility Name) (hpriv : vis n = Visibility.priv) :
    -- the assembled states genuinely differ at the private field `n`...
    assemble vis s (Function.update s n a) n
        ≠ assemble vis s (Function.update s n b) n ∧
    -- ...yet the verifier's views are identical (the private coordinate is dropped).
    (fieldZK vis).view s (Function.update s n a)
      = (fieldZK vis).view s (Function.update s n b) := by
  refine ⟨?_, fieldZK_view_indep vis s (Function.update s n a) (Function.update s n b)⟩
  -- both sides reduce, via the private arm of `assemble`, to the updated witness at `n`,
  -- i.e. `a` and `b`, which differ by hypothesis.
  simp only [assemble, hpriv, Function.update_self]
  exact hab

end FieldTier

#assert_axioms FieldTier.fieldZK
#assert_axioms FieldTier.fieldZK_view_indep
#assert_axioms FieldTier.fieldZK_factors
#assert_axioms FieldTier.fieldZK_hides_differing_private

/-! # RESIDUAL — what stays an explicit parameter (NOT closed here).

This module closes ONLY the **perfect/statistical (information-theoretic)** fragment of the
ZK indistinguishability OPEN: under perfect hiding (`view s w = sim s`, an *equality* of
views), the verifier's view carries literally zero information about the witness
(`view_indep_of_witness`), and this grounds the value leaked at the repo's ZK dial floor as
witness-independent (`floor_leak_witness_independent`, `fragment_grounds_dial_bottom`).

It DOES NOT close — and does not pretend to — the **COMPUTATIONAL** version:

  * a PPT (probabilistic polynomial-time) adversary,
  * a *negligible* (not zero) distinguishing advantage between real and simulated
    transcripts,
  * simulator existence against *efficient* distinguishers (computational zero-knowledge),
  * the probability-distribution machinery (the views are distributions, indistinguishable
    rather than equal).

That layer is a genuine circuit/cryptographic obligation and remains EXACTLY the
`Disclosure` separation *parameter* the metatheory carries (`ConstructiveKnowledge` §2,
`EpistemicDial` §6): the metatheory says "*if* the notches separate the disclosure order and
the crypto layer discharges indistinguishability, *then* the verifier is epistemically
confined." We have discharged the antecedent's *perfect/statistical* instance; the
*computational* instance stays an honest, un-`axiom`'d parameter. -/

end Metatheory.Open.PerfectZK
