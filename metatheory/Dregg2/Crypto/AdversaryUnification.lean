/-
# `Dregg2.Crypto.AdversaryUnification` — ONE adversary notion, ONE cost semantics, with the two
classical worlds PROVED to be one world at two points of a single budget scale — and the quantum
world put on the same scale as far as it soundly goes, with the obstruction to going further NAMED.

## The fragmentation this file answers (A1 of `docs/reference/ADOPT-ARKLIB-VCVIO-IDEAS.md`)

The tree carries three adversary notions that never meet:

  1. **World 1** — `RomQueryFloor.RomEff`: adversaries that factor through a `RomOracle.OracleComp`
     query tree, cost = `QueryBounded` (a budget `Q : ℕ → ℕ`).
  2. **World 2** — `FloorGames.Adversary`: a raw function `∀ l, Inst l → Ans l`, NO resource bound in
     the type, advantage = `winProb` over the sampled instance.
  3. **World 3** — `OneWayToHiding.Adversary`: a quantum unitary sequence with a query count `q`,
     conclusions in ℓ²-norm at a SINGLE finite basis, no λ, no `Negl`.

That fragmentation is what let `CostAdversary.IsPolyTime` (a poly-SIZE-answers class) masquerade as
an efficiency bound: with no shared cost semantics there was nothing to measure it against.

## §2 — ⚑ THE UNIFICATION THEOREM: World 2 IS World 1 at the exhaustive budget.

The unifying cost semantics is the QUERY BUDGET, and the theorem that makes it a genuine
unification (not a definitional alias) is `adversary_romEff_exhaustive` /
`romEff_exhaustive_eq_top`:

    RomEff F (fun l => |D l|)  =  (fun _ => True)

EVERY raw `FloorGames.Adversary` of an oracle game — `Classical.choice` ones included — factors
through a query tree that queries the WHOLE domain (`tabulateComp`: reconstruct the oracle's truth
table point by point, then run the raw adversary on the reconstruction). So the "unrestricted"
World-2 class is not a fourth notion of adversary: it is the TOP of World 1's budget scale, and the
scale is total on it (`adversary_romEff_some_budget`: every adversary has SOME budget). One
adversary notion — the oracle program; one cost — how much of the oracle it reads; World 2 = the
`Q = |D|` point.

⚑ Position against `RomQueryDial`, whose substrate this reuses (`reconstruct`/`reconstruct_map` +
`OracleComp.ofList`): that file proved the budget is a load-bearing DIAL by embedding ONE adversary
(`bruteComp`, the paying twin of the collision `choiceAdv`) at the unkeyed game. This file proves
the embedding for EVERY adversary at once and states it as a predicate EQUALITY — a witness became
a unification — and extends it to the KEYED game (the deployed floor's world), the CARRIER games
(the binding layer), and `choiceAdv` itself (no twin needed: the choice adversary literally IS an
exhaustive-budget member, `choiceAdv_separates`).

This converts the floor/refutation dichotomy into a statement about ONE parameter:

  * at a POLYNOMIAL budget the floor is a theorem (`keyedRom_hard`, birthday bound);
  * at the EXHAUSTIVE budget the floor is FALSE (`keyedRom_exhaustive_not_hard` — via the same
    equality, this IS `keyedRom_top_false`);
  * the hierarchy is STRICT, witnessed by the exact adversary that killed the `IsPolyTime` floor:
    `choiceAdv_separates` — the `Classical.choice` collision answerer is IN the exhaustive class and
    OUT of every polynomial class (`keyedChoiceAdv_excluded` is untouched). The counterexample
    still dies where it must and lives where it must; unification collapsed nothing
    (`keyedRomEff_ne_exhaustive`).

`carrierAdversary_romCarrierEff_exhaustive` gives the same result at the binding layer
(`RomBindingReduction.romCarrierGame`), so the carrier world rides the same scale.

## §5 — the quantum world: same budget scale, same `Negl` discipline, and the honest boundary.

What IS soundly shared with World 3, and is proved here:

  * `bornProb_diff_le` — the PROBABILITY-level O2H bound: `|Pr[A^{O}=1] − Pr[A^{O'}=1]| ≤
    4·√(q·Pfind)` for sub-normalized initial states (from `o2h_bound` via `state_norm`/`amp_le_one`;
    `bornProb` is a probability, the same UNITS as `winProb`).
  * `QRomAdversaryFamily` — the λ-INDEXED quantum adversary, with the SAME `Q : ℕ → ℕ` budget shape
    (`QueryBudget`) and its advantage as an `Ensemble`, so `Negl` applies to it
    (`QRomAdversaryFamily.adv_negl`). World 3 statements are now comparable in COST and in
    ADVANTAGE LANGUAGE with Worlds 1/2. `toyQFamily` witnesses the class inhabited.

⚑ **WHAT IS DELIBERATELY NOT CLAIMED — the obstruction, precisely.** `keyedRom_hard` remains a
CLASSICAL-ROM statement. No transport of the keyed floor to quantum adversaries is stated, because
the missing object is not a lemma but a SEMANTICS: World 1/2 games SAMPLE the oracle `H` and count
`winProb` across instances, while `OracleDiffData` fixes ONE pair of oracles — there is no
average-over-sampled-`H` Born semantics (no `winProb (fun H => Born-measured win event of A^{O_H})`)
in the tree, and no reversible compilation of a classical `OracleComp` into a `Unitary B` either.
Any consumer of `keyedRom_hard` that calls itself post-quantum carries an unstated
classical-adversary hypothesis; this file makes that boundary visible instead of papering over it.

⚑ **The FIXED-function world (`FloorGames.hashGame`) is deliberately NOT unified.** Its instance is
a KEY while the hash stays public, so oracle-query cost measures nothing there — against a fixed
known function a query-bounded adversary brute-forces (`RomBindingReduction` header proves the
argument). That world is the refuted `IsPolyTime` disease, not a fourth pole to preserve; its sound
successor IS the keyed ROM world this file unifies onto.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Crypto.RomBindingReduction
import Dregg2.Crypto.RomQueryDial
import Dregg2.Crypto.OneWayToHiding
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.AdversaryUnification

open Dregg2.Crypto.ConcreteSecurity
  (Ensemble Negl PolyBounded negl_of_eventually_le negl_const_mul)
open Dregg2.Crypto.FloorGames
  (Game Adversary Hard gameAdv solvableFrac choiceAdv choiceAdv_gameAdv
   hard_top_iff_solvableFrac_negl)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (RomFamily romCollisionGame RomComp romAdv RomEff)
open Dregg2.Crypto.KeyedRomFloor
  (KeyedRomFamily keyedRomGame KeyedRomEff keyedRom_hard keyedRom_top_false
   keyedChoiceAdv_excluded deployedKeyedFamily deployedKeyed_card_R deployedKeyed_compressing
   deployedKeyed_verdict)
open Dregg2.Crypto.RomBindingReduction (RomCarrier romCarrierGame RomCarrierComp RomCarrierEff)
open Dregg2.Crypto.RomQueryDial (reconstruct reconstruct_map romCollision_exhaustive_budget_false)
open Dregg2.Crypto.QuantumOracle (QState Unitary OracleDiffData)
open Dregg2.Crypto.OneWayToHiding
  (Pfind o2h_bound toyAdv toyD toyMeas toyMeas_norm_le toyPsi toy_Pfind)

set_option autoImplicit false

/-! ## §1 — the TABULATING oracle program: ANY raw function of the oracle, as a query tree.

Built from the substrate the tree already has — `RomOracle.OracleComp.ofList` (query a fixed list,
return a function of the answers) and `RomQueryDial.reconstruct`/`reconstruct_map` (a complete
answer list rebuilds the oracle exactly). `RomQueryDial.bruteComp` is this construction specialized
to ONE `f` (choose a collision); `tabulateComp` is the same move for EVERY `f`, generic in the
answer type — which is what turns a witness into an embedding. -/

/-- **The exhaustive tabulating program**: query the whole (finite) domain, rebuild the oracle from
the answers (`RomQueryDial.reconstruct`), and run the raw function `f` on the reconstruction.
Generic in the answer type `A`, so it serves the collision game and every carrier game alike. -/
noncomputable def tabulateComp {D R A : Type} [Fintype D] [DecidableEq D] [Nonempty R]
    (f : (D → R) → A) : OracleComp D R A :=
  OracleComp.ofList (Finset.univ : Finset D).toList
    (fun rs => f (reconstruct (Finset.univ : Finset D).toList rs (Classical.arbitrary R)))

/-- **⚑ THE TABULATING PROGRAM COMPUTES THE RAW FUNCTION EXACTLY.** Over the full enumeration the
reconstruction IS the oracle (`RomQueryDial.reconstruct_map`), so the tree's output is `f H` — for
EVERY `f`, including a `Classical.choice` one. Reading the whole oracle is not beyond the query
model; it just costs the whole domain. -/
theorem tabulateComp_eval {D R A : Type} [Fintype D] [DecidableEq D] [Nonempty R]
    (f : (D → R) → A) (H : D → R) : (tabulateComp f).eval H = f H := by
  unfold tabulateComp
  rw [OracleComp.ofList_eval,
    reconstruct_map (Finset.univ : Finset D).toList
      (fun x => Finset.mem_toList.2 (Finset.mem_univ x)) H]

/-- The exhaustive program's budget is exactly the domain size. -/
theorem tabulateComp_queryBounded {D R A : Type} [Fintype D] [DecidableEq D] [Nonempty R]
    (f : (D → R) → A) : QueryBounded (Fintype.card D) (tabulateComp f) := by
  have h := OracleComp.ofList_queryBounded (D := D) (R := R)
    (Finset.univ : Finset D).toList
    (fun rs => f (reconstruct (Finset.univ : Finset D).toList rs (Classical.arbitrary R)))
  rwa [Finset.length_toList, Finset.card_univ] at h

/-! ## §2 — ⚑ THE UNIFICATION: World 2 = World 1 at the exhaustive budget. -/

/-- The budget scale is MONOTONE: a `Q`-budget adversary is a `Q'`-budget adversary for `Q ≤ Q'`
pointwise. This is what makes `RomEff` a genuine SCALE of classes rather than a bag of predicates. -/
theorem romEff_mono (F : RomFamily) {Q Q' : ℕ → ℕ} (hle : ∀ l, Q l ≤ Q' l)
    (A : Adversary (romCollisionGame F)) (hA : RomEff F Q A) : RomEff F Q' A := by
  obtain ⟨M, hM, hrun⟩ := hA
  exact ⟨M, fun l => (hM l).mono (hle l), hrun⟩

/-- **The exhaustive budget** — the domain size at each parameter, the top of the cost scale. -/
def exhaustiveBudget (F : RomFamily) : ℕ → ℕ :=
  fun l => letI := F.dFin l; Fintype.card (F.D l)

/-- **⚑⚑ THE EMBEDDING — every raw adversary factors through an exhaustive-budget query tree.**
This is World 2 landing INSIDE World 1: the arbitrary function of the whole oracle, which
`RomOracle`'s header calls "the disease", is exactly the `Q = |D|` point of the query-cost scale.
NOT a definitional alias — the witness is the `tabulateComp` reconstruction. -/
theorem adversary_romEff_exhaustive (F : RomFamily) (A : Adversary (romCollisionGame F)) :
    RomEff F (exhaustiveBudget F) A := by
  refine ⟨fun l => letI := F.dFin l; letI := F.dDec l; letI := F.rNe l;
      tabulateComp (A.run l), fun l => ?_, fun l H => ?_⟩
  · letI := F.dFin l; letI := F.dDec l; letI := F.rNe l
    exact tabulateComp_queryBounded (A.run l)
  · letI := F.dFin l; letI := F.dDec l; letI := F.rNe l
    exact (tabulateComp_eval (A.run l) H).symm

/-- **⚑⚑⚑ THE UNIFICATION THEOREM: the unrestricted World-2 class IS the exhaustive-budget
World-1 class**, as an equality of predicates. `Eff := ⊤` was never a fourth adversary notion — it
is a point on the query-budget scale, and the whole trichotomy (floor proved / floor false /
counterexample excluded) becomes a statement about WHERE on one scale you stand. -/
theorem romEff_exhaustive_eq_top (F : RomFamily) :
    RomEff F (exhaustiveBudget F) = fun _ => True := by
  funext A
  simp only [eq_iff_iff, iff_true]
  exact adversary_romEff_exhaustive F A

/-- **The scale is TOTAL on World 2**: every raw adversary has SOME budget. One adversary notion,
one cost semantics, no residue. -/
theorem adversary_romEff_some_budget (F : RomFamily) (A : Adversary (romCollisionGame F)) :
    ∃ Q : ℕ → ℕ, RomEff F Q A :=
  ⟨exhaustiveBudget F, adversary_romEff_exhaustive F A⟩

/-- **Hardness transports across the unification**: the exhaustive-budget floor IS the unrestricted
floor. (So `romCollision_top_false` is, after unification, a statement about the top of the budget
scale — not about a different kind of adversary.) -/
theorem hard_exhaustive_iff_hard_top (F : RomFamily) :
    Hard (romCollisionGame F) (RomEff F (exhaustiveBudget F))
      ↔ Hard (romCollisionGame F) (fun _ => True) := by
  rw [romEff_exhaustive_eq_top]

/-! ## §3 — the keyed floor on the unified scale: both poles preserved, the counterexample
still dies, and the hierarchy is STRICT. -/

/-- The exhaustive budget of the keyed (tag-separated) family. -/
def keyedExhaustiveBudget (F : KeyedRomFamily) : ℕ → ℕ :=
  exhaustiveBudget F.toRomFamily

/-- The embedding at the keyed game: every raw keyed adversary is an exhaustive-budget member. -/
theorem adversary_keyedRomEff_exhaustive (F : KeyedRomFamily)
    (A : Adversary (keyedRomGame F)) :
    KeyedRomEff F (keyedExhaustiveBudget F) A :=
  adversary_romEff_exhaustive F.toRomFamily A

/-- The unification theorem at the keyed game. -/
theorem keyedRomEff_exhaustive_eq_top (F : KeyedRomFamily) :
    KeyedRomEff F (keyedExhaustiveBudget F) = fun _ => True :=
  romEff_exhaustive_eq_top F.toRomFamily

/-- **⚑ THE TOP OF THE SCALE IS NOT HARD** (compressing family): after unification,
`keyedRom_top_false` is exactly the statement that the exhaustive-budget floor fails — hardness is
a property of the BUDGET, and at `Q = |D|` the birthday bound `(Q² + 1)/|R|` has no content. The
keyed floor (`keyedRom_hard`, polynomial budget) is untouched: same game, same scale, opposite
verdicts at the two ends. -/
theorem keyedRom_exhaustive_not_hard (F : KeyedRomFamily)
    (hc : ∀ l, letI := (F.toRomFamily).dFin l; letI := (F.toRomFamily).rFin l;
      Fintype.card (F.toRomFamily.R l) < Fintype.card (F.toRomFamily.D l)) :
    ¬ Hard (keyedRomGame F) (KeyedRomEff F (keyedExhaustiveBudget F)) :=
  romCollision_exhaustive_budget_false F.toRomFamily hc

/-- **⚑⚑ THE COUNTEREXAMPLE STILL DIES — AND NOW ITS PLACE ON THE SCALE IS EXACT.** The
`Classical.choice` collision answerer (the adversary that refuted every unrestricted floor) is IN
the exhaustive-budget class and OUT of every polynomial-budget class. Unification did not weaken
the exclusion (`keyedChoiceAdv_excluded` is applied verbatim); it explains it — the choice
adversary is not an alien to the query model, it is an adversary whose honest query cost is the
whole domain. -/
theorem choiceAdv_separates (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (hc : ∀ l, letI := (F.toRomFamily).dFin l; letI := (F.toRomFamily).rFin l;
      Fintype.card (F.toRomFamily.R l) < Fintype.card (F.toRomFamily.D l))
    (hne : ∀ l, Nonempty ((keyedRomGame F).Ans l)) :
    KeyedRomEff F (keyedExhaustiveBudget F) (choiceAdv (keyedRomGame F) hne)
      ∧ ¬ KeyedRomEff F Q (choiceAdv (keyedRomGame F) hne) :=
  ⟨adversary_keyedRomEff_exhaustive F _, keyedChoiceAdv_excluded F Q hQ hw hc hne⟩

/-- **The budget hierarchy is STRICT** — the polynomial-budget class and the exhaustive-budget
class are provably DIFFERENT predicates, separated by the choice adversary. The unification is not
a collapse. -/
theorem keyedRomEff_ne_exhaustive (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (hc : ∀ l, letI := (F.toRomFamily).dFin l; letI := (F.toRomFamily).rFin l;
      Fintype.card (F.toRomFamily.R l) < Fintype.card (F.toRomFamily.D l))
    (hne : ∀ l, Nonempty ((keyedRomGame F).Ans l)) :
    KeyedRomEff F Q ≠ KeyedRomEff F (keyedExhaustiveBudget F) := by
  intro heq
  obtain ⟨hin, hout⟩ := choiceAdv_separates F Q hQ hw hc hne
  rw [heq] at hout
  exact hout hin

/-! ## §4 — the binding layer rides the same scale. -/

/-- The embedding at a carrier forgery game: every raw carrier forger factors through an
exhaustive-budget query tree (the SAME `tabulateComp`, at the carrier's answer type). So
`RomBindingReduction`'s world is on the unified scale too, and `romCarrier_binds` /
`romCarrier_choiceForger_excluded` read as budget statements. -/
theorem carrierAdversary_romCarrierEff_exhaustive (F : KeyedRomFamily) (C : RomCarrier F)
    (A : Adversary (romCarrierGame F C)) :
    RomCarrierEff F C (keyedExhaustiveBudget F) A := by
  refine ⟨fun l => letI := (F.toRomFamily).dFin l; letI := (F.toRomFamily).dDec l;
      letI := (F.toRomFamily).rNe l; tabulateComp (A.run l), fun l => ?_, fun l H => ?_⟩
  · letI := (F.toRomFamily).dFin l; letI := (F.toRomFamily).dDec l
    letI := (F.toRomFamily).rNe l
    exact tabulateComp_queryBounded (A.run l)
  · letI := (F.toRomFamily).dFin l; letI := (F.toRomFamily).dDec l
    letI := (F.toRomFamily).rNe l
    exact (tabulateComp_eval (A.run l) H).symm

/-- The unification theorem at the carrier game. -/
theorem romCarrierEff_exhaustive_eq_top (F : KeyedRomFamily) (C : RomCarrier F) :
    RomCarrierEff F C (keyedExhaustiveBudget F) = fun _ => True := by
  funext A
  simp only [eq_iff_iff, iff_true]
  exact carrierAdversary_romCarrierEff_exhaustive F C A

/-! ## §5 — the whole verdict at the deployed-shape family: the unified scale, priced. -/

/-- The deployed keyed game's answer space is inhabited (two tagged messages always exist). -/
theorem deployedKeyed_ansNe : ∀ l, Nonempty ((keyedRomGame deployedKeyedFamily).Ans l) := by
  intro l
  have h2 : 0 < 2 * 2 ^ l := by positivity
  show Nonempty ((Fin 4 × Fin (2 * 2 ^ l)) × (Fin 4 × Fin (2 * 2 ^ l)))
  exact ⟨((0, ⟨0, h2⟩), (0, ⟨0, h2⟩))⟩

/-- `Q l = l + 2` is a polynomially bounded budget (the budget `deployedKeyed_verdict` prices). -/
theorem polyBudget_l_add_two :
    PolyBounded (fun l => (((l + 2 : ℕ) : ℝ)) * (((l + 2 : ℕ) : ℝ)) + 1) := by
  refine ⟨2, 6, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith

/-- **⚑⚑⚑ THE UNIFIED VERDICT AT THE DEPLOYED SHAPE.** At one concrete keyed family, all four
facts of the unified picture at once:

  1. **totality** — EVERY adversary (World 2 entire) is on the budget scale, at the exhaustive
     point;
  2. **the floor holds at a polynomial budget** (`keyedRom_hard` at `Q l = l + 2`) — unification
     did not weaken it;
  3. **the floor fails at the exhaustive budget** — the old "unrestricted refutation" is the top
     of the same scale;
  4. **the counterexample is priced exactly**: the choice adversary is a member at `Q = |D|` and a
     non-member at `Q l = l + 2`.

So after unification the keyed floor is still non-refutable at its stated budget, both poles are
inhabited, and what used to be three adversary notions is one notion at different budgets. -/
theorem deployedUnification_verdict :
    (∀ A : Adversary (keyedRomGame deployedKeyedFamily),
        KeyedRomEff deployedKeyedFamily (keyedExhaustiveBudget deployedKeyedFamily) A)
      ∧ Hard (keyedRomGame deployedKeyedFamily)
          (KeyedRomEff deployedKeyedFamily (fun l => l + 2))
      ∧ ¬ Hard (keyedRomGame deployedKeyedFamily)
          (KeyedRomEff deployedKeyedFamily (keyedExhaustiveBudget deployedKeyedFamily))
      ∧ (KeyedRomEff deployedKeyedFamily (keyedExhaustiveBudget deployedKeyedFamily)
            (choiceAdv (keyedRomGame deployedKeyedFamily) deployedKeyed_ansNe)
          ∧ ¬ KeyedRomEff deployedKeyedFamily (fun l => l + 2)
            (choiceAdv (keyedRomGame deployedKeyedFamily) deployedKeyed_ansNe)) :=
  ⟨fun A => adversary_keyedRomEff_exhaustive deployedKeyedFamily A,
   deployedKeyed_verdict.1,
   keyedRom_exhaustive_not_hard deployedKeyedFamily deployedKeyed_compressing,
   adversary_keyedRomEff_exhaustive deployedKeyedFamily _,
   keyedChoiceAdv_excluded deployedKeyedFamily (fun l => l + 2) polyBudget_l_add_two
     deployedKeyed_card_R deployedKeyed_compressing deployedKeyed_ansNe⟩

/-! ## §6 — the quantum world on the shared scale: probability-level O2H, λ-indexing, `Negl`.

What is proved here is exactly what is sound: World 3's advantage becomes a PROBABILITY
(`bornProb_diff_le`), its adversaries become λ-INDEXED with the same `ℕ → ℕ` budget shape, and its
bounds become `Ensemble`/`Negl` statements. What is NOT claimed: any bridge from these to
`winProb`/`gameAdv` over a SAMPLED oracle — see the header for the precise obstruction. -/

section Quantum

variable {B : Type*} [Fintype B]

/-- **The adversary's state never changes norm** — every work unitary and every oracle application
is an isometry. The invariant behind `amp ≤ 1`. -/
theorem state_norm (A : Dregg2.Crypto.OneWayToHiding.Adversary B) (O : ℕ → Unitary B) (k : ℕ) :
    ‖A.state O k‖ = ‖A.ψ₀‖ := by
  induction k with
  | zero =>
      show ‖A.U 0 A.ψ₀‖ = ‖A.ψ₀‖
      exact (A.U 0).norm_map A.ψ₀
  | succ n ih =>
      show ‖A.U (n + 1) (O n (A.state O n))‖ = ‖A.ψ₀‖
      rw [(A.U (n + 1)).norm_map, (O n).norm_map, ih]

/-- The final state has the initial state's norm. -/
theorem run_norm (A : Dregg2.Crypto.OneWayToHiding.Adversary B) (Or : Unitary B) :
    ‖A.run Or‖ = ‖A.ψ₀‖ :=
  state_norm A (fun _ => Or) A.q

/-- **A Born amplitude is at most `1`** for a sub-normalized initial state — the measurement is
norm-nonincreasing and the evolution is isometric. -/
theorem amp_le_one (A : Dregg2.Crypto.OneWayToHiding.Adversary B)
    (P₁ : QState B →ₗ[ℂ] QState B) (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖) (Or : Unitary B)
    (hψ : ‖A.ψ₀‖ ≤ 1) : A.amp P₁ Or ≤ 1 := by
  calc A.amp P₁ Or = ‖P₁ (A.run Or)‖ := rfl
    _ ≤ ‖A.run Or‖ := hP1 _
    _ = ‖A.ψ₀‖ := run_norm A Or
    _ ≤ 1 := hψ

/-- The semiclassical find probability is nonnegative (a sum of squares). -/
theorem pfind_nonneg (A : Dregg2.Crypto.OneWayToHiding.Adversary B) (D : OracleDiffData B) :
    0 ≤ Pfind A D :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **⚑ PROBABILITY-LEVEL O2H** — the missing rung between `o2h_bound` (amplitudes) and any future
sampled-oracle bridge: for a sub-normalized initial state,

    |Pr[A^{O} = 1] − Pr[A^{O'} = 1]| ≤ 4·√(q · Pfind).

`a² − b² = (a − b)(a + b)` with both amplitudes in `[0,1]` (`amp_le_one`), then `o2h_bound`. The
left side is a DIFFERENCE OF PROBABILITIES — the same units as `winProb`, which is what makes
World-3 statements comparable in advantage language with Worlds 1/2. -/
theorem bornProb_diff_le (A : Dregg2.Crypto.OneWayToHiding.Adversary B) (D : OracleDiffData B)
    (P₁ : QState B →ₗ[ℂ] QState B) (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖) (hψ : ‖A.ψ₀‖ ≤ 1) :
    |A.bornProb P₁ D.O - A.bornProb P₁ D.O'| ≤ 4 * Real.sqrt ((A.q : ℝ) * Pfind A D) := by
  have ha0 : 0 ≤ A.amp P₁ D.O := norm_nonneg _
  have hb0 : 0 ≤ A.amp P₁ D.O' := norm_nonneg _
  have ha1 : A.amp P₁ D.O ≤ 1 := amp_le_one A P₁ hP1 D.O hψ
  have hb1 : A.amp P₁ D.O' ≤ 1 := amp_le_one A P₁ hP1 D.O' hψ
  have hfact : A.bornProb P₁ D.O - A.bornProb P₁ D.O'
      = (A.amp P₁ D.O - A.amp P₁ D.O') * (A.amp P₁ D.O + A.amp P₁ D.O') := by
    rw [A.bornProb_eq_amp_sq, A.bornProb_eq_amp_sq]
    ring
  rw [hfact, abs_mul]
  have hsum : |A.amp P₁ D.O + A.amp P₁ D.O'| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have ho2h := o2h_bound A D P₁ hP1
  calc |A.amp P₁ D.O - A.amp P₁ D.O'| * |A.amp P₁ D.O + A.amp P₁ D.O'|
      ≤ (2 * Real.sqrt ((A.q : ℝ) * Pfind A D)) * 2 :=
        mul_le_mul ho2h hsum (abs_nonneg _) (by positivity)
    _ = 4 * Real.sqrt ((A.q : ℝ) * Pfind A D) := by ring

end Quantum

/-- **The λ-INDEXED quantum adversary family** — World 3 with a security parameter: at each `l` a
`q`-query quantum adversary, a reprogrammed-oracle pair, and a norm-nonincreasing output
measurement on a sub-normalized initial state. This is the λ-indexing without which no World-3
statement is even COMPARABLE to a World-1/2 one (they are `ℕ`-families; a single finite `B` is
not). -/
structure QRomAdversaryFamily (B : ℕ → Type) [∀ l, Fintype (B l)] where
  /-- The quantum adversary at parameter `l`. -/
  adv : ∀ l, Dregg2.Crypto.OneWayToHiding.Adversary (B l)
  /-- The reprogrammed-oracle pair at parameter `l`. -/
  diff : ∀ l, OracleDiffData (B l)
  /-- The output measurement at parameter `l`. -/
  meas : ∀ l, QState (B l) →ₗ[ℂ] QState (B l)
  /-- The measurement is norm-nonincreasing (a legitimate measurement operator). -/
  meas_norm_le : ∀ l (v : QState (B l)), ‖meas l v‖ ≤ ‖v‖
  /-- The initial state is sub-normalized (a legitimate physical state). -/
  init_norm_le : ∀ l, ‖(adv l).ψ₀‖ ≤ 1

namespace QRomAdversaryFamily

variable {B : ℕ → Type} [∀ l, Fintype (B l)]

/-- **The SAME budget shape as Worlds 1/2**: `Q : ℕ → ℕ` bounds the per-parameter query count.
One cost semantics — oracle calls against a budget — now spans all three worlds. -/
def QueryBudget (F : QRomAdversaryFamily B) (Q : ℕ → ℕ) : Prop :=
  ∀ l, (F.adv l).q ≤ Q l

/-- The family's distinguishing advantage, as an `Ensemble` — a probability difference at each
parameter, the World-1/2 advantage LANGUAGE. -/
noncomputable def advEnsemble (F : QRomAdversaryFamily B) : Ensemble := fun l =>
  |(F.adv l).bornProb (F.meas l) (F.diff l).O - (F.adv l).bornProb (F.meas l) (F.diff l).O'|

/-- The family's semiclassical find probability, as an `Ensemble`. -/
noncomputable def findEnsemble (F : QRomAdversaryFamily B) : Ensemble := fun l =>
  Pfind (F.adv l) (F.diff l)

/-- The λ-indexed probability-level O2H bound, at the adversary's own query counts. -/
theorem adv_le (F : QRomAdversaryFamily B) (l : ℕ) :
    F.advEnsemble l ≤ 4 * Real.sqrt (((F.adv l).q : ℝ) * F.findEnsemble l) :=
  bornProb_diff_le (F.adv l) (F.diff l) (F.meas l) (F.meas_norm_le l) (F.init_norm_le l)

/-- The bound at any dominating budget — the budget scale is monotone here exactly as in World 1. -/
theorem adv_le_budget (F : QRomAdversaryFamily B) (Q : ℕ → ℕ) (hQ : F.QueryBudget Q) (l : ℕ) :
    F.advEnsemble l ≤ 4 * Real.sqrt ((Q l : ℝ) * F.findEnsemble l) := by
  refine (F.adv_le l).trans ?_
  have hfind : 0 ≤ F.findEnsemble l := pfind_nonneg (F.adv l) (F.diff l)
  have hq : ((F.adv l).q : ℝ) ≤ (Q l : ℝ) := by exact_mod_cast hQ l
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hq hfind)
  linarith

/-- **The `Negl` discipline transports to the quantum family**: a budget on the queries plus a
negligible find-probability ensemble makes the quantum distinguishing advantage negligible. This is
the semiclassical-O2H usage pattern, stated in the SAME asymptotic language (`Negl` on `Ensemble`)
the classical floors use — with its hypothesis explicit, not smuggled. -/
theorem adv_negl (F : QRomAdversaryFamily B) (Q : ℕ → ℕ) (hQ : F.QueryBudget Q)
    (hfind : Negl (fun l => Real.sqrt ((Q l : ℝ) * F.findEnsemble l))) :
    Negl F.advEnsemble := by
  refine negl_of_eventually_le (Filter.Eventually.of_forall fun l => ?_)
    (negl_const_mul 4 hfind)
  have h0 : (0 : ℝ) ≤ F.advEnsemble l := abs_nonneg _
  have h4 : (0 : ℝ) ≤ 4 * Real.sqrt ((Q l : ℝ) * F.findEnsemble l) := by positivity
  rw [abs_of_nonneg h0, abs_of_nonneg h4]
  exact F.adv_le_budget Q hQ l

end QRomAdversaryFamily

/-! ### The quantum family class is INHABITED (the λ-indexing is not vacuous). -/

/-- The toy initial state is normalized. -/
theorem toyPsi_norm : ‖toyPsi‖ = 1 := by
  unfold Dregg2.Crypto.OneWayToHiding.toyPsi
  rw [PiLp.norm_single]
  simp

/-- **A concrete λ-indexed quantum family** — the O2H toy instance at every parameter (constant
family, `q = 1`). It witnesses `QRomAdversaryFamily` inhabited, so the shared-scale statements
above are about something. -/
noncomputable def toyQFamily : QRomAdversaryFamily (fun _ => Bool × ZMod 2) where
  adv := fun _ => toyAdv
  diff := fun _ => toyD
  meas := fun _ => toyMeas
  meas_norm_le := fun _ => toyMeas_norm_le
  init_norm_le := fun _ => le_of_eq toyPsi_norm

/-- The toy family fits the constant budget `1`. -/
theorem toyQFamily_budget : toyQFamily.QueryBudget (fun _ => 1) :=
  fun _ => le_refl 1

/-- **(TOOTH — the family-level bound FIRES with concrete numbers.)** At `q = 1` and `Pfind = 1`
(the toy is the tight case) the unified bound gives `advEnsemble l ≤ 4` at every parameter — a
genuine consequence of `adv_le`, not a vacuous `≤ ∞`. -/
theorem toyQFamily_adv_le (l : ℕ) : toyQFamily.advEnsemble l ≤ 4 := by
  have h := toyQFamily.adv_le l
  have hq : ((toyQFamily.adv l).q : ℝ) = 1 := by
    have hql : (toyQFamily.adv l).q = 1 := rfl
    rw [hql]
    norm_num
  have hfind : toyQFamily.findEnsemble l = 1 := toy_Pfind
  rw [hq, hfind] at h
  simpa using h

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  tabulateComp_eval,
  tabulateComp_queryBounded,
  romEff_mono,
  adversary_romEff_exhaustive,
  romEff_exhaustive_eq_top,
  adversary_romEff_some_budget,
  hard_exhaustive_iff_hard_top,
  adversary_keyedRomEff_exhaustive,
  keyedRomEff_exhaustive_eq_top,
  keyedRom_exhaustive_not_hard,
  choiceAdv_separates,
  keyedRomEff_ne_exhaustive,
  carrierAdversary_romCarrierEff_exhaustive,
  romCarrierEff_exhaustive_eq_top,
  deployedKeyed_ansNe,
  polyBudget_l_add_two,
  deployedUnification_verdict,
  state_norm,
  run_norm,
  amp_le_one,
  pfind_nonneg,
  bornProb_diff_le,
  QRomAdversaryFamily.adv_le,
  QRomAdversaryFamily.adv_le_budget,
  QRomAdversaryFamily.adv_negl,
  toyPsi_norm,
  toyQFamily_budget,
  toyQFamily_adv_le
]

end Dregg2.Crypto.AdversaryUnification
