/-
# Dregg2.Calculus.BiorthTensor — the TENSOR test: is the bridge load-bearing? (S3 linear + S4 grading.)

`Dregg2/Calculus/Biorthogonality.lean` proved the literal/order families are behaviours — but those
are RECTANGLES (point-tests), closed under almost any orthogonality. `docs/TRANSCENDENTAL-SYNTAX-
BRIDGE.md` (STATUS) names the two questions that decide whether the bridge is LOAD-BEARING or
decorative. This module answers both.

## TARGET 1 — THE TENSOR / LINEARITY. VERDICT: **CONDITIONAL YES, with the boundary made exact.**

The tensor lives over a COMPOSITE universe (stella `mll.rs` §69.35–36: `A ⊗ B = (A ⊙ B)^⊥⊥`, the
biorthogonal of the pairwise-union pre-tensor — NOT `(A^⊥ ∪ B^⊥)^⊥` over one universe, which is the
additive `&` by the landed `coOrth_union`; `orth_union_is_with` pins that distinction). A composite
move is a PAIR of guarded writes (debit at src, credit at dst — the `move` verb,
`VerbCompression.moveStep`); conservation is `Σδ = 0` across the pair (`move_conserves` /
`reachable_total_zero`).

  * **THE OBSTRUCTION (fully general).** Over ANY per-component test family — any test type `R`,
    any relation in which each test's verdict on a mixed pair follows componentwise
    (`Rectangular`) — every biorthogonal is mix-closed (`rect_mix_in_biorth`, one generic line),
    and conservation is NOT mix-closed: `(δ−1,δ+1)` and `(δ−2,δ+2)` both conserve but the mix
    `(δ−1,δ+2)` does not. So `conservation_not_behaviour_rectangular`: NO rectangular
    orthogonality, however rich its atoms, can carve the resource law. Componentwise testing is
    structurally blind to CORRELATION — that is precisely what biorthogonality misses about
    resources when its tests are per-turn. (Instantiated at the LIVE gate:
    `conservation_not_behaviour_live_pairs`, pairs of `SlotCaveat` tests.)
  * **THE RECOVERY.** Field the deployed pair-observable as a test — the `Σδ` comparator, exactly
    the `valTotal` observable `move_conserves` is stated in — and conservation IS an orthogonal,
    hence a behaviour: `conservation_is_behaviour` (`Cons = {Σδ ≥ 0, Σδ ≤ 0}^⊥ = Cons^⊥⊥`).
    Moreover conservation is EXACTLY the biorthogonal closure of the matched-delta pre-tensors
    (`conservation_eq_closure_of_matched_tensors`: `Cons = (⋃ₖ Δₖ ⊙ Δ₋ₖ)^⊥⊥`), and each matched
    tensor `Δₖ ⊗ Δ₋ₖ` lands inside it (`matched_tensor_subset_conservation`) — the linear face,
    decomposed through `⊗`. Non-vacuity both polarities: `conservation_proper` (a member, a
    non-member, the closure), and `pair_closure_grows` (a two-element conserving candidate whose
    closure STRICTLY grows — by re-pairing matched deltas — so the closure does real work here too).
  * **THE HEADLINE** (`linearity_recovered_from_orthogonality`): linearity is recovered from
    orthogonality IFF the test side may CORRELATE the components. The refutation of
    non-conservation is itself a relational (sum-reading) witness; rectangles can never field it.
    This is `docs/EPISTEMIC-DATALOG.md`'s fact/fiction line made formal: the resource law lies
    OUTSIDE every per-turn (rectangular) testing fragment and INSIDE the composite-test fragment,
    with the deployed `valTotal` observable as the one test that crosses the line.

## TARGET 2 — DOES THE COORDINATION GRADING EMERGE? VERDICT: **PARTIAL — and the conjectured
form REFUTED.**

  * **The conjectured shape is the WRONG one.** "Coordination-free ⟺ behaviour closed under
    DIRECTED union" (the CALM/Scott shape) FAILS in dregg's deployed lattices: every nonempty
    directed subset of `Budget` with a LUB ATTAINS it (`budget_directed_lub_attained` — bounded
    ℕ-valued coordinates), so directed-lub-closure holds VACUOUSLY for every subset
    (`directedLubClosed_vacuous`) — including the admission set of the bounded `budgetGuard`,
    which FORCES ORDERING (`directed_conjecture_refuted`). Directedness models one growing view;
    coordination cost is about DIVERGENT (incomparable) replicas. The two notions split exactly
    there.
  * **What the tier actually IS, structurally**: closure under PAIRWISE joins of (possibly
    incomparable) members — `free_iff_joinClosed`, definitionally `IConfluent`. The tier is a
    closure property of the admission SET, not a stapled-on label.
  * **The grading EMERGES on the test side of `^⊥` — soundly, not completely.** A test is
    JOIN-STABLE if its survivor set is join-closed; join-stability is inherited through the
    orthogonality (`coOrth_joinClosed`: an orthogonal of join-stable tests is join-closed), so any
    guard whose admission set is presented as `X^⊥` over join-stable tests is PROVED
    coordination-free (`behaviour_grade_sound`; the monotone pole re-derived purely through the
    orthogonality: `markGuard_grade_emerges`). The bounded pole's ceiling test is NOT join-stable
    (`ceiling_test_not_joinStable`) and its guard indeed forces ordering. But the grading is NOT
    complete: a behaviour over a family CONTAINING the unstable ceiling test can still be free
    (`grading_incomplete`) — the grade is a sound TYPE DISCIPLINE on `^⊥` (an upper bound on
    cost), not a semantic readout. S4's "coordination price as a modality on `^⊥`" is exactly the
    sound direction; the tier-1 verdict for an arbitrary guard remains `free_iff_joinClosed`
    (semantic), as `relational_decided_by_merge` already said.

## The honest bottom line

The bridge is LOAD-BEARING for the linear face — conservation is forced by the orthogonality once
(and only once) the test language is composite, and the boundary theorem is two-sided, not a
costume. The coordination grading is HALF-derived: sound through `^⊥`, semantically completed by
the join, and the CALM-flavored directed-union story is refuted on the deployed lattices.

No `sorry`, no `:= True`, no `native_decide`; every keystone `#assert_axioms`-pinned.
-/
import Dregg2.Calculus.Biorthogonality
import Mathlib.Data.Set.Prod
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Directed
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FinCases

namespace Dregg2.Calculus.Biorth

open Dregg2.Exec

/-! ## §1 — Generic layer: closure monotonicity, the with/⊗ distinction, the tensor, rectangles. -/

variable {T R : Type*}

/-- The biorthogonal closure is monotone (antitone ∘ antitone). -/
theorem biorth_mono (perp : T → R → Prop) {S₁ S₂ : Set T} (h : S₁ ⊆ S₂) :
    biorth perp S₁ ⊆ biorth perp S₂ :=
  coOrth_antitone perp (orthSet_antitone perp h)

/-- **The union-of-refutations form is the ADDITIVE `&`, not the tensor.**
`(A^⊥ ∪ B^⊥)^⊥ = A^⊥⊥ ∩ B^⊥⊥` over ONE universe (instance of `coOrth_union`) — the behaviour
MEET. The multiplicative `⊗` requires the COMPOSITE universe (`tensor` below, stella §69.35–36):
same-universe union of refutations can never be the tensor. -/
theorem orth_union_is_with (perp : T → R → Prop) (A B : Set T) :
    coOrthSet perp (orthSet perp A ∪ orthSet perp B) = biorth perp A ∩ biorth perp B :=
  coOrth_union perp _ _

section Tensor

variable {T₁ T₂ : Type*}

/-- **The tensor of two classes** over the composite universe: the biorthogonal closure of the
pre-tensor `A ⊙ B = A ×ˢ B` (stella's `pre_tensor`/`tensor`, `mll.rs` §69.35–36), under a
composite-test relation `perp : T₁ × T₂ → R → Prop`. The test side is allowed to CORRELATE the
components — that freedom is the whole question of §3. -/
def tensor (perp : T₁ × T₂ → R → Prop) (A : Set T₁) (B : Set T₂) : Set (T₁ × T₂) :=
  biorth perp (A ×ˢ B)

/-- The tensor is always a behaviour (it is a biorthogonal). -/
theorem tensor_isBehaviour (perp : T₁ × T₂ → R → Prop) (A : Set T₁) (B : Set T₂) :
    IsBehaviour perp (tensor perp A B) :=
  biorth_isBehaviour perp (A ×ˢ B)

/-- The pre-tensor sits inside the tensor (closure is extensive). -/
theorem subset_tensor (perp : T₁ × T₂ → R → Prop) (A : Set T₁) (B : Set T₂) :
    A ×ˢ B ⊆ tensor perp A B :=
  subset_biorth perp (A ×ˢ B)

/-- The tensor is monotone in both arguments. -/
theorem tensor_mono (perp : T₁ × T₂ → R → Prop) {A A' : Set T₁} {B B' : Set T₂}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    tensor perp A B ⊆ tensor perp A' B' :=
  biorth_mono perp (Set.prod_mono hA hB)

/-- **A RECTANGULAR composite-test relation**: every test's verdict on the MIXED pair
`(a.1, b.2)` follows from its verdicts on `a` and `b` — the shape of every per-component family
(a test reads the src write, or the dst write, or any conjunction of one-sided reads), for ANY
test type. This is the hypothesis under which biorthogonality is provably blind to correlation. -/
def Rectangular (perp : T₁ × T₂ → R → Prop) : Prop :=
  ∀ (r : R) (a b : T₁ × T₂), perp a r → perp b r → perp (a.1, b.2) r

/-- Pairing two one-sided relations is rectangular (the canonical instance). -/
theorem prodPerp_rectangular {R₁ R₂ : Type*} (p₁ : T₁ → R₁ → Prop) (p₂ : T₂ → R₂ → Prop) :
    Rectangular (fun (t : T₁ × T₂) (r : R₁ × R₂) => p₁ t.1 r.1 ∧ p₂ t.2 r.2) :=
  fun _ _ _ ha hb => ⟨ha.1, hb.2⟩

/-- **The generic mix law: under a rectangular relation, every biorthogonal closure contains the
mixed corner.** One line — the obstruction needs nothing about the atoms. -/
theorem rect_mix_in_biorth {perp : T₁ × T₂ → R → Prop} (hrect : Rectangular perp)
    {S : Set (T₁ × T₂)} {a b : T₁ × T₂} (ha : a ∈ S) (hb : b ∈ S) :
    (a.1, b.2) ∈ biorth perp S :=
  fun r hr => hrect r a b (hr a ha) (hr b hb)

end Tensor

/-! ## §2 — The MOVE universe: composite turns, the Σδ = 0 class, the witnesses. -/

namespace Mv

open Cav

/-- The resource delta of one guarded write, as the live caveat gate observes it
(`Cav.CTurn` is `SlotCaveat.eval`'s exact domain). -/
def delta (c : CTurn) : Int := c.new - c.old

/-- **A composite MOVE: the PAIRED writes** — a debit at src, a credit at dst (the `move` verb's
state shape, `VerbCompression.moveStep`: two openings changed by cancelling deltas). -/
abbrev Move := CTurn × CTurn

/-- The pair's total delta — the `valTotal` observable `move_conserves` is stated in
(`VerbCompression.move_conserves`: `valTotal m' = valTotal m`, i.e. `Σδ = 0`). -/
def sumDelta (m : Move) : Int := delta m.1 + delta m.2

/-- **CONSERVATION** — the linear resource class: the pair's deltas cancel
(`reachable_total_zero`'s per-asset law, at the granularity of one composite move). -/
def Cons : Set Move := {m | sumDelta m = 0}

/-! ### The concrete writes (all four deltas live in the demos below). -/

/-- A debit write at src cell 1: `10 → 9`, δ = −1. -/
def w : CTurn := ⟨1, 10, 9⟩
/-- The matching credit at dst cell 2: `0 → 1`, δ = +1. -/
def v : CTurn := ⟨2, 0, 1⟩
/-- A second debit at src cell 1: `10 → 8`, δ = −2. -/
def w₂ : CTurn := ⟨1, 10, 8⟩
/-- Its matching credit at dst cell 2: `0 → 2`, δ = +2. -/
def v₂ : CTurn := ⟨2, 0, 2⟩

/-- `(w, v)` conserves (δ −1 + 1 = 0). -/
theorem wv_mem : (w, v) ∈ Cons := (by decide : sumDelta (w, v) = 0)

/-- `(w₂, v₂)` conserves (δ −2 + 2 = 0). -/
theorem w2v2_mem : (w₂, v₂) ∈ Cons := (by decide : sumDelta (w₂, v₂) = 0)

/-- The MIXED pair `(w, v₂)` does NOT conserve (δ −1 + 2 = 1 ≠ 0). -/
theorem mix_not_conserves : ((w, v₂) : Move) ∉ Cons := by
  intro h
  have h' : sumDelta (w, v₂) = 0 := h
  exact absurd h' (by decide)

/-! ### §2(a) — THE OBSTRUCTION: no rectangular family can carve conservation. -/

/-- **`conservation_not_behaviour_rectangular` — THE NEGATIVE HALF, fully general.** For EVERY
test type `R` and EVERY rectangular composite-test relation (every per-component family,
however rich its atoms), conservation is NOT a behaviour: its closure must contain the mixed
corner `(w, v₂)` of the conserving pairs `(w, v)`, `(w₂, v₂)` — and the mix has Σδ = 1.
Componentwise testing is structurally blind to the correlation linearity IS. -/
theorem conservation_not_behaviour_rectangular
    {R : Type*} (perp : Move → R → Prop) (hrect : Rectangular perp) :
    ¬ IsBehaviour perp Cons := by
  intro h
  have hmix : ((w, v₂) : Move) ∈ biorth perp Cons :=
    rect_mix_in_biorth hrect wv_mem w2v2_mem
  rw [show biorth perp Cons = Cons from h] at hmix
  exact mix_not_conserves hmix

/-- The live-gate instance: PAIRS of `SlotCaveat` tests (one on each write — the deployed
per-component gate, doubled) cannot carve conservation. -/
def cavPairPerp (m : Move) (r : SlotCaveat × SlotCaveat) : Prop :=
  Cav.Survives m.1 r.1 ∧ Cav.Survives m.2 r.2

theorem cavPair_rectangular : Rectangular cavPairPerp :=
  fun _ _ _ ha hb => ⟨ha.1, hb.2⟩

/-- **The deployed caveat surface, paired componentwise, cannot see the resource law.** -/
theorem conservation_not_behaviour_live_pairs : ¬ IsBehaviour cavPairPerp Cons :=
  conservation_not_behaviour_rectangular cavPairPerp cavPair_rectangular

/-! ### §2(b) — THE RECOVERY: field the deployed pair-observable as a test. -/

/-- **The composite test family**: the live per-component caveats PLUS the pair's one deployed
RELATIONAL observable — the `Σδ` comparator (the `valTotal` reading `move_conserves` is stated
in), fielded fail-closed in both directions. A refutation of conservation IS a sum-reading
witness; this family is the smallest honest home for it. -/
inductive MoveTest where
  /-- a slot-caveat test on the src write (the live gate, componentwise). -/
  | onSrc (r : SlotCaveat)
  /-- a slot-caveat test on the dst write. -/
  | onDst (r : SlotCaveat)
  /-- the pair observable, lower half: survive iff `k ≤ Σδ`. -/
  | sumGe (k : Int)
  /-- the pair observable, upper half: survive iff `Σδ ≤ k`. -/
  | sumLe (k : Int)

/-- The Bool evaluator (the per-component arms are the verbatim live `SlotCaveat.eval`). -/
def msurvB (m : Move) : MoveTest → Bool
  | .onSrc r => Cav.survivesB m.1 r
  | .onDst r => Cav.survivesB m.2 r
  | .sumGe k => decide (k ≤ sumDelta m)
  | .sumLe k => decide (sumDelta m ≤ k)

/-- `m ⊥ r` over composite moves. Decidable. -/
def MSurvives (m : Move) (r : MoveTest) : Prop := msurvB m r = true

instance (m : Move) (r : MoveTest) : Decidable (MSurvives m r) :=
  inferInstanceAs (Decidable (msurvB m r = true))

/-- **Conservation IS an orthogonal**: `Cons = {Σδ ≥ 0, Σδ ≤ 0}^⊥` — the conservation class is
exactly the common-survivor set of the two halves of the deployed pair observable. -/
theorem Cons_eq_coOrth :
    Cons = coOrthSet MSurvives {MoveTest.sumGe 0, MoveTest.sumLe 0} := by
  ext m
  constructor
  · intro hm r hr
    have hs : sumDelta m = 0 := hm
    have hr' : r = .sumGe 0 ∨ r = .sumLe 0 := hr
    rcases hr' with rfl | rfl
    · show decide ((0 : Int) ≤ sumDelta m) = true
      exact decide_eq_true (le_of_eq hs.symm)
    · show decide (sumDelta m ≤ (0 : Int)) = true
      exact decide_eq_true (le_of_eq hs)
  · intro h
    have h₁ : decide ((0 : Int) ≤ sumDelta m) = true := h (MoveTest.sumGe 0) (Or.inl rfl)
    have h₂ : decide (sumDelta m ≤ (0 : Int)) = true := h (MoveTest.sumLe 0) (Or.inr rfl)
    exact le_antisymm (of_decide_eq_true h₂) (of_decide_eq_true h₁)

/-- **`conservation_is_behaviour` — THE POSITIVE HALF.** With the deployed pair observable
fielded as a test, conservation equals its own double-orthogonal: the LINEAR resource class is a
behaviour — forced by the orthogonality, exactly as the bridge conjectured, and exactly where the
rectangular theorem says it could not happen without correlated tests. -/
theorem conservation_is_behaviour : IsBehaviour MSurvives Cons := by
  rw [Cons_eq_coOrth]
  exact coOrth_isBehaviour MSurvives _

/-- Non-vacuity (TRUE polarity): conservation is a PROPER behaviour — a member, a non-member,
and the closure. -/
theorem conservation_proper :
    (w, v) ∈ Cons ∧ ((w, v₂) : Move) ∉ Cons ∧ IsBehaviour MSurvives Cons :=
  ⟨wv_mem, mix_not_conserves, conservation_is_behaviour⟩

/-! ### Non-vacuity (FALSE polarity): the closure does real work in THIS family too.

A two-element conserving candidate `{(w,v), (u,z)}` (two matched-delta moves) is NOT a behaviour:
its closure adds the RE-PAIRING `(w, z)` — still conserving (consistent with
`conservation_is_behaviour`), but a genuinely new element. The composite family identifies a
candidate up to its observable content; what it adds is conservation-compatible, never more. -/

/-- A second δ = −1 debit (different magnitudes: `7 → 6`). -/
def u : CTurn := ⟨1, 7, 6⟩
/-- A second δ = +1 credit (`6 → 7`). -/
def z : CTurn := ⟨2, 6, 7⟩

/-- The candidate's first move. -/
def p : Move := (w, v)
/-- The candidate's second move. -/
def q : Move := (u, z)
/-- The RE-PAIRING the closure must add: src write of `p`, dst write of `q` (Σδ = 0). -/
def trep : Move := (w, z)

/-- Every test both `p` and `q` survive, the re-pairing survives: per-component tests see a
component of `p` or of `q`; the sum tests see Σδ = 0, shared by all three. -/
theorem repair_in_closure : trep ∈ biorth MSurvives ({p, q} : Set Move) := by
  intro r hr
  have hp : MSurvives p r := hr p (Or.inl rfl)
  have hq : MSurvives q r := hr q (Or.inr rfl)
  cases r with
  | onSrc c => exact hp
  | onDst c => exact hq
  | sumGe k =>
      have hp' : decide (k ≤ sumDelta p) = true := hp
      have hk : k ≤ sumDelta p := of_decide_eq_true hp'
      have hp0 : sumDelta p = 0 := by decide
      have ht0 : sumDelta trep = 0 := by decide
      show decide (k ≤ sumDelta trep) = true
      exact decide_eq_true (by omega)
  | sumLe k =>
      have hp' : decide (sumDelta p ≤ k) = true := hp
      have hk : sumDelta p ≤ k := of_decide_eq_true hp'
      have hp0 : sumDelta p = 0 := by decide
      have ht0 : sumDelta trep = 0 := by decide
      show decide (sumDelta trep ≤ k) = true
      exact decide_eq_true (by omega)

theorem trep_not_in_pair : trep ∉ ({p, q} : Set Move) := by
  intro h
  have h' : trep = p ∨ trep = q := h
  rcases h' with h | h
  · exact absurd (congrArg (fun m : Move => m.2.old) h) (by decide)
  · exact absurd (congrArg (fun m : Move => m.1.old) h) (by decide)

/-- **Non-vacuity (FALSE polarity)**: `{p, q}` is not a behaviour — its closure strictly grows
(the re-pairing enters). The S2-style closure is not vacuous over composites either. -/
theorem pair_closure_grows :
    trep ∈ biorth MSurvives ({p, q} : Set Move)
      ∧ trep ∉ ({p, q} : Set Move)
      ∧ ¬ IsBehaviour MSurvives ({p, q} : Set Move) :=
  ⟨repair_in_closure, trep_not_in_pair, fun h => trep_not_in_pair (h ▸ repair_in_closure)⟩

/-! ### §2(c) — The ⊗-decomposition: conservation = the closure of the matched-delta tensors. -/

/-- The single-write delta class `Δₖ`. -/
def DeltaIs (k : Int) : Set CTurn := {c | delta c = k}

/-- Conservation is exactly the union of the matched-delta PRE-tensors `Δₖ ⊙ Δ₋ₖ`. -/
theorem cons_eq_union_matched :
    Cons = ⋃ k : Int, (DeltaIs k ×ˢ DeltaIs (-k)) := by
  ext m
  simp only [Cons, sumDelta, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, DeltaIs]
  constructor
  · intro h
    exact ⟨delta m.1, rfl, by omega⟩
  · rintro ⟨k, h1, h2⟩
    omega

/-- **Each matched-delta tensor lands inside conservation**: `Δₖ ⊗ Δ₋ₖ ⊆ Cons` — the closure of
a matched pre-tensor adds nothing non-conserving (conservation is a behaviour, so closure cannot
escape it). The `⊗`-shaped containment of the linear face. -/
theorem matched_tensor_subset_conservation (k : Int) :
    tensor MSurvives (DeltaIs k) (DeltaIs (-k)) ⊆ Cons := by
  have hsub : DeltaIs k ×ˢ DeltaIs (-k) ⊆ Cons := by
    rintro ⟨a, b⟩ ⟨h1, h2⟩
    have h1' : delta a = k := h1
    have h2' : delta b = -k := h2
    show delta a + delta b = 0
    omega
  have hmono := biorth_mono MSurvives hsub
  rw [show biorth MSurvives Cons = Cons from conservation_is_behaviour] at hmono
  exact hmono

/-- **Conservation IS the behaviour generated by the matched tensors**:
`Cons = (⋃ₖ Δₖ ⊙ Δ₋ₖ)^⊥⊥` — the linear class is the biorthogonal closure of the family of
matched-delta pre-tensors. The tensor decomposition, exact. -/
theorem conservation_eq_closure_of_matched_tensors :
    Cons = biorth MSurvives (⋃ k : Int, DeltaIs k ×ˢ DeltaIs (-k)) := by
  rw [← cons_eq_union_matched]
  exact conservation_is_behaviour.symm

/-! ### §2(d) — THE HEADLINE. -/

/-- **`linearity_recovered_from_orthogonality` — THE T1 VERDICT.**
(1) With the deployed pair observable (`valTotal`'s Σδ) fielded as a test, CONSERVATION IS A
BEHAVIOUR — the linear face is recovered from orthogonality over the composite universe;
(2) it is EXACTLY the closure of the matched-delta tensors — the `⊗`-decomposition is exact;
(3) and NO rectangular (per-component) test family, over ANY test type, can carve it — the
boundary is two-sided. Linearity is recovered from orthogonality IFF the test side may correlate
the pair: the resource law lives outside every per-turn testing fragment and exactly at the
deployed composite observable. -/
theorem linearity_recovered_from_orthogonality :
    IsBehaviour MSurvives Cons
      ∧ Cons = biorth MSurvives (⋃ k : Int, DeltaIs k ×ˢ DeltaIs (-k))
      ∧ ∀ {R : Type} (perp : Move → R → Prop), Rectangular perp → ¬ IsBehaviour perp Cons :=
  ⟨conservation_is_behaviour, conservation_eq_closure_of_matched_tensors,
   fun perp h => conservation_not_behaviour_rectangular perp h⟩

end Mv

/-! ## §3 — TARGET 2: the coordination grading against the behaviour structure. -/

namespace Grading

open Dregg2.Authority.ConfluenceClassifier
open Dregg2.Confluence
open Dregg2.Confluence.CRDT

variable {S R : Type*}

/-- Closure of a set under pairwise joins of members (over possibly INCOMPARABLE pairs — the
divergent-replica shape, NOT the directed/one-growing-view shape). -/
def JoinClosed [SemilatticeSup S] (A : Set S) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ⊔ y ∈ A

/-- **The coordination price IS pairwise-join closure of the admission set** — `modality_price`
(`= guardKeepsConfluence = IConfluent`) restated as a closure property of the SET the guard
admits. The tier is structural, not stapled on. -/
theorem price_iff_joinClosed [MergeState S] (g : Guard S) :
    modality_price g ↔ JoinClosed {s | guardInv g s} := by
  constructor
  · intro h x hx y hy
    exact h x y hx hy
  · intro h x y hx hy
    exact h x hx y hy

/-- The tier-1 verdict, as the closure property: `CoordinationFree g ↔ JoinClosed (Adm g)`. -/
theorem free_iff_joinClosed [MergeState S] (g : Guard S) :
    CoordinationFree g ↔ JoinClosed {s | guardInv g s} :=
  (keeps_iff_coordinationFree g).symm.trans (price_iff_joinClosed g)

/-! ### §3(a) — The grading EMERGES on the test side of `^⊥` (the sound direction). -/

/-- **A JOIN-STABLE test**: its survivor set is join-closed. The coordination grade of a single
refutation — the "modality on `^⊥`" S4 asked for. -/
def JoinStable [SemilatticeSup S] (perp : S → R → Prop) (r : R) : Prop :=
  ∀ x y : S, perp x r → perp y r → perp (x ⊔ y) r

/-- **Join-stability is inherited through the orthogonality**: the orthogonal of any set of
join-stable tests is join-closed (an intersection of join-closed survivor sets). The grade of a
behaviour is computed on its tests and INHERITED through `^⊥` — this is the structural emergence. -/
theorem coOrth_joinClosed [SemilatticeSup S] (perp : S → R → Prop) (X : Set R)
    (h : ∀ r ∈ X, JoinStable perp r) :
    JoinClosed (coOrthSet perp X) :=
  fun x hx y hy r hr => h r hr x y (hx r hr) (hy r hr)

/-- **`behaviour_grade_sound` — the EMERGENCE theorem (sound direction).** A guard whose
admission set is presented as the orthogonal of join-stable tests is PROVED coordination-free:
the tier-1 verdict follows from the orthogonality presentation alone. The I-confluence tier, for
such guards, is derived — not assembled. -/
theorem behaviour_grade_sound [MergeState S] (g : Guard S) (perp : S → R → Prop) (X : Set R)
    (hadm : {s | guardInv g s} = coOrthSet perp X)
    (hstable : ∀ r ∈ X, JoinStable perp r) :
    CoordinationFree g := by
  rw [free_iff_joinClosed, hadm]
  exact coOrth_joinClosed perp X hstable

/-- The floor-observer test family on `ℕ` (the monotone pole's tests): survive `k` iff `k ≤ s`. -/
def floorPerp : ℕ → ℕ → Prop := fun s k => k ≤ s

/-- **Non-vacuity (TRUE polarity): the monotone pole's verdict EMERGES through `^⊥`.** The
high-water-mark guard's admission set is the orthogonal of the (join-stable) floor test, so
`behaviour_grade_sound` re-derives `markGuard_runs_free` purely from the orthogonality
presentation — no appeal to the classifier's syntactic monotone arm. -/
theorem markGuard_grade_emerges : CoordinationFree Witness.markGuard := by
  refine behaviour_grade_sound Witness.markGuard floorPerp {3} ?_ ?_
  · ext s
    constructor
    · intro hs k hk
      have hk3 : k = 3 := hk
      subst hk3
      exact hs
    · intro h
      exact h 3 rfl
  · intro k _ x y hx _
    exact le_trans hx le_sup_left

/-! ### §3(b) — Incompleteness: the grade is a sound type discipline, not a semantic readout. -/

/-- A two-test family over the deployed `Budget`: the bounded CEILING test (`consumed ≤ 1`, the
live bounded pole) and a PIN test (`= ⊥`). -/
def budgetPerp (b : Budget) : Bool → Prop
  | true  => consumed b ≤ 1
  | false => b = ⊥

/-- The ceiling test is NOT join-stable — the clashing split `(1,0) ⊔ (0,1) = (1,1)` (the same
witness as `budgetGuard_breaks`, at the single-test level). -/
theorem ceiling_test_not_joinStable : ¬ JoinStable budgetPerp true := by
  intro h
  have hbad := h Witness.splitX Witness.splitY
    (show consumed Witness.splitX ≤ 1 by decide)
    (show consumed Witness.splitY ≤ 1 by decide)
  have hno : ¬ consumed (Witness.splitX ⊔ Witness.splitY) ≤ 1 := by decide
  exact hno hbad

/-- **`grading_incomplete` — the converse FAILS.** A behaviour over a family CONTAINING the
non-join-stable ceiling test can still be join-closed (free): the pin test cuts the orthogonal
down to `{⊥}`, which is trivially join-closed. So the test-side grade is an UPPER BOUND on
coordination cost (sound), not a semantic readout (complete): the tier of an arbitrary guard
remains the semantic `free_iff_joinClosed` / `relational_decided_by_merge` question. -/
theorem grading_incomplete :
    JoinClosed (coOrthSet budgetPerp Set.univ)
      ∧ IsBehaviour budgetPerp (coOrthSet budgetPerp Set.univ)
      ∧ ¬ JoinStable budgetPerp true := by
  refine ⟨?_, coOrth_isBehaviour budgetPerp Set.univ, ceiling_test_not_joinStable⟩
  intro x hx y hy
  have hx1 : x = ⊥ := hx false (Set.mem_univ _)
  have hy1 : y = ⊥ := hy false (Set.mem_univ _)
  subst hx1; subst hy1
  have hbb : (⊥ : Budget) ⊔ ⊥ = ⊥ := by simp
  rw [hbb]
  exact hx

/-- The discriminator FIRES on the bounded pole: the budget guard's admission set is NOT
join-closed (equivalently, `budgetGuard_breaks`, through `price_iff_joinClosed`). -/
theorem budget_admission_not_joinClosed :
    ¬ JoinClosed {b : Budget | guardInv Witness.budgetGuard b} := by
  intro h
  exact Witness.budgetGuard_breaks ((price_iff_joinClosed Witness.budgetGuard).mpr h)

/-! ### §3(c) — REFUTATION of the conjectured directed-union form.

The conjecture (`monotone_guard_iff_directed_closed`, the CALM/Scott shape): coordination-free ⟺
admission set closed under directed unions. In dregg's deployed lattices it FAILS, and for a
structural reason: a DIRECTED set models one growing view — any two members already reconcile
INSIDE the set — while coordination cost is about DIVERGENT (incomparable) replicas. Concretely,
in `Budget` (ℕ-valued coordinates) every nonempty directed set with a LUB ATTAINS it, so
directed-lub-closure holds for EVERY subset — including the bounded guard's, which forces
ordering. -/

/-- Closure under LUBs of nonempty directed subsets (the dcpo/Scott-continuity shape). -/
def DirectedLubClosed [Preorder S] (A : Set S) : Prop :=
  ∀ D : Set S, D.Nonempty → DirectedOn (· ≤ ·) D → D ⊆ A → ∀ s, IsLUB D s → s ∈ A

/-- **In the deployed lattice every nonempty directed set ATTAINS its LUB.** Each coordinate's
value set is a nonempty bounded set of naturals, so its sup is attained at some member;
directedness reconciles the two coordinate-maximizers inside `D`, and that reconciler equals the
LUB. -/
theorem budget_directed_lub_attained
    {D : Set Budget} (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    {s : Budget} (hs : IsLUB D s) : s ∈ D := by
  have hbdd : ∀ i : Fin 2, BddAbove ((fun f : Budget => f i) '' D) := by
    intro i
    refine ⟨s i, ?_⟩
    rintro a ⟨d, hd, rfl⟩
    exact hs.1 hd i
  have hattain : ∀ i : Fin 2, ∃ d ∈ D, ∀ e ∈ D, e i ≤ d i := by
    intro i
    obtain ⟨d, hd, hdi⟩ := Nat.sSup_mem (hne.image (fun f : Budget => f i)) (hbdd i)
    refine ⟨d, hd, fun e he => ?_⟩
    have h1 : e i ≤ sSup ((fun f : Budget => f i) '' D) := le_csSup (hbdd i) ⟨e, he, rfl⟩
    rw [← hdi] at h1
    exact h1
  obtain ⟨d₀, hd₀, hmax₀⟩ := hattain 0
  obtain ⟨d₁, hd₁, hmax₁⟩ := hattain 1
  obtain ⟨dT, hdT, h0T, h1T⟩ := hdir d₀ hd₀ d₁ hd₁
  have hub : dT ∈ upperBounds D := by
    intro e he i
    fin_cases i
    · exact le_trans (hmax₀ e he) (h0T 0)
    · exact le_trans (hmax₁ e he) (h1T 1)
  have h1 : s ≤ dT := hs.2 hub
  have h2 : dT ≤ s := hs.1 hdT
  exact le_antisymm h2 h1 ▸ hdT

/-- **Directed-lub-closure is VACUOUS on the deployed lattice**: EVERY subset of `Budget`
satisfies it (the LUB is always a member of the directed set itself). The CALM/Scott shape
cannot discriminate anything here. -/
theorem directedLubClosed_vacuous (A : Set Budget) : DirectedLubClosed A :=
  fun _D hne hdir hsub _s hs => hsub (budget_directed_lub_attained hne hdir hs)

/-- **`directed_conjecture_refuted` — the T2 conjecture is FALSE as stated.** The bounded
budget guard's admission set IS directed-lub-closed (vacuously), yet the guard FORCES ORDERING;
hence "directed-closed ⇒ coordination-free" fails (with this concrete witness). The correct
structural form is `free_iff_joinClosed` — pairwise joins over divergent replicas, which the
SAME admission set fails (`budget_admission_not_joinClosed`). -/
theorem directed_conjecture_refuted :
    (DirectedLubClosed {b : Budget | guardInv Witness.budgetGuard b}
        ∧ ForcesOrdering Witness.budgetGuard)
      ∧ ¬ ∀ g : Guard Budget,
            DirectedLubClosed {b | guardInv g b} → CoordinationFree g :=
  ⟨⟨directedLubClosed_vacuous _, Witness.budgetGuard_forces_ordering.1⟩,
   fun h => Witness.budgetGuard_breaks
     ((keeps_iff_coordinationFree Witness.budgetGuard).mpr
       (h Witness.budgetGuard (directedLubClosed_vacuous _)))⟩

/-- **The packaged T2 verdict**: the monotone pole's freedom EMERGES through `^⊥`
(join-stable tests, inherited); the join-closure discriminator fires on the bounded pole; the
directed-union (CALM) shape is blind on the very same admission set; and that set really does
force ordering. PARTIAL emergence, with the boundary exact. -/
theorem coordination_grading_verdict :
    CoordinationFree Witness.markGuard
      ∧ ¬ JoinClosed {b : Budget | guardInv Witness.budgetGuard b}
      ∧ DirectedLubClosed {b : Budget | guardInv Witness.budgetGuard b}
      ∧ ForcesOrdering Witness.budgetGuard :=
  ⟨markGuard_grade_emerges, budget_admission_not_joinClosed,
   directedLubClosed_vacuous _, Witness.budgetGuard_forces_ordering.1⟩

end Grading

/-! ## §4 — Computational spot-checks (both polarities, executable). -/

-- a conserving pair passes the Σδ gate, both halves:
#guard Mv.msurvB (Mv.w, Mv.v) (.sumGe 0) && Mv.msurvB (Mv.w, Mv.v) (.sumLe 0)
-- the non-conserving mix is REFUTED by the upper half (Σδ = 1):
#guard !(Mv.msurvB (Mv.w, Mv.v₂) (.sumLe 0))
#guard decide (Mv.sumDelta (Mv.w, Mv.v₂) = 1)
-- the re-pairing really conserves (the false-polarity growth stays inside conservation):
#guard decide (Mv.sumDelta Mv.trep = 0)
-- per-component arms are the verbatim live gate:
#guard Mv.msurvB (Mv.w, Mv.v) (.onSrc (.boundedBy "x" 0 100))
#guard !(Mv.msurvB (Mv.w, Mv.v) (.onSrc (.monotonic "x")))   -- a debit is not monotone

/-! ## §5 — Axiom hygiene. -/

-- §1 the generic layer
#assert_axioms biorth_mono
#assert_axioms orth_union_is_with
#assert_axioms tensor_isBehaviour
#assert_axioms subset_tensor
#assert_axioms tensor_mono
#assert_axioms prodPerp_rectangular
#assert_axioms rect_mix_in_biorth
-- §2 T1: the obstruction + the recovery + the decomposition + the headline
#assert_axioms Mv.conservation_not_behaviour_rectangular
#assert_axioms Mv.conservation_not_behaviour_live_pairs
#assert_axioms Mv.Cons_eq_coOrth
#assert_axioms Mv.conservation_is_behaviour
#assert_axioms Mv.conservation_proper
#assert_axioms Mv.repair_in_closure
#assert_axioms Mv.pair_closure_grows
#assert_axioms Mv.cons_eq_union_matched
#assert_axioms Mv.matched_tensor_subset_conservation
#assert_axioms Mv.conservation_eq_closure_of_matched_tensors
#assert_axioms Mv.linearity_recovered_from_orthogonality
-- §3 T2: the structural tier + the emergence + the incompleteness + the refutation
#assert_axioms Grading.price_iff_joinClosed
#assert_axioms Grading.free_iff_joinClosed
#assert_axioms Grading.coOrth_joinClosed
#assert_axioms Grading.behaviour_grade_sound
#assert_axioms Grading.markGuard_grade_emerges
#assert_axioms Grading.ceiling_test_not_joinStable
#assert_axioms Grading.grading_incomplete
#assert_axioms Grading.budget_admission_not_joinClosed
#assert_axioms Grading.budget_directed_lub_attained
#assert_axioms Grading.directedLubClosed_vacuous
#assert_axioms Grading.directed_conjecture_refuted
#assert_axioms Grading.coordination_grading_verdict

end Dregg2.Calculus.Biorth
