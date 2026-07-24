/-
# `Dregg2.Crypto.PolyTimeRomBridge` — THE KEYSTONE: every proved random-oracle floor, PROMOTED
from the query-bounded class to the FULL poly-time class.

## The situation this file answers

The tree PROVES three ROM floors, each against a QUERY-BOUNDED class, each carrying the same
named residual — "this holds against query-bounded adversaries, not against all poly-time ones":

  * BINDING / collision: `RomQueryFloor.birthday_bound` (364) and `romCollision_hard` (508), at
    the class `RomEff` (442) — adversaries that factor through a `Q`-query
    `RomOracle.OracleComp` tree (`QueryBounded`, RomOracle 68).
  * KEYED collision: `KeyedRomFloor.keyedRom_hard` (162), at `KeyedRomEff` (152).
  * Two-world HIDING: `KeyedRomHidingFloor.hidingAdv_le` (592) and `keyedRomHiding_hard` (930),
    at `QueryHiding` (413) / `KeyedRomHidingEff` (913).

Separately, `CostAdversary` builds the deep-embedded COST MODEL: a `FreeOracle` program whose
cost VECTOR `⟨intr, qry⟩` is DERIVED FROM ITS SYNTAX (`FreeOracle.cost`, 345), with `PolyTime`
(594) and the exact factorization `polyTime_iff_intr_and_queries` (661): poly-time = poly
intrinsic work AND poly per-oracle query counts (`PolyQueries`, 605).

## THE BRIDGE

`toOracleComp_queryBounded`: translating a single-oracle `FreeOracle` program into an
`OracleComp` query tree is QUERY-COUNT-PRESERVING — the tree is `QueryBounded` by EXACTLY the
program's syntactic `qry` component, and evaluation commutes with denotation
(`toOracleComp_eval`). Hence a poly-time program — whose `qry` component is poly by the
`polyTime_iff` factorization (here `romPolyTime_iff_intr_and_queries`, same proof over the same
`Cost` lemmas) — FACTORS THROUGH a `Q`-query tree for polynomial `Q`
(`polyTime_to_queryBounded`). Composing with the three proved floors promotes each to the full
poly-time class: `binding_polyTime`, `collision_polyTime`, `hiding_polyTime`.

## ⚑ THE ONE TYPE-SHAPE DECISION THAT MAKES THE PROMOTION HONEST

`CostAdversary.IsPolyTime` (934) hands the program the INSTANCE as data. At a ROM game the
instance IS the sampled oracle, so an instance-passing "poly-time" program can `.pure`-hardcode
an answer read off the oracle it was handed — that class prices answer SIZE, never search
difficulty, and its floor is REFUTED in-tree (`sysRoots_floor_polyTime_false_babyBear`; the
disease `KeyedRomFloor`'s header documents). The honest poly-time ROM adversary accesses the
oracle ONLY through the cost model's ORACLE INTERFACE: `RomCostAdversary.prog` is a `FreeOracle`
program with NO instance input whose ONE oracle is the random oracle, so every bit it learns of
`H` is a `query` node COUNTED IN ITS SYNTAX (`cost` cannot be faked — it is a function of the
program). That is the standard PPT-with-oracle-access shape, and it is what makes "poly-time ⇒
poly-many queries" a THEOREM here rather than a false claim.

## The distinguisher partner (two-world hiding)

`CostDistinguisher` extends the cost model to the two-world hiding game: `msg0`/`msg1` fixed up
front and a CHALLENGE-INDEXED `FreeOracle` program — the challenge digest is data (it is handed
to the adversary), the oracle is queried, and the hidden blinding is NEVER an input (the induced
`HidingDistinguisher.accept` ignores `r` BY CONSTRUCTION — a cost program structurally cannot
read the experiment tape). `IsPolyTimeDist` is the induced PPT distinguisher class over
`FamilyHidingDistinguisher`, and `hiding_polyTime` is the two-world hiding floor against it.
The generic `FreeOracle` cost machinery (`cost_bind_le_lin`, `cost_postMapProg_tight`,
`polyTime_postMapProg`) applies to these programs UNCHANGED — nothing needed re-porting, because
`CostAdversary`'s composition layer is stated at the program level, not the game level.

## HONEST RESIDUAL — what this bridge does and does NOT discharge

This module upgrades the ADVERSARY CLASS of three PROVED floors: query-bounded → full poly-time
(poly-time in the tree's deep-embedded cost model — worst-case, uniform, deterministic, exactly
`CostAdversary`'s stated design commitments). The ROM IDEALIZATION ITSELF — modeling the
deployed hash (the wide Poseidon2) as a uniformly sampled function — remains the ONE named
residual, exactly as `RomQueryFloor` and `KeyedRomHidingFloor` state it. It is NOT discharged
here, and nothing here claims security of the concrete hash outside that model. The promotion
direction is the sound one: the poly-time class is a SUBSET of the query-bounded class (a
`Q`-query tree may do unbounded work between queries; a poly-time program may not), so each
promoted floor is implied by its query-bounded parent — the content of this file is that the
implication is now a THEOREM with the poly-time class a REAL, inhabited, properly-restricted
class, not a parameter.

## Non-vacuity — both poles, at the deployed-shape families

  * ⊥ pole, collision: `binaryTwoPoint_polyTime` + `polyTimeRom_inhabited_with_advantage` — the
    genuine two-query finder IS a poly-time cost program and wins with positive advantage.
  * ⊤ pole, collision: `choiceAdv_not_polyTimeRom` — the `Classical.choice` full-oracle answerer
    is EXCLUDED from the poly-time class (else its advantage `1` would be negligible).
  * The QUERY component is load-bearing: `romQueryHog_not_polyTime` — a program with POLY
    intrinsic work and `2^l` queries is NOT in the class (the scalar-total collapse cannot
    happen at the ROM interface).
  * ⊥ pole, hiding: `oneQueryCostDist` + `polyTimeDist_inhabited_with_advantage` — the one-query
    distinguisher is a poly-time cost program with strictly positive hiding advantage.
  * ⊤ pole, hiding: `blindedTopFamily_not_polyTimeDist` — the full-tape `topAdv` family (which
    reads the hidden blinding) denotes to NO poly-time cost distinguisher.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. NEW ADDITIVE file; all imports read-only.
-/
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.KeyedRomHidingFloor
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.PolyTimeRomBridge

open Dregg2.Crypto.ConcreteSecurity
  (Negl PolyBounded PolyBoundedNat expBound expBound_not_ppt)
open Dregg2.Crypto.FloorGames
  (Game Adversary Hard gameAdv solvableFrac choiceAdv choiceAdv_gameAdv
   hard_top_iff_solvableFrac_negl)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor
  (RomFamily romCollisionGame RomComp romAdv RomEff romCollision_hard twoPointComp
   twoPointAdv_gameAdv_pos binaryRomFamily binaryRom_card_R binaryRom_top_false)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame KeyedRomEff keyedRom_hard)
open Dregg2.Crypto.KeyedRomHidingFloor
  (HidingDistinguisher QueryHiding hidingAdv HidingRomFamily FamilyHidingDistinguisher
   famHidingAdv KeyedRomHidingEff HidingHard keyedRomHiding_hard oneQueryAdv
   oneQueryAdv_hidingAdv_pos topAdv topAdv_hidingAdv blindedSpanRomFamily
   blindedSpanRom_card_B)
open Dregg2.Crypto.CostAdversary

set_option autoImplicit false

/-! ## §1 — THE BRIDGE CORE: the cost program's query tree, count-preservingly.

A single-oracle `FreeOracle` program erases to an `OracleComp` decision tree: `tick`s vanish
(they are the INTRINSIC cost, invisible to the oracle), `query` nodes translate one-for-one.
The two theorems that make this the keystone: evaluation commutes (`toOracleComp_eval`), and
the tree's query budget IS the program's syntactic `qry` count (`toOracleComp_queryBounded`). -/

/-- **Erase the intrinsic-work structure, keep the query structure.** A single-oracle
`FreeOracle` program as an `OracleComp` decision tree: `pure ↦ pure`, `tick k ↦ k` (intrinsic
work is invisible to the oracle), `query ↦ query`. -/
def toOracleComp {D R α : Type} :
    FreeOracle Unit (fun _ => D) (fun _ => R) α → OracleComp D R α
  | .pure a => .pure a
  | .tick k => toOracleComp k
  | .query _ q k => .query q (fun r => toOracleComp (k r))

/-- **EVALUATION COMMUTES WITH DENOTATION.** Running the erased tree against `H` is running the
program under the oracle `H`. So the tree and the program are the SAME adversary — the erasure
changes the bookkeeping, never the behaviour. -/
theorem toOracleComp_eval {D R α : Type}
    (m : FreeOracle Unit (fun _ => D) (fun _ => R) α) (H : D → R) :
    (toOracleComp m).eval H = FreeOracle.denote (fun _ q => H q) m := by
  induction m with
  | pure a => rfl
  | tick k ih => exact ih
  | query o q k ih => exact ih (H q)

/-- **⚑ THE BRIDGE CORE — the denotation is QUERY-COUNT-PRESERVING.** The erased tree is
`QueryBounded` by EXACTLY the program's syntactic per-oracle call count — the `qry` component of
`FreeOracle.cost`. This is the fact the whole promotion rides on: the cost model's query counter
and the ROM floors' query budget are the SAME number, so "poly-time ⇒ poly queries ⇒ in the
query-bounded class" has no gap in the middle. -/
theorem toOracleComp_queryBounded {D R α : Type} [Fintype R] (sz : α → ℕ)
    (m : FreeOracle Unit (fun _ => D) (fun _ => R) α) :
    QueryBounded ((FreeOracle.cost sz m).qry ()) (toOracleComp m) := by
  induction m with
  | pure a => exact QueryBounded.pure _ a
  | tick k ih =>
      simpa [toOracleComp, FreeOracle.cost_tick, Cost.add_qry, Cost.tickC_qry] using ih
  | query o q k ih =>
      cases o
      have hb : QueryBounded
          (Finset.univ.sup (fun r => (FreeOracle.cost sz (k r)).qry ()) + 1)
          (OracleComp.query q (fun r => toOracleComp (k r))) :=
        QueryBounded.query _ q _ (fun r =>
          (ih r).mono (Finset.le_sup (f := fun r => (FreeOracle.cost sz (k r)).qry ())
            (Finset.mem_univ r)))
      have hq : (FreeOracle.cost sz (FreeOracle.query (O := Unit)
            (Q := fun _ => D) (R := fun _ => R) () q k)).qry ()
          = Finset.univ.sup (fun r => (FreeOracle.cost sz (k r)).qry ()) + 1 := by
        simp [FreeOracle.cost_query, Cost.add_qry, Cost.callC_qry, Cost.supOver_qry,
          Nat.add_comm]
      rw [hq]
      exact hb

/-- The bridge core, slackened to any budget dominating the syntactic count. -/
theorem toOracleComp_queryBounded_of_le {D R α : Type} [Fintype R] (sz : α → ℕ)
    (m : FreeOracle Unit (fun _ => D) (fun _ => R) α) {n : ℕ}
    (hn : (FreeOracle.cost sz m).qry () ≤ n) : QueryBounded n (toOracleComp m) :=
  (toOracleComp_queryBounded sz m).mono hn

/-! ## §2 — the ORACLE-INTERFACED poly-time ROM adversary.

⚑ NOT `CostAdversary` at the ROM game. There `prog : ∀ l, G.Inst l → FreeOracle …` receives the
instance — and at a ROM game the instance IS the oracle, which is the refuted `IsPolyTime`
shape (answer-size pricing; `KeyedRomFloor` header). Here the program has NO instance input:
its ONE oracle IS the random oracle, so reading `H` costs a counted `query` node. -/

/-- **A COST-CARRYING ROM ADVERSARY.** One `FreeOracle` program per security parameter; the
single oracle (named by `Unit`) takes queries in `F.D l` and answers in `F.R l` — it IS the
random oracle. ⚑ EXACTLY ONE FIELD, and no instance input: the sampled oracle is not data the
program receives, it is the interface the program queries. -/
structure RomCostAdversary (F : RomFamily) where
  /-- The adversary's program at parameter `l`. Output: a candidate collision pair. -/
  prog : ∀ l, FreeOracle Unit (fun _ => F.D l) (fun _ => F.R l) (F.D l × F.D l)

/-- An answer-size measure for the collision answer (a pair of domain points) — the encoding
length the game charges at the `pure` leaf, per `CostAdversary`'s design commitment 4. -/
abbrev RomAnsSize (F : RomFamily) : Type := ∀ l, F.D l × F.D l → ℕ

/-- The program's syntactic cost vector at parameter `l`. -/
def RomCostAdversary.costAt {F : RomFamily} (A : RomCostAdversary F) (sz : RomAnsSize F)
    (l : ℕ) : Cost Unit :=
  letI := F.rFin l
  FreeOracle.cost (sz l) (A.prog l)

/-- **`RomPolyTime`** — the ROM program's total cost (intrinsic work + query count, unit oracle
price) is polynomially bounded. The mirror of `CostAdversary.PolyTime` (594) at the
oracle-interfaced type. -/
def RomPolyTime {F : RomFamily} (sz : RomAnsSize F) (A : RomCostAdversary F) : Prop :=
  ∃ C k : ℕ, ∀ l, (A.costAt sz l).total ≤ C * l ^ k + C

/-- The intrinsic half — poly instruction count (mirror of `PolyIntr`, 599). -/
def RomPolyIntr {F : RomFamily} (sz : RomAnsSize F) (A : RomCostAdversary F) : Prop :=
  ∃ C k : ℕ, ∀ l, (A.costAt sz l).intr ≤ C * l ^ k + C

/-- The query half — poly-many calls to the random oracle (mirror of `PolyQueries`, 605). This
is the component the bridge hands to `QueryBounded`. -/
def RomPolyQueries {F : RomFamily} (sz : RomAnsSize F) (A : RomCostAdversary F) : Prop :=
  ∃ C k : ℕ, ∀ l, (A.costAt sz l).qry () ≤ C * l ^ k + C

/-- **THE VECTOR IS THE OBJECT, at the ROM interface** — `RomPolyTime` factors EXACTLY into poly
intrinsic work and poly query count. Same proof as `polyTime_iff_intr_and_queries` (661), over
the same `Cost` lemmas; the `→` direction (total dominates each component) is what the bridge
consumes. -/
theorem romPolyTime_iff_intr_and_queries {F : RomFamily} (sz : RomAnsSize F)
    (A : RomCostAdversary F) :
    RomPolyTime sz A ↔ (RomPolyIntr sz A ∧ RomPolyQueries sz A) := by
  constructor
  · rintro ⟨C, k, h⟩
    exact ⟨⟨C, k, fun l => (Cost.intr_le_total _).trans (h l)⟩,
           ⟨C, k, fun l => (Cost.qry_le_total _ ()).trans (h l)⟩⟩
  · rintro ⟨⟨C₁, k₁, h₁⟩, ⟨C₂, k₂, h₂⟩⟩
    have hpoly : PolyBoundedNat (fun l => (C₁ * l ^ k₁ + C₁)
        + Fintype.card Unit * (C₂ * l ^ k₂ + C₂)) :=
      polyBoundedNat_add ⟨k₁, C₁, fun _ => le_rfl⟩
        (polyBoundedNat_const_mul _ ⟨k₂, C₂, fun _ => le_rfl⟩)
    obtain ⟨k, C, hC⟩ := hpoly
    exact ⟨C, k, fun l =>
      (Cost.total_le _ _ _ (h₁ l) (fun _ => h₂ l)).trans (hC l)⟩

/-- **Denotation to a raw adversary — the program RUN AGAINST THE SAMPLED ORACLE.** The game's
instance is `H`; the program's oracle is `H`. Contrast `CostAdversary.toAdversary` (692), which
runs under a default oracle because there the instance is separate data. -/
def RomCostAdversary.toAdversary {F : RomFamily} (A : RomCostAdversary F) :
    Adversary (romCollisionGame F) where
  run := fun l H => FreeOracle.denote (fun _ q => H q) (A.prog l)

/-- **⚑ THE FULL POLY-TIME ROM ADVERSARY CLASS** — a raw adversary is poly-time iff SOME
poly-time oracle-interfaced cost program denotes to it. This is the `Eff` the promoted floors
quantify over: PPT with oracle access, in the tree's deep-embedded cost model. -/
def IsPolyTimeRom (F : RomFamily) (sz : RomAnsSize F)
    (A : Adversary (romCollisionGame F)) : Prop :=
  ∃ B : RomCostAdversary F, B.toAdversary = A ∧ RomPolyTime sz B

/-! ## §3 — ⚑⚑⚑ THE BRIDGE: poly-time factors through the query-bounded class. -/

/-- A cost program with query count ≤ `Q l` is in `RomEff F Q`: its erased tree is the required
`Q`-query tree (bridge core), and it computes the same answers (`toOracleComp_eval`). -/
theorem romEff_of_queryBound {F : RomFamily} (B : RomCostAdversary F) (sz : RomAnsSize F)
    (Q : ℕ → ℕ) (hQ : ∀ l, (B.costAt sz l).qry () ≤ Q l) :
    RomEff F Q B.toAdversary := by
  refine ⟨fun l => letI := F.rFin l; toOracleComp (B.prog l), fun l => ?_, fun l H => ?_⟩
  · letI := F.rFin l
    exact toOracleComp_queryBounded_of_le (sz l) (B.prog l) (hQ l)
  · letI := F.rFin l
    exact (toOracleComp_eval (B.prog l) H).symm

/-- **⚑⚑⚑ THE KEYSTONE BRIDGE — `PolyTime ⇒ QueryBounded`.** Every poly-time ROM adversary IS a
query-bounded ROM adversary at a POLYNOMIAL budget: poly-time bounds the query component
(`romPolyTime_iff_intr_and_queries`), and the query component IS the erased tree's budget
(`toOracleComp_queryBounded`). This single implication promotes every `RomEff`-class floor to
the full poly-time class. -/
theorem polyTime_to_queryBounded {F : RomFamily} (sz : RomAnsSize F)
    {A : Adversary (romCollisionGame F)} (hA : IsPolyTimeRom F sz A) :
    ∃ C k : ℕ, RomEff F (fun l => C * l ^ k + C) A := by
  obtain ⟨B, rfl, hBpt⟩ := hA
  obtain ⟨C, k, hq⟩ := ((romPolyTime_iff_intr_and_queries sz B).mp hBpt).2
  exact ⟨C, k, romEff_of_queryBound B sz _ hq⟩

/-! ### The polynomial-budget arithmetic the floors ask for. -/

/-- `(C·lᵏ+C)² + 1` is polynomially bounded — the `hQ` shape `romCollision_hard` (508) and
`keyedRom_hard` (162) take. -/
theorem polyBounded_budget_sq (C k : ℕ) :
    PolyBounded (fun l =>
      ((C * l ^ k + C : ℕ) : ℝ) * ((C * l ^ k + C : ℕ) : ℝ) + 1) := by
  refine ⟨2 * k, 4 * (C : ℝ) * (C : ℝ) + 1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : (1 : ℝ) ≤ (n : ℝ) ^ k := one_le_pow₀ hn1
  have h2k : (n : ℝ) ^ (2 * k) = (n : ℝ) ^ k * (n : ℝ) ^ k := by
    rw [two_mul, pow_add]
  rw [abs_of_nonneg (by positivity), h2k]
  push_cast
  nlinarith [hx, sq_nonneg ((n : ℝ) ^ k - 1), Nat.cast_nonneg (α := ℝ) C,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) C) (Nat.cast_nonneg (α := ℝ) C))
      (sq_nonneg ((n : ℝ) ^ k - 1))]

/-- `2·(C·lᵏ+C) + 1` is polynomially bounded — the `hQ` shape `keyedRomHiding_hard` (930)
takes. -/
theorem polyBounded_budget_two_mul (C k : ℕ) :
    PolyBounded (fun l => 2 * ((C * l ^ k + C : ℕ) : ℝ) + 1) := by
  refine ⟨k, 4 * (C : ℝ) + 1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : (1 : ℝ) ≤ (n : ℝ) ^ k := one_le_pow₀ hn1
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith [hx, Nat.cast_nonneg (α := ℝ) C,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) C) (sub_nonneg.mpr hx)]

/-! ## §4 — ⚑⚑ THE PROMOTED FLOORS: binding and keyed collision at FULL POLY-TIME. -/

/-- **⚑⚑ BINDING, PROMOTED TO THE FULL POLY-TIME CLASS.** At a `λ`-bit digest space, EVERY
poly-time ROM adversary's collision advantage is negligible — `romCollision_hard`'s birthday
bound (364), now quantified over the whole PPT class instead of a per-budget query class. The
residual that the query-bounded floor carried ("only against `Q`-query adversaries") is
DISCHARGED; the ROM idealization itself remains the one named residual. -/
theorem binding_polyTime (F : RomFamily) (sz : RomAnsSize F)
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l) :
    Hard (romCollisionGame F) (IsPolyTimeRom F sz) := by
  intro A hA
  obtain ⟨C, k, hEff⟩ := polyTime_to_queryBounded sz hA
  exact romCollision_hard F (fun l => C * l ^ k + C) (polyBounded_budget_sq C k) hw A hEff

/-- **The keyed poly-time class** — poly-time at the tag-folded family, so the same
oracle-interfaced programs attack the keyed game. -/
def IsPolyTimeKeyed (F : KeyedRomFamily) (sz : RomAnsSize F.toRomFamily)
    (A : Adversary (keyedRomGame F)) : Prop :=
  IsPolyTimeRom F.toRomFamily sz A

/-- **⚑⚑ KEYED COLLISION, PROMOTED TO THE FULL POLY-TIME CLASS.** `keyedRom_hard` (162) at every
poly-time keyed adversary: the domain-separated collision floor of the deployed keyed hash
shape, against the whole PPT class. -/
theorem collision_polyTime (F : KeyedRomFamily) (sz : RomAnsSize F.toRomFamily)
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l) :
    Hard (keyedRomGame F) (IsPolyTimeKeyed F sz) := by
  intro A hA
  obtain ⟨C, k, hEff⟩ := polyTime_to_queryBounded sz hA
  exact keyedRom_hard F (fun l => C * l ^ k + C) (polyBounded_budget_sq C k) hw A hEff

/-! ## §5 — THE DISTINGUISHER PARTNER: the cost model at the two-world hiding game.

The hiding game's adversary is a `HidingDistinguisher` (KeyedRomHidingFloor 355): two fixed
messages and a raw `accept : (Msg × B → R) → B → R → Bool` that at the RAW type may read the
whole oracle and even the hidden blinding. The cost-carrying shape below can do NEITHER: the
challenge digest is its INPUT (that is data the game hands over), the oracle is its QUERY
interface, and the blinding simply does not appear. -/

/-- **A COST-CARRYING TWO-WORLD DISTINGUISHER.** Two challenge messages fixed up front, and a
CHALLENGE-INDEXED `FreeOracle` program: on challenge digest `c` it queries the keyed oracle
(domain `Msg × B`) and outputs a verdict bit. ⚑ The hidden blinding is NOT an input — the
structure has no field that could receive it. -/
structure CostDistinguisher (Msg B R : Type) where
  /-- The first challenge message. -/
  msg0 : Msg
  /-- The second challenge message. -/
  msg1 : Msg
  /-- The verdict program, indexed by the challenge digest. -/
  prog : R → FreeOracle Unit (fun _ => Msg × B) (fun _ => R) Bool

/-- The induced raw hiding distinguisher: the verdict is the program run against the oracle —
a function of the challenge and the answers it queried, and of nothing else (`accept` ignores
`r` BY CONSTRUCTION). -/
def CostDistinguisher.toHiding {Msg B R : Type} (Dst : CostDistinguisher Msg B R) :
    HidingDistinguisher Msg B R where
  msg0 := Dst.msg0
  msg1 := Dst.msg1
  accept := fun H _r c => FreeOracle.denote (fun _ q => H q) (Dst.prog c)

/-- **The bridge, at the hiding game**: a cost distinguisher whose programs make at most `Q`
queries (syntactically, at every challenge) is in the `QueryHiding` class (413). -/
theorem CostDistinguisher.queryHiding {Msg B R : Type} [Fintype R]
    (Dst : CostDistinguisher Msg B R) (szB : Bool → ℕ)
    (Q : ℕ) (hQ : ∀ c, (FreeOracle.cost szB (Dst.prog c)).qry () ≤ Q) :
    QueryHiding Q Dst.toHiding :=
  ⟨fun c => toOracleComp (Dst.prog c),
   fun c => toOracleComp_queryBounded_of_le szB (Dst.prog c) (hQ c),
   fun H _r c => (toOracleComp_eval (Dst.prog c) H).symm⟩

/-- A family of cost distinguishers, one per security parameter. -/
structure FamilyCostDistinguisher (F : HidingRomFamily) where
  /-- The cost distinguisher at parameter `l`. -/
  dst : ∀ l, CostDistinguisher (F.Msg l) (F.B l) (F.R l)

/-- The induced raw family distinguisher. -/
def FamilyCostDistinguisher.toFamily {F : HidingRomFamily}
    (Dst : FamilyCostDistinguisher F) : FamilyHidingDistinguisher F :=
  ⟨fun l => (Dst.dst l).toHiding⟩

/-- **`DistPolyTime`** — the distinguisher's programs run in poly total cost, uniformly over the
challenge (the challenge plays the instance's role in `CostAdversary.PolyTime`'s `∀ i`). -/
def DistPolyTime (F : HidingRomFamily) (szB : Bool → ℕ)
    (Dst : FamilyCostDistinguisher F) : Prop :=
  ∃ C k : ℕ, ∀ l (c : F.R l),
    (letI := F.rFin l
     FreeOracle.cost szB ((Dst.dst l).prog c)).total ≤ C * l ^ k + C

/-- **⚑ THE FULL PPT DISTINGUISHER CLASS** over raw family distinguishers — `IsPolyTimeDist A`
iff SOME poly-time cost distinguisher denotes to `A`. The two-world `Eff` with content, the
mirror of `IsPolyTimeRom` on the `distAdv`-shaped side. -/
def IsPolyTimeDist (F : HidingRomFamily) (szB : Bool → ℕ)
    (A : FamilyHidingDistinguisher F) : Prop :=
  ∃ Dst : FamilyCostDistinguisher F, Dst.toFamily = A ∧ DistPolyTime F szB Dst

/-- **⚑⚑ TWO-WORLD HIDING, PROMOTED TO THE FULL PPT DISTINGUISHER CLASS.** At a `λ`-bit blinding
space, EVERY poly-time distinguisher's two-world hiding advantage is negligible —
`keyedRomHiding_hard` (930) composed with the bridge: poly-time bounds the query component,
the query component is the erased tree's budget, and the tree is the `QueryHiding` witness.
The hiding floor's "query-bounded only" residual is DISCHARGED; the ROM idealization remains
the one named residual. -/
theorem hiding_polyTime (F : HidingRomFamily) (szB : Bool → ℕ)
    (hw : ∀ l, letI := F.bFin l; Fintype.card (F.B l) = 2 ^ l) :
    HidingHard F (IsPolyTimeDist F szB) := by
  intro A hA
  obtain ⟨Dst, rfl, C, k, hC⟩ := hA
  refine keyedRomHiding_hard F (fun l => C * l ^ k + C)
    (polyBounded_budget_two_mul C k) hw _ ?_
  intro l
  letI := F.msgFin l; letI := F.msgDec l; letI := F.bFin l; letI := F.bDec l
  letI := F.rFin l; letI := F.rDec l; letI := F.bNe l; letI := F.rNe l
  exact (Dst.dst l).queryHiding szB _ (fun c =>
    (Cost.qry_le_total _ ()).trans (hC l c))

/-- Contrapositive tooth (mirror of `KeyedRomFloor.not_keyedRomEff_of_not_negl`): a family
distinguisher with non-negligible advantage is OUTSIDE the poly-time class. -/
theorem not_polyTimeDist_of_not_negl (F : HidingRomFamily) (szB : Bool → ℕ)
    (hw : ∀ l, letI := F.bFin l; Fintype.card (F.B l) = 2 ^ l)
    (A : FamilyHidingDistinguisher F) (hnn : ¬ Negl (famHidingAdv F A)) :
    ¬ IsPolyTimeDist F szB A :=
  fun h => hnn (hiding_polyTime F szB hw A h)

/-! ## §6 — NON-VACUITY: both poles, at the deployed-shape families.

The promoted floors quantify over a class that must be INHABITED by real winners (else the
floors are `hard_bot_vacuous` in disguise) and must EXCLUDE the full-tape solvers (else the
floors would be false). Both, proved. -/

/-- A concrete, non-degenerate answer size for the binary deployed-shape family: a collision
pair is two `(l+1)`-bit points. -/
def binarySz : RomAnsSize binaryRomFamily := fun l _ => 2 * l + 2

/-- **THE GENUINE TWO-QUERY FINDER, AS A COST PROGRAM.** Query `x l`, query `y l`, output the
pair iff the answers collide. The oracle-interfaced twin of `RomQueryFloor.twoPointComp`. -/
def binaryTwoPoint (x y : ∀ l, binaryRomFamily.D l) : RomCostAdversary binaryRomFamily where
  prog := fun l =>
    letI := binaryRomFamily.rDec l
    .query () (x l) fun rx => .query () (y l) fun ry =>
      if rx = ry then .pure (x l, y l) else .pure (x l, x l)

/-- The two-query cost program denotes to exactly `RomQueryFloor`'s two-point adversary. -/
theorem binaryTwoPoint_toAdversary (x y : ∀ l, binaryRomFamily.D l) :
    (binaryTwoPoint x y).toAdversary
      = romAdv binaryRomFamily (fun l => twoPointComp binaryRomFamily l (x l) (y l)) := by
  unfold RomCostAdversary.toAdversary romAdv
  congr 1
  funext l H
  letI := binaryRomFamily.rDec l
  show FreeOracle.denote (fun _ q => H q)
      ((binaryTwoPoint x y).prog l)
    = (twoPointComp binaryRomFamily l (x l) (y l)).eval H
  by_cases h : H (x l) = H (y l) <;>
    simp [binaryTwoPoint, twoPointComp, FreeOracle.denote, OracleComp.eval, h]

/-- **(⊥ POLE — the poly-time class contains the two-query finder.)** Its cost: two queries,
plus writing a `(2l+2)`-symbol answer — total `2l + 4`, poly. Derived from the syntax, as
always; nothing is asserted. -/
theorem binaryTwoPoint_polyTime (x y : ∀ l, binaryRomFamily.D l) :
    RomPolyTime binarySz (binaryTwoPoint x y) := by
  refine ⟨4, 1, fun l => ?_⟩
  letI := binaryRomFamily.rFin l
  letI := binaryRomFamily.rDec l
  letI := binaryRomFamily.rNe l
  have hbranch : ∀ rx ry : binaryRomFamily.R l,
      FreeOracle.cost (binarySz l)
        (if rx = ry then (.pure (x l, y l) : FreeOracle Unit (fun _ => binaryRomFamily.D l)
            (fun _ => binaryRomFamily.R l) (binaryRomFamily.D l × binaryRomFamily.D l))
          else .pure (x l, x l))
        ≤ (⟨2 * l + 2, fun _ => 0⟩ : Cost Unit) := by
    intro rx ry
    split <;> exact le_of_eq rfl
  have hinner : ∀ rx : binaryRomFamily.R l,
      FreeOracle.cost (binarySz l)
        (.query () (y l) fun ry =>
          if rx = ry then (.pure (x l, y l) : FreeOracle Unit (fun _ => binaryRomFamily.D l)
              (fun _ => binaryRomFamily.R l) (binaryRomFamily.D l × binaryRomFamily.D l))
            else .pure (x l, x l))
        ≤ Cost.callC () + (⟨2 * l + 2, fun _ => 0⟩ : Cost Unit) := by
    intro rx
    rw [FreeOracle.cost_query]
    exact Cost.add_le_add (le_refl _) (Cost.supOver_le (fun ry => hbranch rx ry))
  have houter : (binaryTwoPoint x y).costAt binarySz l
      ≤ Cost.callC () + (Cost.callC () + (⟨2 * l + 2, fun _ => 0⟩ : Cost Unit)) := by
    show FreeOracle.cost (binarySz l) ((binaryTwoPoint x y).prog l) ≤ _
    rw [show (binaryTwoPoint x y).prog l
        = .query () (x l) (fun rx => .query () (y l) fun ry =>
            if rx = ry then .pure (x l, y l) else .pure (x l, x l)) from rfl,
      FreeOracle.cost_query]
    exact Cost.add_le_add (le_refl _) (Cost.supOver_le (fun rx => hinner rx))
  have htot := Cost.total_mono houter
  have hcall : (Cost.callC (O := Unit) ()).total = 1 := by
    simp [Cost.callC, Cost.total]
  have hconst : ((⟨2 * l + 2, fun _ => 0⟩ : Cost Unit)).total = 2 * l + 2 := by
    simp [Cost.total]
  have hval : (Cost.callC (O := Unit) ()
      + (Cost.callC () + (⟨2 * l + 2, fun _ => 0⟩ : Cost Unit))).total = 2 * l + 4 := by
    rw [Cost.total_add, Cost.total_add, hcall, hconst]
    omega
  rw [hval] at htot
  calc ((binaryTwoPoint x y).costAt binarySz l).total
      ≤ 2 * l + 4 := htot
    _ ≤ 4 * l ^ 1 + 4 := by rw [pow_one]; omega

/-- **(⊥ POLE, PRICED.)** The poly-time class is inhabited by an adversary with strictly
POSITIVE advantage at every parameter — the promoted binding floor is a statement about a real,
winning attacker, not about an empty class. -/
theorem polyTimeRom_inhabited_with_advantage :
    ∃ A : Adversary (romCollisionGame binaryRomFamily),
      IsPolyTimeRom binaryRomFamily binarySz A
        ∧ ∀ l, 0 < gameAdv (romCollisionGame binaryRomFamily) A l := by
  have hlt : ∀ l : ℕ, 1 < 2 * 2 ^ l := by
    intro l
    have : 0 < 2 ^ l := by positivity
    omega
  let x : ∀ l, binaryRomFamily.D l := fun l => (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l))
  let y : ∀ l, binaryRomFamily.D l := fun l => (⟨1, hlt l⟩ : Fin (2 * 2 ^ l))
  have hxy : ∀ l, x l ≠ y l := by
    intro l h
    have := congrArg Fin.val h
    simp [x, y] at this
  refine ⟨(binaryTwoPoint x y).toAdversary,
    ⟨binaryTwoPoint x y, rfl, binaryTwoPoint_polyTime x y⟩, fun l => ?_⟩
  rw [binaryTwoPoint_toAdversary x y]
  exact twoPointAdv_gameAdv_pos binaryRomFamily l x y (hxy l)

/-- **(⊤ POLE — `Classical.choice`'s adversary is EXCLUDED from the poly-time class.)** The
full-oracle answerer's advantage is the solvable fraction — the constant `1` at the compressing
deployed shape. Were it poly-time, `binding_polyTime` would make `1` negligible. The promotion
therefore keeps out exactly the adversary the unrestricted class admits — the same exclusion
`RomQueryFloor.choiceAdv_not_romEff` proves for the query-bounded class, now at poly-time. -/
theorem choiceAdv_not_polyTimeRom
    (hne : ∀ l, Nonempty ((romCollisionGame binaryRomFamily).Ans l)) :
    ¬ IsPolyTimeRom binaryRomFamily binarySz
      (choiceAdv (romCollisionGame binaryRomFamily) hne) := by
  intro hA
  have hnegl := binding_polyTime binaryRomFamily binarySz binaryRom_card_R _ hA
  rw [choiceAdv_gameAdv] at hnegl
  exact binaryRom_top_false
    ((hard_top_iff_solvableFrac_negl (romCollisionGame binaryRomFamily) hne).mpr hnegl)

/-- **THE QUERY HOG at the ROM interface** — poly intrinsic work, `2^l` oracle calls. -/
def romQueryHog (x : ∀ l, binaryRomFamily.D l) : RomCostAdversary binaryRomFamily where
  prog := fun l => FreeOracle.probe () (x l) (2 ^ l) (x l, x l)

/-- **(THE QUERY COMPONENT IS LOAD-BEARING.)** The query hog's intrinsic work is poly (it just
writes its answer) yet it is NOT `RomPolyTime`: its `2^l` COUNTED calls blow the budget. At the
ROM interface an adversary cannot smuggle exponentially many oracle reads past the cost model —
the exact failure mode `CostAdversary.queryHog` documents, now at the game the floors live at. -/
theorem romQueryHog_not_polyTime (x : ∀ l, binaryRomFamily.D l) :
    ¬ RomPolyTime binarySz (romQueryHog x) := by
  rintro ⟨C, k, h⟩
  refine expBound_not_ppt ⟨k, C, fun l => ?_⟩
  have hl := h l
  have hcost : (romQueryHog x).costAt binarySz l
      = ⟨2 * l + 2, fun o' => if o' = () then 2 ^ l else 0⟩ := by
    letI := binaryRomFamily.rFin l
    letI := binaryRomFamily.rNe l
    exact FreeOracle.cost_probe (Q := fun _ => binaryRomFamily.D l)
      (R := fun _ => binaryRomFamily.R l) (binarySz l) () (x l) (2 ^ l) (x l, x l)
  rw [hcost] at hl
  have hsum : ((⟨2 * l + 2, fun o' => if o' = () then 2 ^ l else 0⟩ : Cost Unit)).total
      = 2 * l + 2 + 2 ^ l := by
    simp [Cost.total]
  rw [hsum] at hl
  show 2 ^ l ≤ C * l ^ k + C
  exact le_trans (Nat.le_add_left _ _) hl

/-! ### Non-vacuity on the hiding side. -/

/-- **THE ONE-QUERY DISTINGUISHER, AS A COST PROGRAM.** Probe the single point `(msg0, r0)` and
compare with the challenge — `KeyedRomHidingFloor.oneQueryAdv`'s exact strategy, now with its
one query COUNTED in its syntax. -/
def oneQueryCostDist {Msg B R : Type} [DecidableEq R] (m0 m1 : Msg) (r0 : B) :
    CostDistinguisher Msg B R where
  msg0 := m0
  msg1 := m1
  prog := fun c => .query () (m0, r0) fun a => .pure (decide (a = c))

/-- The one-query cost program denotes to exactly `oneQueryAdv`. -/
theorem oneQueryCostDist_toHiding {Msg B R : Type} [DecidableEq R] (m0 m1 : Msg) (r0 : B) :
    (oneQueryCostDist (Msg := Msg) (B := B) (R := R) m0 m1 r0).toHiding
      = oneQueryAdv m0 m1 r0 := by
  unfold oneQueryCostDist CostDistinguisher.toHiding oneQueryAdv
  simp [FreeOracle.denote]

/-- The one-query cost program's total cost is `2` at every challenge: one counted call, one
symbol of verdict. -/
theorem oneQueryCostDist_total_le {Msg B R : Type} [Fintype R] [DecidableEq R]
    (m0 m1 : Msg) (r0 : B) (c : R) :
    (FreeOracle.cost (fun _ => 1)
      ((oneQueryCostDist (Msg := Msg) (B := B) (R := R) m0 m1 r0).prog c)).total ≤ 2 := by
  have hleaf : ∀ a : R,
      FreeOracle.cost (fun _ => 1)
        (.pure (decide (a = c)) : FreeOracle Unit (fun _ => Msg × B) (fun _ => R) Bool)
        ≤ (⟨1, fun _ => 0⟩ : Cost Unit) := fun a => le_of_eq rfl
  have hcost : FreeOracle.cost (fun _ => 1)
      ((oneQueryCostDist (Msg := Msg) (B := B) (R := R) m0 m1 r0).prog c)
      ≤ Cost.callC () + (⟨1, fun _ => 0⟩ : Cost Unit) := by
    rw [show (oneQueryCostDist (Msg := Msg) (B := B) (R := R) m0 m1 r0).prog c
        = .query () (m0, r0) (fun a => .pure (decide (a = c))) from rfl,
      FreeOracle.cost_query]
    exact Cost.add_le_add (le_refl _) (Cost.supOver_le hleaf)
  have htot := Cost.total_mono hcost
  have hcall : (Cost.callC (O := Unit) ()).total = 1 := by
    simp [Cost.callC, Cost.total]
  have hone : ((⟨1, fun _ => 0⟩ : Cost Unit)).total = 1 := by
    simp [Cost.total]
  have hval : (Cost.callC (O := Unit) () + (⟨1, fun _ => 0⟩ : Cost Unit)).total = 2 := by
    rw [Cost.total_add, hcall, hone]
  rw [hval] at htot
  exact htot

/-- **(⊥ POLE, HIDING — the PPT distinguisher class is inhabited by a real winner.)** The
one-query cost distinguisher family at the deployed-shape blinded-span family: poly-time
(total cost `2`), and its hiding advantage is strictly POSITIVE at every parameter. The
promoted hiding floor is about a class with a real attacker in it. -/
theorem polyTimeDist_inhabited_with_advantage :
    ∃ A : FamilyHidingDistinguisher blindedSpanRomFamily,
      IsPolyTimeDist blindedSpanRomFamily (fun _ => 1) A
        ∧ ∀ l, 0 < famHidingAdv blindedSpanRomFamily A l := by
  have hlt : ∀ l : ℕ, 1 < 2 * 2 ^ l := by
    intro l
    have : 0 < 2 ^ l := by positivity
    omega
  let Dst : FamilyCostDistinguisher blindedSpanRomFamily :=
    ⟨fun l =>
      letI := blindedSpanRomFamily.rDec l
      oneQueryCostDist (Msg := blindedSpanRomFamily.Msg l) (B := blindedSpanRomFamily.B l)
        (R := blindedSpanRomFamily.R l)
        (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l)) (⟨1, hlt l⟩ : Fin (2 * 2 ^ l))
        (⟨0, by positivity⟩ : Fin (2 ^ l))⟩
  refine ⟨Dst.toFamily, ⟨Dst, rfl, 2, 0, fun l c => ?_⟩, fun l => ?_⟩
  · letI := blindedSpanRomFamily.rFin l
    letI := blindedSpanRomFamily.rDec l
    calc (FreeOracle.cost (fun _ => 1) ((Dst.dst l).prog c)).total
        ≤ 2 := oneQueryCostDist_total_le _ _ _ c
      _ ≤ 2 * l ^ 0 + 2 := by simp
  · letI := blindedSpanRomFamily.msgFin l; letI := blindedSpanRomFamily.msgDec l
    letI := blindedSpanRomFamily.bFin l; letI := blindedSpanRomFamily.bDec l
    letI := blindedSpanRomFamily.rFin l; letI := blindedSpanRomFamily.rDec l
    letI := blindedSpanRomFamily.bNe l; letI := blindedSpanRomFamily.rNe l
    show 0 < hidingAdv ((Dst.dst l).toHiding)
    rw [show (Dst.dst l).toHiding
        = oneQueryAdv (B := blindedSpanRomFamily.B l) (R := blindedSpanRomFamily.R l)
          (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l)) (⟨1, hlt l⟩ : Fin (2 * 2 ^ l))
          (⟨0, by positivity⟩ : Fin (2 ^ l)) from oneQueryCostDist_toHiding _ _ _]
    refine oneQueryAdv_hidingAdv_pos _ _ _ ?_ ?_
    · intro h
      have := congrArg Fin.val h
      simp at this
    · show 1 < Fintype.card (Fin (2 ^ (8 * l + 8)))
      rw [Fintype.card_fin]
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (8 * l + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The full-tape `topAdv` family at the deployed-shape blinded-span family — the adversary
that reads the WHOLE oracle and the hidden blinding. -/
def blindedTopFamily : FamilyHidingDistinguisher blindedSpanRomFamily :=
  ⟨fun l =>
    letI := blindedSpanRomFamily.rDec l
    topAdv (B := blindedSpanRomFamily.B l) (R := blindedSpanRomFamily.R l)
      (⟨0, by have := Nat.two_pow_pos l; omega⟩ : Fin (2 * 2 ^ l))
      (⟨1, by have := Nat.two_pow_pos l; omega⟩ : Fin (2 * 2 ^ l))⟩

/-- The full-tape family's advantage is at least `1/2` at every parameter (it is
`1 − 1/2^(8l+8)`, `topAdv_hidingAdv`). -/
theorem blindedTopFamily_advantage_ge_half (l : ℕ) :
    (1 : ℝ) / 2 ≤ famHidingAdv blindedSpanRomFamily blindedTopFamily l := by
  letI := blindedSpanRomFamily.msgFin l; letI := blindedSpanRomFamily.msgDec l
  letI := blindedSpanRomFamily.bFin l; letI := blindedSpanRomFamily.bDec l
  letI := blindedSpanRomFamily.rFin l; letI := blindedSpanRomFamily.rDec l
  letI := blindedSpanRomFamily.bNe l; letI := blindedSpanRomFamily.rNe l
  have hne : (⟨0, by have := Nat.two_pow_pos l; omega⟩ : Fin (2 * 2 ^ l))
      ≠ (⟨1, by have := Nat.two_pow_pos l; omega⟩ : Fin (2 * 2 ^ l)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  show (1 : ℝ) / 2 ≤ hidingAdv (blindedTopFamily.adv l)
  have heq : hidingAdv (blindedTopFamily.adv l)
      = 1 - 1 / (Fintype.card (blindedSpanRomFamily.R l) : ℝ) :=
    topAdv_hidingAdv _ _ hne
  rw [heq]
  have h2 : (2 : ℝ) ≤ (Fintype.card (blindedSpanRomFamily.R l) : ℝ) := by
    have : (2 : ℕ) ≤ Fintype.card (Fin (2 ^ (8 * l + 8))) := by
      rw [Fintype.card_fin]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (8 * l + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have hinv : 1 / (Fintype.card (blindedSpanRomFamily.R l) : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- A function bounded below by `1/2` everywhere is not negligible. -/
theorem not_negl_of_ge_half {f : ℕ → ℝ} (h : ∀ l, (1 : ℝ) / 2 ≤ f l) : ¬ Negl f := by
  intro hn
  obtain ⟨n, hlt, hn2⟩ := ((hn 1).and (Filter.eventually_ge_atTop 2)).exists
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnn : (0 : ℝ) ≤ f n := le_trans (by norm_num) (h n)
  rw [abs_of_nonneg hnn, pow_one] at hlt
  have hhalf : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn'
  linarith [h n]

/-- **(⊤ POLE, HIDING — the full-tape reader is EXCLUDED from the PPT distinguisher class.)**
`topAdv` reads the whole oracle and the hidden blinding; NO poly-time cost distinguisher
denotes to it (its advantage `≥ 1/2` would then be negligible). Structurally forced too: a
`CostDistinguisher`'s verdict cannot even MENTION the blinding. The hiding twin of
`choiceAdv_not_polyTimeRom`. -/
theorem blindedTopFamily_not_polyTimeDist :
    ¬ IsPolyTimeDist blindedSpanRomFamily (fun _ => 1) blindedTopFamily :=
  not_polyTimeDist_of_not_negl blindedSpanRomFamily (fun _ => 1) blindedSpanRom_card_B
    blindedTopFamily (not_negl_of_ge_half blindedTopFamily_advantage_ge_half)

/-! ## §7 — THE WHOLE VERDICT, at one deployed-shape family. -/

/-- **⚑⚑⚑ THE PROMOTION, PRICED AT THE DEPLOYED SHAPE.** At the `λ`-bit binary family, all
three at once: the binding floor HOLDS against the FULL poly-time class; the class is INHABITED
by a poly-time attacker with positive advantage; and the `Classical.choice` full-oracle solver
is EXCLUDED from the class. The floor is true, about something, and not about everything. -/
theorem binaryRom_polyTime_verdict :
    Hard (romCollisionGame binaryRomFamily) (IsPolyTimeRom binaryRomFamily binarySz)
      ∧ (∃ A, IsPolyTimeRom binaryRomFamily binarySz A
              ∧ ∀ l, 0 < gameAdv (romCollisionGame binaryRomFamily) A l)
      ∧ ∀ hne : ∀ l, Nonempty ((romCollisionGame binaryRomFamily).Ans l),
          ¬ IsPolyTimeRom binaryRomFamily binarySz
            (choiceAdv (romCollisionGame binaryRomFamily) hne) :=
  ⟨binding_polyTime binaryRomFamily binarySz binaryRom_card_R,
   polyTimeRom_inhabited_with_advantage,
   fun hne => choiceAdv_not_polyTimeRom hne⟩

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  toOracleComp_eval,
  toOracleComp_queryBounded,
  toOracleComp_queryBounded_of_le,
  romPolyTime_iff_intr_and_queries,
  romEff_of_queryBound,
  polyTime_to_queryBounded,
  polyBounded_budget_sq,
  polyBounded_budget_two_mul,
  binding_polyTime,
  collision_polyTime,
  CostDistinguisher.queryHiding,
  hiding_polyTime,
  not_polyTimeDist_of_not_negl,
  binaryTwoPoint_toAdversary,
  binaryTwoPoint_polyTime,
  polyTimeRom_inhabited_with_advantage,
  choiceAdv_not_polyTimeRom,
  romQueryHog_not_polyTime,
  oneQueryCostDist_toHiding,
  oneQueryCostDist_total_le,
  polyTimeDist_inhabited_with_advantage,
  blindedTopFamily_advantage_ge_half,
  not_negl_of_ge_half,
  blindedTopFamily_not_polyTimeDist,
  binaryRom_polyTime_verdict
]

end Dregg2.Crypto.PolyTimeRomBridge
