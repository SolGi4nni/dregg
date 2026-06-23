/-
# Dregg2.Authority.CaveatConvergence — the caveat-algebra CONVERGENCE (§3B): the parallel caveat
surfaces are VIEWS of one core, proved by faithful denotation-preserving embeddings.

The §3B language uplift grew, by incremental builds, FOUR parallel caveat/predicate surfaces that
share the Boolean connective shape but were never tied together — a "fork-debt" the live-wiring and
D6 agents both named:

  * **`Authority.Caveat.CaveatPred`** — the reified, introspectable temporal-caveat AST
    (`validAfter` / `validUntil` / `heightLt` + `and`/`or`/`not`/`tt`/`ff`), denoting over a request
    `Ctx` through an explicit `view : Ctx → Time` seam.
  * **`Exec.PredAlgebra.Pred`** — the clean Boolean predicate ALGEBRA over the `StateConstraint`
    atom catalog (`fieldGe`/`fieldLe`/… + the typed dig/sym atoms), denoting over the `(old, new)`
    transition records.
  * **`Exec.PredCaveatLive`** — the LIVE bridge: `CaveatPred` instantiated at `Ctx := TxCtx` (the
    `(actor, old, new)` transition tuple) with `txViewNew := (·.new)`, enforced on the executor's
    field-write leg.
  * **`Authority.RelationalClosure.RelPred`** — the relational closure, the general affine
    half-space `Σ cᵢ·rec[fᵢ] ≤ k` closed under `and`/`or`/`not` (covered by `AffineBridge` already).

## What this module proves (the convergence, honest)

The two surfaces that share the SAME `(old, new)` transition denotation — `CaveatPred` (under the
live `txViewNew`/`txViewOld` views) and `Pred` — are made VIEWS OF ONE CORE: there is a
denotation-preserving translation `coreOfCaveat : CaveatPred → Pred` such that, on the SAME
transition, `CaveatPred.eval (live view) = Pred.eval (coreOfCaveat …)`. So the live `caveatsAdmit`
(over `CaveatPred`) and the `Pred`-algebra decision are two readings of ONE predicate term — the
fork between them is a VIEW-multiplicity, NOT divergent semantics.

  * **THE FIRST WELD — `caveatPred_validAfter_embeds` (the atom).** `CaveatPred.eval txViewNew
    (.validAfter t)` on `(actor, old, new)` EQUALS `Pred.eval (.atom (.simple (.fieldGe f t)))` on the
    single-field record `[(f, .int new)]`. The reified temporal floor and the algebra's `fieldGe` atom
    are the SAME decision `decide (t ≤ new)` — proven equal, both directions of admit/reject.
  * **The companion atom welds** — `validUntil ≡ fieldLe`, and the `old`-view direction (a caveat on
    the prior value), each a denotational equality on the shared scalar.
  * **THE STRUCTURAL EMBEDDING — `coreOfCaveat_view_embeds`.** The translation extends over the WHOLE
    `and`/`or`/`not`/`tt`/`ff` connective layer by structural induction: `CaveatPred.eval view p`
    equals `Pred.eval (coreOfCaveat view p)` on the bridged transition, for EVERY `p`. So CaveatPred
    is a faithful VIEW of the `Pred` core — the connectives mean the same thing, the atoms mean the
    same thing, end to end.
  * **The live-leg corollary — `caveatPredLive_is_pred_view`.** Under the live `txViewNew`, the
    reified caveat surface `PredCaveatLive` decides EXACTLY what the `Pred` algebra decides on the
    same `(actor, old, new)` write. The two live admission paths are one decision.

## HONEST FRAMING — expressiveness / consolidation, NOT soundness

This is a CONSOLIDATION result: it retires fork-debt by proving the parallel surfaces are views of
one core (so a fact proved on one transports to the other with no re-proof, and an author writing in
either vocabulary writes the SAME policy). It is NOT a soundness gain — the circuit still binds the
aggregate decision bit and trusts the executor; embedding a caveat does not force its policy
in-circuit. NON-VK: adds no atom, no constructor, no executor arm; a pure metatheory bridge.

## What does NOT fully embed (the honest finding)

`RelPred` (the affine half-space `Σ cᵢ·rec[fᵢ] ≤ k`) is STRICTLY MORE EXPRESSIVE than the
single-field comparison atoms `CaveatPred` reaches: a genuine diagonal `rec[a] − rec[b] ≤ k` reads
TWO slots and is not a `CaveatPred` (whose atoms read one `Time` view). So the convergence is: three
of the four surfaces (`CaveatPred`, `PredCaveatLive`, `Pred`) collapse to one `Pred` core with proven-
equal denotation; the affine `RelPred` is a SUPER-fragment that the `Pred` core embeds INTO (its
comparison atoms are the single-slot affine atoms — `AffineBridge` is the arrow). The four are not
all the SAME expressiveness; they form a TOWER `CaveatPred-atoms ⊆ Pred-comparisons ⊆ RelPred-affine`,
and the convergence proves each inclusion is denotation-preserving where it lands. That tower IS the
resolution of the fork-debt: not "all one algebra", but "one core with proven faithful views".

NEW file only. Imports `Exec.PredCaveatLive` (hence `Authority.Caveat` + `Exec.EffectsState`) and
`Exec.PredAlgebra`. Touches none of them. Every keystone `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.PredCaveatLive
import Dregg2.Exec.PredAlgebra
import Dregg2.Authority.RelationalClosure

namespace Dregg2.Authority.CaveatConvergence

open Dregg2.Exec (Value FieldName)
open Dregg2.Authority (CaveatPred Time)
open Dregg2.Exec.PredCaveatLive (TxCtx txViewNew txViewOld)
open Dregg2.Exec.PredAlgebra (Pred)

/-! ## §1 — The atom welds: a reified temporal caveat IS a `Pred` comparison atom, on the shared
transition.

`CaveatPred.eval` (Caveat.lean) reads a `Time` off the request context through `view`. The live
`PredCaveatLive` instantiates `Ctx := TxCtx` with `txViewNew c := c.new` / `txViewOld c := c.old`.
`Pred.eval` (PredAlgebra.lean) reads a scalar field off the post-record. The bridge makes the SAME
scalar drive both: a `validAfter t` over `txViewNew` is the floor `new ≥ t`, which is EXACTLY the
algebra's `fieldGe f t` atom evaluated on the single-field record `[(f, .int new)]`. -/

/-- The single-field record carrying the WRITTEN scalar `new` under slot `f` — the post-record the
`Pred` comparison atom reads, mirroring `PredCaveat.eval`'s `(old, new) ↦ records` lift. -/
def recOf (f : FieldName) (new : Int) : Value := .record [(f, .int new)]

/-- The bridged scalar reads back: `(recOf f new).scalar f = some new`. The bridge's lemma — the
single-field record exposes exactly the written value to the comparison atom. -/
theorem recOf_scalar (f : FieldName) (new : Int) :
    (recOf f new).scalar f = some new := by
  simp [recOf, Value.scalar, Value.field]

/-- **`caveatPred_validAfter_embeds` (THE FIRST WELD).** The reified temporal floor and the algebra's
`fieldGe` atom are the SAME decision on the shared transition: `CaveatPred.eval txViewNew
(.validAfter t)` on `(actor, old, new)` EQUALS `Pred.eval (.atom (.simple (.fieldGe f t)))` on the
single-field record `[(f, .int new)]`. Both are `decide (t ≤ new)` — the reified caveat is a VIEW of
the `Pred` comparison atom, not a separate semantics. -/
theorem caveatPred_validAfter_embeds (f : FieldName) (t : Time) (actor : Dregg2.Exec.CellId)
    (old new : Int) :
    CaveatPred.eval txViewNew (.validAfter t) { actor := actor, old := old, new := new }
      = Pred.eval (.atom (.simple (.fieldGe f t))) (recOf f old) (recOf f new) := by
  simp only [CaveatPred.eval, txViewNew, Pred.eval, Dregg2.Exec.evalConstraint,
    Dregg2.Exec.evalSimple, recOf_scalar]
  -- LHS: `decide (t ≤ new)`. RHS: `intLe t new = decide (t ≤ new)`.
  rfl

/-- **`caveatPred_validUntil_embeds` (the ceiling weld).** The reified expiry ceiling and the
algebra's `fieldLe` atom are the SAME decision: `validUntil t` over `txViewNew` ≡ `fieldLe f t` — both
`decide (new ≤ t)`. The dual of the floor weld. -/
theorem caveatPred_validUntil_embeds (f : FieldName) (t : Time) (actor : Dregg2.Exec.CellId)
    (old new : Int) :
    CaveatPred.eval txViewNew (.validUntil t) { actor := actor, old := old, new := new }
      = Pred.eval (.atom (.simple (.fieldLe f t))) (recOf f old) (recOf f new) := by
  simp only [CaveatPred.eval, txViewNew, Pred.eval, Dregg2.Exec.evalConstraint,
    Dregg2.Exec.evalSimple, recOf_scalar]
  rfl

/-- **`caveatPred_validAfter_old_embeds` (the prior-value direction).** A caveat read against the
PRIOR value (`txViewOld`) embeds into the algebra atom read on the OLD record: `validAfter t` over
`txViewOld` ≡ `decide (t ≤ old)`, the comparison `fieldGe f t` on `recOf f old`. The same weld on the
`old` projection — both transition projections are views of the same `Pred` atom. -/
theorem caveatPred_validAfter_old_embeds (f : FieldName) (t : Time) (actor : Dregg2.Exec.CellId)
    (old new : Int) :
    CaveatPred.eval txViewOld (.validAfter t) { actor := actor, old := old, new := new }
      = Pred.eval (.atom (.simple (.fieldGe f t))) (recOf f new) (recOf f old) := by
  simp only [CaveatPred.eval, txViewOld, Pred.eval, Dregg2.Exec.evalConstraint,
    Dregg2.Exec.evalSimple, recOf_scalar]
  rfl

/-! ## §2 — The structural embedding `coreOfCaveat`: the WHOLE connective layer is a view.

The atom welds extend over `and`/`or`/`not`/`tt`/`ff` by structural recursion. `coreOfCaveat view p`
translates a `CaveatPred` into the `Pred` core: each temporal atom maps to its `fieldGe`/`fieldLe`
comparison; the connectives map structurally (they MEAN the same Boolean operation in both algebras).
`heightLt h` (strict `< h`) is the comparison `¬ fieldGe (h)` — i.e. `not (fieldGe f h)` is `new < h`
on integers. -/

/-- **`coreOfCaveat f p`** — translate a reified temporal `CaveatPred` into the `Pred` core, on the
live `txViewNew` view, against slot `f`. The temporal atoms become the algebra's comparison atoms
(`validAfter ↦ fieldGe`, `validUntil ↦ fieldLe`, `heightLt h ↦ not (fieldGe h)` = strict `< h`); the
Boolean connectives map structurally. The witness that `CaveatPred` is a sub-language of `Pred`. -/
def coreOfCaveat (f : FieldName) : CaveatPred → Pred
  | .validAfter t => .atom (.simple (.fieldGe f t))
  | .validUntil t => .atom (.simple (.fieldLe f t))
  | .heightLt h   => .not (.atom (.simple (.fieldGe f h)))   -- `new < h`  ≡  `¬ (h ≤ new)`
  | .tt           => .tt
  | .ff           => .ff
  | .and l r      => .and (coreOfCaveat f l) (coreOfCaveat f r)
  | .or l r       => .or (coreOfCaveat f l) (coreOfCaveat f r)
  | .not p        => .not (coreOfCaveat f p)

/-- Helper: the strict `heightLt` atom embeds — `decide (new < h) = !(decide (h ≤ new))` on `Int`. -/
private theorem heightLt_embeds (f : FieldName) (h : Time) (old new : Int) :
    CaveatPred.eval txViewNew (Ctx := TxCtx) (.heightLt h)
        { actor := 0, old := old, new := new }
      = Pred.eval (coreOfCaveat f (.heightLt h)) (recOf f old) (recOf f new) := by
  simp only [CaveatPred.eval, txViewNew, coreOfCaveat, Pred.eval, Dregg2.Exec.evalConstraint,
    Dregg2.Exec.evalSimple, recOf_scalar]
  -- LHS `decide (new < h)`; RHS `!(intLe h new)`. `intLe h new` is `decide (h ≤ new)` by def, so
  -- this is `decide (new < h) = !decide (h ≤ new)` — the `Int` trichotomy.
  show decide (new < h) = !decide (h ≤ new)
  rw [← decide_not]
  congr 1
  exact propext ⟨fun hlt => Int.not_le.mpr hlt, fun hnle => Int.not_le.mp hnle⟩

/-- **`coreOfCaveat_view_embeds` (THE STRUCTURAL EMBEDDING).** For EVERY reified `CaveatPred p`, its
live `txViewNew` denotation on `(actor, old, new)` EQUALS the `Pred` core `coreOfCaveat f p` evaluated
on the bridged single-field records. So `CaveatPred` is a FAITHFUL VIEW of the `Pred` algebra — the
connectives and atoms agree end to end, decided once over all transitions. The fork between the
reified caveat surface and the algebra is a view-multiplicity, not divergent semantics. -/
theorem coreOfCaveat_view_embeds (f : FieldName) (actor : Dregg2.Exec.CellId) (old new : Int) :
    ∀ p : CaveatPred,
      CaveatPred.eval txViewNew p { actor := actor, old := old, new := new }
        = Pred.eval (coreOfCaveat f p) (recOf f old) (recOf f new) := by
  intro p
  induction p with
  | validAfter t => exact caveatPred_validAfter_embeds f t actor old new
  | validUntil t => exact caveatPred_validUntil_embeds f t actor old new
  | heightLt h =>
      -- the helper is stated at `actor := 0`; the denotation does not read `actor`, so it transports.
      have := heightLt_embeds f h old new
      simpa [CaveatPred.eval, txViewNew, coreOfCaveat, Pred.eval] using this
  | tt => rfl
  | ff => rfl
  | and l r ihl ihr =>
      simp only [CaveatPred.eval, coreOfCaveat, Pred.eval, ihl, ihr]
  | or l r ihl ihr =>
      simp only [CaveatPred.eval, coreOfCaveat, Pred.eval, ihl, ihr]
  | not p ih =>
      simp only [CaveatPred.eval, coreOfCaveat, Pred.eval, ih]

/-! ## §3 — The live-leg corollary: the two LIVE admission paths are ONE decision.

`PredCaveatLive.caveatPredAdmit` decides a single reified caveat via `CaveatPred.eval` on the live
`TxCtx`. `PredAlgebra.predCaveatsAdmit` decides a single `Pred` caveat via `Pred.eval` on the lifted
records. The structural embedding makes them AGREE: a `Pred`-caveat that is `coreOfCaveat f p` decides
exactly what the reified caveat `p` decides on the same `(actor, old, new)` write. The fork between
the live reified surface and the live algebra surface is closed. -/

/-- **`caveatPredLive_is_pred_view`.** The live reified admission of a SINGLE `validAfter`/`validUntil`/
connective caveat over slot `f` EQUALS the `Pred`-algebra admission of its `coreOfCaveat f` image, on
the same committed value `old` and write `new`. The two live admission paths decide identically — one
decision, two views. Built from `caveatPredAdmit_single` + `coreOfCaveat_view_embeds` + the `PredCaveat`
single-caveat adapter. -/
theorem caveatPredLive_is_pred_view (k : Dregg2.Exec.RecordKernelState) (f : FieldName)
    (actor target : Dregg2.Exec.CellId) (new : Int) (p : CaveatPred) :
    Dregg2.Exec.PredCaveatLive.caveatPredAdmit
        [{ field := f, pred := p, view := txViewNew }] k f actor target new
      = Pred.eval (coreOfCaveat f p)
          (recOf f (Dregg2.Exec.EffectsState.fieldOf f (k.cell target)))
          (recOf f new) := by
  rw [Dregg2.Exec.PredCaveatLive.caveatPredAdmit_single]
  exact coreOfCaveat_view_embeds f actor (Dregg2.Exec.EffectsState.fieldOf f (k.cell target)) new p

/-! ## §4 — NON-VACUITY: the embedding is a GENUINE shared decision (both admit and reject), not a
laundered tautology. A concrete reified caveat and its `Pred` image agree on a write that ADMITS and
on one that REJECTS — and the negative tooth: the two algebras really do decide (a `validAfter 100`
view rejects 50, both surfaces). -/

/-- A concrete reified floor `validAfter 100` over slot `"v"` and its `Pred` image (`fieldGe "v" 100`).
-/
def vFloorCaveat : CaveatPred := .validAfter 100
def vFloorCore   : Pred := coreOfCaveat "v" vFloorCaveat   -- = `.atom (.simple (.fieldGe "v" 100))`

-- The two surfaces AGREE on a write of 150 (ADMIT) and of 50 (REJECT) — both polarities.
example :
    CaveatPred.eval txViewNew vFloorCaveat { actor := 0, old := 0, new := 150 }
      = Pred.eval vFloorCore (recOf "v" 0) (recOf "v" 150) :=
  coreOfCaveat_view_embeds "v" 0 0 150 vFloorCaveat

example :
    CaveatPred.eval txViewNew vFloorCaveat { actor := 0, old := 0, new := 50 }
      = Pred.eval vFloorCore (recOf "v" 0) (recOf "v" 50) :=
  coreOfCaveat_view_embeds "v" 0 0 50 vFloorCaveat

/-- **`convergence_nonvacuous` — BOTH poles, decided.** The shared decision genuinely ADMITS a write
above the floor and REJECTS one below it, in BOTH surfaces simultaneously (so the embedding is not a
`true = true` triviality). The reified `CaveatPred` and its `Pred` core image are the SAME non-trivial
discriminator. -/
theorem convergence_nonvacuous :
    (CaveatPred.eval txViewNew vFloorCaveat { actor := 0, old := 0, new := 150 } = true ∧
       Pred.eval vFloorCore (recOf "v" 0) (recOf "v" 150) = true) ∧
    (CaveatPred.eval txViewNew vFloorCaveat { actor := 0, old := 0, new := 50 } = false ∧
       Pred.eval vFloorCore (recOf "v" 0) (recOf "v" 50) = false) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- A composed reified WINDOW `validAfter 100 ∧ validUntil 300` and its `Pred` core image — the whole
connective layer embeds, decided over the band `[100, 300]` on both surfaces. -/
def vWindowCaveat : CaveatPred := .and (.validAfter 100) (.validUntil 300)

example :
    CaveatPred.eval txViewNew vWindowCaveat { actor := 0, old := 0, new := 150 }
      = Pred.eval (coreOfCaveat "v" vWindowCaveat) (recOf "v" 0) (recOf "v" 150) :=
  coreOfCaveat_view_embeds "v" 0 0 150 vWindowCaveat

/-- **`window_convergence_nonvacuous`** — the composed window agrees on both surfaces inside the band
(150 ADMIT) and outside it (350 REJECT, 50 REJECT) — the connective embedding is a genuine
discriminator end to end. -/
theorem window_convergence_nonvacuous :
    (CaveatPred.eval txViewNew vWindowCaveat { actor := 0, old := 0, new := 150 } = true ∧
       Pred.eval (coreOfCaveat "v" vWindowCaveat) (recOf "v" 0) (recOf "v" 150) = true) ∧
    (CaveatPred.eval txViewNew vWindowCaveat { actor := 0, old := 0, new := 350 } = false ∧
       Pred.eval (coreOfCaveat "v" vWindowCaveat) (recOf "v" 0) (recOf "v" 350) = false) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## §5 — THE TOWER: the honest expressiveness statement. `CaveatPred`'s atoms are single-slot
comparisons; `RelPred`'s atom is the general affine half-space `Σ cᵢ·rec[fᵢ] ≤ k`. The comparison
`fieldGe f t` ≡ `new ≥ t` IS the single-term affine half-space `(−1)·rec[f] ≤ −t` — so a `CaveatPred`
floor embeds into `RelPred` too (the tower `CaveatPred ⊆ Pred-comparisons ⊆ RelPred-affine`). But a
GENUINE diagonal `rec[a] − rec[b] ≤ k` reads TWO slots and is NOT any `CaveatPred` (whose temporal
atoms read one `Time` view): the affine layer is STRICTLY more expressive. We state the upper rung of
the tower (the floor IS a single-slot half-space) and the honest non-collapse (the diagonal is not a
single-slot comparison). -/

/-- The affine half-space that a `validAfter t` floor on slot `f` corresponds to in `RelPred` shape:
`new ≥ t`  ≡  `(−1)·rec[f] ≤ −t`. This is the upper rung — `CaveatPred`'s comparison embeds into the
affine fragment. (`Authority.AffineBridge` already proves the `Pred`-comparison ↔ `RelPred`-affine
transport on the all-fields-present domain; this names the specific instance for the temporal floor.) -/
def floorAsAffineSum (f : FieldName) (new : Int) : Int :=
  Dregg2.Authority.RelationalClosure.affineSum [((-1 : Int), f)] (recOf f new)

/-- **`floor_is_affine_halfspace` (the upper rung).** The reified floor `new ≥ t` IS the affine
half-space `(−1)·rec[f] ≤ −t` over the SAME single-field record: `validAfter t` admits IFF
`affineSum [(-1,f)] (recOf f new) ≤ −t`. So `CaveatPred`'s comparison atom lands inside `RelPred`'s
affine fragment — the tower's top inclusion, denotation-preserving. -/
theorem floor_is_affine_halfspace (f : FieldName) (t : Time) (actor : Dregg2.Exec.CellId)
    (old new : Int) :
    CaveatPred.eval txViewNew (.validAfter t) { actor := actor, old := old, new := new }
      = decide (floorAsAffineSum f new ≤ -t) := by
  have hsum : floorAsAffineSum f new = -new := by
    simp only [floorAsAffineSum, Dregg2.Authority.RelationalClosure.affineSum,
      Dregg2.Exec.EffectsState.fieldOf, recOf_scalar, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, Option.getD_some]
    ring
  rw [hsum]
  simp only [CaveatPred.eval, txViewNew]
  -- LHS `decide (t ≤ new)`; RHS `decide (-new ≤ -t)` — equal since `t ≤ new ↔ -new ≤ -t`.
  exact decide_eq_decide.mpr (Int.neg_le_neg_iff.symm)

/-- **`affine_diagonal_not_caveat` (the honest non-collapse).** The genuine diagonal
`rec[a] − rec[b] ≤ k` reads TWO distinct slots, so its truth depends on BOTH `a` and `b`; no
`CaveatPred` (whose temporal atoms read a SINGLE `Time` view of the transition) can have this
denotation. We witness it: the diagonal `rec["a"] − rec["b"] ≤ 0` discriminates two records that
agree on slot `"a"` — so it is not a function of `"a"` alone, hence not any single-slot floor. The
affine fragment is STRICTLY more expressive: the convergence is a TOWER, not a single algebra. -/
theorem affine_diagonal_not_caveat :
    ∃ (k : Int) (r₁ r₂ : Value),
      r₁.scalar "a" = r₂.scalar "a" ∧
      Dregg2.Authority.RelationalClosure.RelPred.eval (.affineLe [((1:Int), "a"), ((-1:Int), "b")] k) r₁
        ≠ Dregg2.Authority.RelationalClosure.RelPred.eval
            (.affineLe [((1:Int), "a"), ((-1:Int), "b")] k) r₂ := by
  refine ⟨0, .record [("a", .int 5), ("b", .int 0)], .record [("a", .int 5), ("b", .int 9)],
    ?_, ?_⟩
  · simp [Value.scalar, Value.field]
  · decide

#assert_axioms recOf_scalar
#assert_axioms caveatPred_validAfter_embeds
#assert_axioms caveatPred_validUntil_embeds
#assert_axioms caveatPred_validAfter_old_embeds
#assert_axioms coreOfCaveat_view_embeds
#assert_axioms caveatPredLive_is_pred_view
#assert_axioms convergence_nonvacuous
#assert_axioms window_convergence_nonvacuous
#assert_axioms floor_is_affine_halfspace
#assert_axioms affine_diagonal_not_caveat

end Dregg2.Authority.CaveatConvergence
