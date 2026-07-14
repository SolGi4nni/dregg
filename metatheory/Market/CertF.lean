/-
# Market.CertF — the fhEgg convex-engine soundness core: `Cert-F` (duality-gap ⇒ ε-optimality).

**The verify-not-find keystone for convex clearing.** `docs/deos/PRIVATE-CONVEX-ENGINE.md §2.3`
(the `Cert-F` headline) and `FHEGG-CODEX-INSIGHTS.md` (the GOLD insight) name the crux of the private
convex engine: you never prove the solver converged. For the canonical dregg program — the volume-max
circulation LP

    maximize   wᵀf     subject to   A f = 0,   0 ≤ f ≤ c

(`A` = the **PUBLIC incidence matrix** of the trade graph, per the codex correction: use the incidence
`A`, NOT a dense cycle basis `B`; `w` = volume weights, `c` = capacities — the private amounts) — a
primal-dual triple `(f, π, s)` satisfying the **linear** certificate

    A f = 0,   0 ≤ f ≤ c,   s ≥ 0,   Aᵀπ + s ≥ w,   cᵀs − wᵀf ≤ ε

CERTIFIES that `f` is ε-optimal — **independent of how `(f, π, s)` was found.** The T iterations of the
oblivious first-order solver (PDHG/ADMM) are an *untrusted search*; this certificate is the *checked
output*. This module proves that soundness core, cleanly and in full generality (any ordered
commutative ring `R`; instantiated at `ℤ` for the worked circulation and the AIR emit).

## What is proved (honest scope)

  * **`weak_duality` (the engine of it all).** For EVERY primal-feasible `f` (`Af=0, 0≤f≤c`) and EVERY
    dual-feasible `(π, s)` (`s≥0, Aᵀπ+s≥w`): `wᵀf ≤ cᵀs`. Four steps: `wᵀf ≤ (Aᵀπ+s)ᵀf` (dual
    feasibility, `f≥0`); `= πᵀ(Af) + sᵀf` (linearity); `= sᵀf` (`Af=0`); `≤ sᵀc = cᵀs` (`f≤c`, `s≥0`).
    Uses nothing about how either point arose — this is the whole point of verify-not-find.
  * **`certifies_epsilon_optimal` (THE KEYSTONE).** If `(f, π, s)` is a certificate with gap `cᵀs − wᵀf
    ≤ ε`, then for EVERY primal-feasible `f'`: `wᵀf' ≤ wᵀf + ε`. So no feasible flow beats the certified
    `f` by more than `ε` — `f` is ε-optimal — and the proof reads ONLY the certificate's feasibility +
    gap. `weak_duality` applied to `f'` against the SAME dual `(π, s)` gives `wᵀf' ≤ cᵀs`; the gap gives
    `cᵀs ≤ wᵀf + ε`. The certificate stands entirely on its own.
  * **`gap_nonneg`** — a corollary: the certified gap is `≥ 0` (weak duality at `f` itself), so `ε ≥ 0`
    is forced; a "certificate" claiming a negative gap is vacuous.

**Honest scope — VERIFYING is what is cheap and proved; SELECTING is NOT this theorem's job.** This
core proves the CERTIFICATE is sound: a linear check ⇒ ε-optimality. It says nothing about *finding* the
optimum — the solver that produces `(f, π, s)` is UNTRUSTED and OUT OF SCOPE (per the codex Q3
correction, choosing the max-volume exact all-or-nothing subset is NP-hard; the tractable engine is the
`[0,1]` partial-fill relaxation whose LP this certifies). The division of labour is exactly dregg's
verify-not-find: prove the checker, not the search.

**Emittability (§4).** The certificate check is a set of LINEAR circuit `Constraint`s over the AIR IR
(`Dregg2.Circuit`): the conservation rows `A f = 0` are arithmetic gates (one per vertex), and the gap
`cᵀs − wᵀf` is a single linear functional (`Expr`). Total size `O(m + nnz A)` — NOT `O(T·m)` (proving
the T iterations). Demonstrated on the worked 3-cycle: `satisfied` of the emitted system ↔ the
certificate holds. The feasibility inequalities (`0≤f≤c`, `s≥0`, `Aᵀπ+s≥w`, `gap≤ε`) ride the standard
AIR range/comparison gadget (`Dregg2.Bignum`), named honestly — the tight (`gap = 0`) optimal case is
emitted here as an exact arithmetic gate.

Pure.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Dregg2.Circuit
import Dregg2.Tactics

namespace Market

open Matrix

/-! ## 1. The volume-max circulation LP (public `A`, private amounts). -/

variable {V E : Type*} [Fintype V] [Fintype E]
variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- **The volume-max circulation LP** `max wᵀf s.t. Af=0, 0≤f≤c` — the canonical dregg program of
`PRIVATE-CONVEX-ENGINE.md §2.3`. `A` is the **public incidence matrix** of the trade graph (vertices `V`
× edges `E`); `w` (volume weights), `c` (capacities), and the certified `f` (edge flows) are the private
amounts. `ε` is the public accuracy target. -/
structure FlowLP (V E R : Type*) where
  /-- The public incidence matrix `A = ∂` of the trade graph. Conservation is `A f = 0`. -/
  A : Matrix V E R
  /-- Per-edge volume weights (the objective `max wᵀf`). -/
  w : E → R
  /-- Per-edge capacities (the box `0 ≤ f ≤ c`). -/
  c : E → R
  /-- The public accuracy target (`gap ≤ ε` ⇒ `ε`-optimal). -/
  ε : R

/-- **Primal feasibility** — `f` is a capacity-respecting circulation: conserves at every node
(`A f = 0`), and lies in the box `0 ≤ f ≤ c`. -/
def PrimalFeasible (lp : FlowLP V E R) (f : E → R) : Prop :=
  lp.A *ᵥ f = 0 ∧ 0 ≤ f ∧ f ≤ lp.c

/-- **Dual feasibility** — node potentials `π` and slacks `s` with `s ≥ 0` and `Aᵀπ + s ≥ w`
(the dual of the box-constrained circulation). `π ᵥ* A` is `Aᵀπ`. -/
def DualFeasible (lp : FlowLP V E R) (π : V → R) (s : E → R) : Prop :=
  0 ≤ s ∧ lp.w ≤ π ᵥ* lp.A + s

/-- **A `Cert-F` certificate** — a primal-dual triple whose duality gap is `≤ ε`. The ENTIRE object the
hidden proof checks; sound ⇒ `f` is `ε`-optimal (`certifies_epsilon_optimal`), independent of how the
triple was found. -/
def Certified (lp : FlowLP V E R) (f : E → R) (π : V → R) (s : E → R) : Prop :=
  PrimalFeasible lp f ∧ DualFeasible lp π s ∧ lp.c ⬝ᵥ s - lp.w ⬝ᵥ f ≤ lp.ε

/-! ## 2. Weak duality — the linear inequality every feasible pair satisfies. -/

/-- **`weak_duality` — `wᵀf ≤ cᵀs` for EVERY feasible primal `f` and dual `(π, s)`.** The load-bearing
lemma: the objective at any feasible flow is bounded by the dual value at any dual-feasible point, using
NOTHING about how either was obtained. The four moves:

  * `wᵀf ≤ (Aᵀπ + s)ᵀf` — dual feasibility `w ≤ Aᵀπ + s` scaled by `f ≥ 0`;
  * `(Aᵀπ + s)ᵀf = πᵀ(Af) + sᵀf` — linearity (`Aᵀπ ⬝ f = π ⬝ Af`);
  * `= sᵀf` — primal conservation `Af = 0`;
  * `sᵀf ≤ sᵀc = cᵀs` — the box `f ≤ c` scaled by `s ≥ 0`.

This is the whole of verify-not-find for convex clearing: a certificate is sound because weak duality
sandwiches the optimum, and weak duality reads only the two feasibilities. -/
theorem weak_duality (lp : FlowLP V E R) {f : E → R} {π : V → R} {s : E → R}
    (hf : PrimalFeasible lp f) (hd : DualFeasible lp π s) :
    lp.w ⬝ᵥ f ≤ lp.c ⬝ᵥ s :=
  calc lp.w ⬝ᵥ f
      ≤ (π ᵥ* lp.A + s) ⬝ᵥ f := dotProduct_le_dotProduct_of_nonneg_right hd.2 hf.2.1
    _ = (π ᵥ* lp.A) ⬝ᵥ f + s ⬝ᵥ f := add_dotProduct _ _ _
    _ = π ⬝ᵥ (lp.A *ᵥ f) + s ⬝ᵥ f := by rw [← dotProduct_mulVec]
    _ = s ⬝ᵥ f := by rw [hf.1, dotProduct_zero, zero_add]
    _ ≤ s ⬝ᵥ lp.c := dotProduct_le_dotProduct_of_nonneg_left hf.2.2 hd.1
    _ = lp.c ⬝ᵥ s := dotProduct_comm _ _

/-! ## 3. THE KEYSTONE — a `Cert-F` certificate ⇒ ε-optimality (verify-not-find). -/

/-- **`certifies_epsilon_optimal` — the certificate CERTIFIES `f` is ε-optimal.** Given a `Certified`
triple `(f, π, s)` (gap `≤ ε`), EVERY primal-feasible `f'` obeys `wᵀf' ≤ wᵀf + ε`: no feasible flow can
out-score the certified one by more than `ε`. The proof reads ONLY the certificate — `weak_duality`
applied to `f'` against the certificate's OWN dual `(π, s)` gives `wᵀf' ≤ cᵀs`, and the gap gives `cᵀs ≤
wᵀf + ε`. **Independent of how `(f, π, s)` was found** — the untrusted solver's search is never
re-examined; the linear certificate stands alone. This is the "checked output" half of the fhEgg
engine. -/
theorem certifies_epsilon_optimal (lp : FlowLP V E R) {f : E → R} {π : V → R} {s : E → R}
    (hcert : Certified lp f π s) {f' : E → R} (hf' : PrimalFeasible lp f') :
    lp.w ⬝ᵥ f' ≤ lp.w ⬝ᵥ f + lp.ε := by
  obtain ⟨_, hd, hgap⟩ := hcert
  have h1 : lp.w ⬝ᵥ f' ≤ lp.c ⬝ᵥ s := weak_duality lp hf' hd
  have h2 : lp.c ⬝ᵥ s ≤ lp.ε + lp.w ⬝ᵥ f := sub_le_iff_le_add.mp hgap
  calc lp.w ⬝ᵥ f' ≤ lp.c ⬝ᵥ s := h1
    _ ≤ lp.ε + lp.w ⬝ᵥ f := h2
    _ = lp.w ⬝ᵥ f + lp.ε := by rw [add_comm]

/-- **`gap_nonneg` — a certified gap is `≥ 0`.** Weak duality at the certified `f` against its own dual
gives `wᵀf ≤ cᵀs`, i.e. `cᵀs − wᵀf ≥ 0`. So a "certificate" asserting a strictly negative gap is
impossible, and the target `ε` it certifies is forced `≥ 0`. -/
theorem gap_nonneg (lp : FlowLP V E R) {f : E → R} {π : V → R} {s : E → R}
    (hf : PrimalFeasible lp f) (hd : DualFeasible lp π s) :
    0 ≤ lp.c ⬝ᵥ s - lp.w ⬝ᵥ f :=
  sub_nonneg.mpr (weak_duality lp hf hd)

/-! ## 4. NON-VACUITY, positive polarity — the worked 3-cycle circulation (over `ℤ`).

The directed triangle `0→1→2→0`, edges `e0,e1,e2`. The incidence `A` (row = vertex, `+1` in-edge,
`−1` out-edge) makes `A f = 0` the node-conservation "in = out". A uniform flow `f = (1,1,1)` circulates;
capacities `c = (1,1,1)` cap it; weights `w = (1,1,1)` (`wᵀf` = total volume). The optimum is `f =
(1,1,1)`, value `3`. Dual certificate `π = 0`, `s = (1,1,1)` gives `cᵀs = 3 = wᵀf` — a TIGHT (`gap = 0`)
certificate of the exact optimum. -/

/-- The `3×3` incidence matrix of the directed triangle `0→1→2→0` (rows = vertices, cols = edges):
edge `e` leaves vertex `e` (`−1`) and enters vertex `e+1 (mod 3)` (`+1`). So the columns are
`e₀=[-1,1,0]ᵀ`, `e₁=[0,-1,1]ᵀ`, `e₂=[1,0,-1]ᵀ`, and `A f = 0` ⇔ `f` is a circulation (in = out at
every node). -/
def ringA : Matrix (Fin 3) (Fin 3) ℤ := fun i e =>
  if i = e then -1 else if (i : ℕ) = ((e : ℕ) + 1) % 3 then 1 else 0

/-- The worked circulation LP: unit weights, unit capacities, exact target `ε = 0` (certify the true
optimum, not merely ε-close). -/
def ringLP : FlowLP (Fin 3) (Fin 3) ℤ :=
  { A := ringA, w := fun _ => 1, c := fun _ => 1, ε := 0 }

/-- The optimal circulation: one unit of flow all the way around the cycle. -/
def ringF : Fin 3 → ℤ := fun _ => 1
/-- The dual potentials — all zero (the triangle is balanced). -/
def ringπ : Fin 3 → ℤ := fun _ => 0
/-- The dual slacks — one per edge, saturating `Aᵀπ + s ≥ w` at `s = w`. -/
def ringS : Fin 3 → ℤ := fun _ => 1

/-- **THE CERTIFICATE VERIFIES — the worked triple is `Certified` with gap exactly `0`.** `f = (1,1,1)`
is a capacity-respecting circulation, `(π, s) = (0, (1,1,1))` is dual-feasible, and `cᵀs − wᵀf = 3 − 3 =
0 ≤ ε = 0`. A concrete, non-vacuous `Cert-F` certificate of a real optimum. -/
theorem ringCert_valid : Certified ringLP ringF ringπ ringS := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · funext i; fin_cases i <;>
      simp [ringLP, ringA, ringF, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro i; fin_cases i <;> simp [ringF]
  · intro i; fin_cases i <;> simp [ringLP, ringF]
  · intro i; fin_cases i <;> simp [ringS]
  · intro i; fin_cases i <;>
      simp [ringLP, ringA, ringπ, ringS, Matrix.vecMul, dotProduct]
  · simp [ringLP, ringF, ringS, dotProduct]

/-- **THE KEYSTONE, INSTANTIATED — the certificate proves `(1,1,1)` is optimal.** Every primal-feasible
`f'` has `wᵀf' ≤ wᵀ(1,1,1) + 0 = 3`: no circulation in the unit box beats a total volume of `3`.
`certifies_epsilon_optimal` on the worked certificate — the untrusted solver's `(1,1,1)` is proven
optimal by the linear certificate alone. -/
theorem ringF_optimal {f' : Fin 3 → ℤ} (hf' : PrimalFeasible ringLP f') :
    ringLP.w ⬝ᵥ f' ≤ 3 := by
  have h := certifies_epsilon_optimal ringLP ringCert_valid hf'
  simpa [ringLP, ringF, dotProduct, Fin.sum_univ_three] using h

/-! ## 5. NON-VACUITY, negative polarity — the teeth (an unsound triple is REFUSED). -/

/-- A NON-CONSERVING flow: `1` on edge `e0` only. `A f`'s node-0 row reads `−1 ≠ 0` (flow leaves node 0
and never returns) — not a circulation. -/
def leakF : Fin 3 → ℤ := fun e => if e = 0 then 1 else 0

/-- **TOOTH (conservation): a non-circulating `f` is REFUSED.** `leakF` puts flow on one edge with no
return leg, so `A f ≠ 0` — it fails `PrimalFeasible`, hence cannot anchor any certificate. The
conservation half of `Cert-F` has real refusing power: value cannot leak out of the cycle. -/
theorem leakF_infeasible : ¬ PrimalFeasible ringLP leakF := by
  rintro ⟨hAf, -, -⟩
  have h0 := congrFun hAf 0
  simp [ringLP, ringA, leakF, Matrix.mulVec, dotProduct] at h0

/-- **TOOTH (the certificate cannot certify a NON-OPTIMAL `f`).** Suppose the zero flow `f = 0` (feasible,
value `0`) carried a `Cert-F` certificate at `ε = 0`. Then `certifies_epsilon_optimal` would force EVERY
feasible `f'` to score `≤ 0` — but the genuine circulation `(1,1,1)` scores `3 > 0`. So NO dual can
certify the sub-optimal zero flow as optimal: the certificate is sound in the strong sense that it
refuses to certify a flow that is not actually ε-best. (`0` is `PrimalFeasible` — a real feasible point,
not a straw man.) -/
theorem zeroFlow_not_certifiable (π s : Fin 3 → ℤ) :
    ¬ Certified ringLP (fun _ => 0) π s := by
  intro hcert
  have hf' : PrimalFeasible ringLP ringF := ringCert_valid.1
  have h := certifies_epsilon_optimal ringLP hcert hf'
  -- h : 3 ≤ 0 + 0, refuted by simp
  simp [ringLP, ringF, dotProduct] at h

/-- **TOOTH (gap > ε): an off-optimal primal with a valid dual is REFUSED.** Pair the zero flow with the
honest dual `(π, s) = (0, (1,1,1))`: it is primal- and dual-feasible, but `cᵀs − wᵀf = 3 − 0 = 3 > 0 =
ε`, so the gap clause fails — not `Certified`. A large duality gap is exactly the certificate detecting
"this flow is `3` short of optimal." -/
theorem zeroFlow_gap_refused : ¬ Certified ringLP (fun _ => 0) ringπ ringS :=
  zeroFlow_not_certifiable ringπ ringS

/-! ## 6. EMITTABILITY — the certificate check as linear AIR `Constraint`s (`Dregg2.Circuit`).

The `Cert-F` check is a LINEAR circuit: conservation rows `A f = 0` (arithmetic gates, one per vertex)
plus the gap `cᵀs − wᵀf` (one linear functional). Size `O(m + nnz A)`, NOT `O(T·m)`. Wire layout for the
3-cycle: `f e = var e` (wires 0,1,2), `s e = var (3 + e)` (wires 3,4,5). -/

open Dregg2.Circuit

/-- Lay a certificate's primal `f` and dual slack `s` out as an AIR witness assignment: `f` on wires
0–2, `s` on wires 3–5. -/
def encodeCert (f s : Fin 3 → ℤ) : Assignment
  | 0 => f 0 | 1 => f 1 | 2 => f 2
  | 3 => s 0 | 4 => s 1 | 5 => s 2
  | _ => 0

/-- **The conservation gates** `A f = 0` for the 3-cycle, as arithmetic `Constraint`s: node 0 `f₂ = f₀`,
node 1 `f₀ = f₁`, node 2 `f₁ = f₂` (the incidence rows `−f₀+f₂=0`, `f₀−f₁=0`, `f₁−f₂=0`). One gate per
vertex — `O(m)`. -/
def consRows : ConstraintSystem :=
  [ { lhs := .var 2, rhs := .var 0 },
    { lhs := .var 0, rhs := .var 1 },
    { lhs := .var 1, rhs := .var 2 } ]

/-- **The gap as a single linear functional** `cᵀs − wᵀf = (s₀+s₁+s₂) − (f₀+f₁+f₂)` (unit `w`, `c`), as
one `Expr` over the witness wires. This is the "the gap is a LINEAR check" claim, emitted. -/
def gapExpr : Expr :=
  .add (.add (.var 3) (.add (.var 4) (.var 5)))
       (.mul (.const (-1)) (.add (.var 0) (.add (.var 1) (.var 2))))

/-- **The gap `Expr` computes exactly `cᵀs − wᵀf`** on any encoded certificate — the emitted functional
is faithful (linear, `O(m + nnz A)`). -/
theorem gapExpr_eval (f s : Fin 3 → ℤ) :
    gapExpr.eval (encodeCert f s) = ringLP.c ⬝ᵥ s - ringLP.w ⬝ᵥ f := by
  simp [gapExpr, Expr.eval, encodeCert, ringLP, dotProduct, Fin.sum_univ_three]
  ring

/-- **The emitted TIGHT certificate check** — the three conservation gates (`consRows`) plus the
exact-optimum gate `gap = 0` (`ε = 0`). The general `gap ≤ ε` rides the standard AIR range/comparison
gadget (`Dregg2.Bignum`); the tight optimal case is this exact arithmetic gate. -/
def certCircuit : ConstraintSystem :=
  [ { lhs := .var 2, rhs := .var 0 },
    { lhs := .var 0, rhs := .var 1 },
    { lhs := .var 1, rhs := .var 2 },
    { lhs := gapExpr, rhs := .const 0 } ]

/-- **THE EMIT BRIDGE — the AIR system is `satisfied` ⇔ the certificate's arithmetic (equality) part
holds.** `satisfied certCircuit (encodeCert f s)` iff `f` conserves (`f₀=f₁=f₂`, i.e. `A f = 0`) AND the
gap is exactly `0`. So checking the circuit IS checking the certificate — the linear-constraint emission
is faithful, on the worked instance. -/
theorem certCircuit_sound (f s : Fin 3 → ℤ) :
    satisfied certCircuit (encodeCert f s)
      ↔ (f 2 = f 0 ∧ f 0 = f 1 ∧ f 1 = f 2) ∧ gapExpr.eval (encodeCert f s) = 0 := by
  simp only [satisfied, certCircuit, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, Constraint.holds, Expr.eval, encodeCert]
  tauto

/-- **THE VALID CERTIFICATE IS ACCEPTED by the emitted circuit** — the worked optimal certificate
satisfies `certCircuit` (conserves, gap `0`). The positive emit polarity. -/
theorem certCircuit_accepts_valid : satisfied certCircuit (encodeCert ringF ringS) := by
  rw [certCircuit_sound]
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  rw [gapExpr_eval]
  simp [ringLP, ringF, ringS, dotProduct]

/-- **A gap-violating certificate is REJECTED by the emitted circuit** — the zero flow against the honest
dual has emitted gap `3 ≠ 0`, so it fails `certCircuit`. The circuit's gap gate has the same refusing
power as the semantic `Certified` (`zeroFlow_gap_refused`). -/
theorem certCircuit_rejects_gap : ¬ satisfied certCircuit (encodeCert (fun _ => 0) ringS) := by
  rw [certCircuit_sound]
  rintro ⟨-, hg⟩
  rw [gapExpr_eval] at hg
  simp [ringLP, ringS, dotProduct] at hg

/-! ### `#guard` smoke — the certificate arithmetic is COMPUTED, not asserted. -/

-- the worked certificate's gap is exactly 0 (tight optimum):
#guard gapExpr.eval (encodeCert ringF ringS) == 0
-- the zero flow against the honest dual has gap 3 (= how far from optimal it is):
#guard gapExpr.eval (encodeCert (fun _ => 0) ringS) == 3
-- the objective at the optimum is 3 (total circulating volume):
#guard (ringLP.w ⬝ᵥ ringF) == 3
-- the emitted conservation system has one gate per vertex (m = 3) plus one gap gate:
#guard certCircuit.length == 4

/-! ### Axiom hygiene — the `Cert-F` keystones pinned kernel-clean. -/

#assert_all_clean [Market.weak_duality, Market.certifies_epsilon_optimal, Market.gap_nonneg,
  Market.ringCert_valid, Market.ringF_optimal, Market.leakF_infeasible,
  Market.zeroFlow_not_certifiable, Market.zeroFlow_gap_refused, Market.gapExpr_eval,
  Market.certCircuit_sound, Market.certCircuit_accepts_valid, Market.certCircuit_rejects_gap]

end Market
