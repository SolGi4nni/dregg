/-
# Dregg2.Exec.CellReal — the living cell on the per-asset executor.

`livingCellA_sound`: the per-asset executor (`execFullForestA`, 46-effect auth-gated tree) — on its
conserving turns — is bisimilar to its per-asset conservation oracle from every state, over unbounded
coinductive time. The observation is the per-asset vector `recTotalAssetWithEscrow` (not a scalar: a
scalar would let a mint of asset B net a burn of asset A). `cellA_h_step` is discharged by the proved
`execFullForestA_conserves_per_asset`. `livingCellA_obs_invariant` carries the badge invariant along
the entire unbounded adversarial schedule.

The supply generators (mint/burn/bridgeMint) are the DISCLOSED boundary, not a leak:
`livingCellA_supply_disclosed` proves a committed forest evolves the per-asset badge by exactly its
disclosed delta (`execFullForestA_ledger_per_asset`), so the constant-oracle bisimulation lives on
the `Δ=0` conserving fragment with supply moves fully accounted on the chain.
-/
import Dregg2.Exec.Cell
import Dregg2.Exec.FullForest

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority

/-! ## Step 1 — the real per-asset living cell as a coalgebra. -/

/-- The per-asset observation (the badge): the conserved per-asset vector `recTotalAssetWithEscrow`
(balance + escrow held, per asset class). A scalar total would miss cross-asset laundering. -/
def cellObsA (s : RecChainedState) : AssetId → ℤ := fun b => recTotalAssetWithEscrow s.kernel b

/-- A conserving forest: per-asset net delta `0` in every asset (transfers / delegations /
escrow-neutral). The supply generators (mint/burn/bridgeMint) are the disclosed boundary, excluded;
they move the badge only by the disclosed amount (`livingCellA_supply_disclosed`). This subtype is
the turn alphabet over which the per-asset conservation law is invariant. -/
def ConservingForest : Type :=
  { f : FullForestA // ∀ b, turnLedgerDeltaAsset (lowerForestA f) b = 0 }

/-- The successor: run the conserving forest via `execFullForestA`; stay-put on an inadmissible
turn (fail-closed self-loop) — totality gives a clean `TurnCoalg`. -/
def cellNextA (s : RecChainedState) (cf : ConservingForest) : RecChainedState :=
  (execFullForestA s cf.1).getD s

/-- The real living cell as a `Boundary.TurnCoalg`: carrier = the per-asset kernel state,
observation = the per-asset vector, transition = `execFullForestA` (46-effect auth-gated tree),
over conserving turns. The structure map is the executor's behaviour over unbounded time. -/
def livingCellA : TurnCoalg (AssetId → ℤ) ConservingForest where
  Carrier := RecChainedState
  step s := (cellObsA s, cellNextA s)

/-! ## Step 2 — the per-asset conservation oracle (the abstract reference) + the bridge. -/

/-- The per-asset conservation oracle: the per-asset vector, invariant (self-loops) — the
conservation law as a constant reference coalgebra. The living cell is sound iff bisimilar to this:
its per-asset badge never drifts from conservation over unbounded time. -/
def perAssetOracle : TurnCoalg (AssetId → ℤ) ConservingForest where
  Carrier := AssetId → ℤ
  step v := (v, fun _ => v)

/-- The decode/replay map into the spec: a cell decodes to its per-asset badge. -/
def cellOracleA (s : RecChainedState) : AssetId → ℤ := cellObsA s

/-- The oracle commutes with observation — definitional. -/
theorem cellA_h_obs (s : RecChainedState) :
    livingCellA.obs s = perAssetOracle.obs (cellOracleA s) := rfl

/-- The oracle commutes with transition: a committed conserving forest preserves every asset's total
(`execFullForestA_conserves_per_asset`, discharged by the conserving subtype's `∀ b, Δ = 0`), and
the stay-put self-loop trivially conserves. -/
theorem cellObsA_next (s : RecChainedState) (cf : ConservingForest) :
    cellObsA (cellNextA s cf) = cellObsA s := by
  funext b
  show recTotalAssetWithEscrow (cellNextA s cf).kernel b = recTotalAssetWithEscrow s.kernel b
  unfold cellNextA
  cases h : execFullForestA s cf.1 with
  | some s' => simp only [Option.getD_some]
               exact execFullForestA_conserves_per_asset s s' cf.1 b h (cf.2 b)
  | none    => simp only [Option.getD_none]

theorem cellA_h_step (s : RecChainedState) (cf : ConservingForest) :
    cellOracleA (livingCellA.next s cf) = perAssetOracle.next (cellOracleA s) cf := by
  show cellObsA (cellNextA s cf) = cellObsA s
  exact cellObsA_next s cf

/-- The golden-oracle bisimulation over an arbitrary turn alphabet `Adm`. A decode map commuting
with observation + transition implies `Impl` is sound relative to `Spec`. Witness relation: "`y`
is the oracle image of `x`." -/
theorem bisim_of_oracleA {Obs Adm : Type} (Impl Spec : TurnCoalg Obs Adm)
    (oracle : Impl.Carrier → Spec.Carrier)
    (h_obs  : ∀ x, Impl.obs x = Spec.obs (oracle x))
    (h_step : ∀ x t, oracle (Impl.next x t) = Spec.next (oracle x) t)
    (x : Impl.Carrier) : Sound Impl Spec x := by
  refine ⟨fun a b => b = oracle a, oracle x, ⟨?_, ?_⟩, rfl⟩
  · rintro a b rfl; exact h_obs a
  · rintro a b rfl t; exact (h_step a t).symm

/-- **`livingCellA_sound`** — the per-asset executor is bisimilar to its per-asset conservation
oracle from every state: its per-asset badge never drifts from conservation over unbounded coinductive
time. `execFullForestA_conserves_per_asset` routed through `cellA_h_step` is what makes the
bisimulation hold. -/
theorem livingCellA_sound (s : RecChainedState) : Sound livingCellA perAssetOracle s :=
  bisim_of_oracleA livingCellA perAssetOracle cellOracleA cellA_h_obs cellA_h_step s

/-! ## Step 3 — the disclosed supply boundary + the temporal νF invariant. -/

/-- **`livingCellA_supply_disclosed`** — a committed forest (including mint/burn) evolves the
per-asset badge by exactly the turn's disclosed per-asset delta — no hidden change. The badge
"drift" on supply ops is fully accounted by the disclosed actions on the chain; the conserving
fragment is precisely where this delta is `0`. (`execFullForestA_ledger_per_asset`.) -/
theorem livingCellA_supply_disclosed (s s' : RecChainedState) (f : FullForestA) (b : AssetId)
    (h : execFullForestA s f = some s') :
    cellObsA s' b = cellObsA s b + turnLedgerDeltaAsset (lowerForestA f) b :=
  execFullForestA_ledger_per_asset s s' f b h

/-- An infinite adversarial schedule of conserving turns. -/
def SchedA : Type := Nat → ConservingForest

/-- The unbounded trajectory: unfold the living cell along the schedule. -/
def trajA (s : RecChainedState) (sched : SchedA) : Nat → RecChainedState
  | 0     => s
  | n + 1 => livingCellA.next (trajA s sched n) (sched n)

/-- **`livingCellA_obs_invariant`** — driven by any infinite stream of conserving turns, the
executor's per-asset badge never drifts from its initial value at any index of the unbounded
trajectory. The coinductive "sound forever" on `execFullForestA`. -/
theorem livingCellA_obs_invariant (s : RecChainedState) (sched : SchedA) :
    ∀ n, cellObsA (trajA s sched n) = cellObsA s := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show cellObsA (cellNextA (trajA s sched k) (sched k)) = cellObsA s
      rw [cellObsA_next]; exact ih

/-! ## It runs (`#eval`) — the real living cell on a genuine conserving transfer (non-vacuity). -/

/-- A conserving forest: actor 0 transfers 30 of asset 0 from cell 0 to cell 1 — a single
`balanceA`, no children. Per-asset net delta is `0` in every asset, so it inhabits `ConservingForest`:
the turn alphabet is non-empty and the bisimulation is non-vacuous. -/
def transferCF : ConservingForest :=
  ⟨⟨.balanceA ⟨0, 0, 1, 30⟩ 0, []⟩, by
    intro b
    simp only [lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ledgerDeltaAsset, add_zero]⟩

#guard ((execFullForestA fma0 transferCF.1).isSome)  --  true (the conserving transfer commits)
#eval (execFullForestA fma0 transferCF.1).map (fun s' => cellObsA s' 0)  -- the asset-0 badge AFTER the turn
#eval cellObsA fma0 0                                                  -- the asset-0 badge BEFORE — EQUAL (conserved)
#guard ((execFullForestA fma0 transferCF.1).map (fun s' => decide (cellObsA s' 0 = cellObsA fma0 0))) == some true  --  some true

/-! ## Axiom hygiene — keystones pinned to the standard kernel triple. -/

#assert_axioms bisim_of_oracleA
#assert_axioms cellObsA_next
#assert_axioms cellA_h_step
#assert_axioms livingCellA_sound
#assert_axioms livingCellA_supply_disclosed
#assert_axioms livingCellA_obs_invariant

end Dregg2.Exec
