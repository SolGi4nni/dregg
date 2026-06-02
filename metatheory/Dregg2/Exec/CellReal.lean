/-
# Dregg2.Exec.CellReal — the LIVING CELL on the REAL per-asset executor (the coalgebraic crown).

`Exec/Cell.lean` proved the living-cell bisimulation (`livingCell_sound`) on the **toy** 2-account
*scalar* kernel (`cexec`), and its own header named the honest l4v sequencing: *"get the living cell
+ soundness right on the proved core first, THEN grow the state."* This module does the grow — onto
the SHIPPED executor: `execFullForestA` (the 46-effect, per-asset, auth-gated tree of #138 / FILL-J).

Three changes from the toy, each load-bearing:
* the observation (the badge crossing a vat boundary) is no longer a scalar total but the **per-asset
  VECTOR** `recTotalAssetWithEscrow` — the FILL-1 no-laundering measure (a scalar would let a mint of
  asset B net a burn of asset A);
* the transition is the real `execFullForestA` (stay-put on an inadmissible turn, the Moore self-loop);
* the bridge `cellA_h_step` is discharged by the **proved** `execFullForestA_conserves_per_asset`.

So `livingCellA_sound` says: the real per-asset executor — on its **conserving** turns — is bisimilar
to its per-asset conservation law over unbounded (coinductive) time ("no drifting future"), and
`livingCellA_obs_invariant` carries that badge invariant along the ENTIRE unbounded adversarial
schedule (the temporal νF face of `Proof/CoinductiveAdversary`, here on the real machine).

The supply generators (mint/burn/bridgeMint) are the **DISCLOSED boundary**, NOT a leak:
`livingCellA_supply_disclosed` proves a committed forest evolves the per-asset badge by EXACTLY its
disclosed delta (`execFullForestA_ledger_per_asset`) — which is precisely why the constant-oracle
bisimulation lives on the `Δ=0` conserving fragment, with supply moves fully accounted on the chain.
-/
import Dregg2.Exec.Cell
import Dregg2.Exec.FullForest

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority

/-! ## Step 1 — the real per-asset living cell as a coalgebra. -/

/-- The per-asset **OBSERVATION** (the badge): the conserved per-asset vector
`recTotalAssetWithEscrow` (balance + escrow held, per asset class). NOT a scalar total — the FILL-1
VECTOR is what makes "no drifting future" catch a cross-asset launder. -/
def cellObsA (s : RecChainedState) : AssetId → ℤ := fun b => recTotalAssetWithEscrow s.kernel b

/-- A **CONSERVING** forest: per-asset net delta `0` in EVERY asset (transfers / delegations /
escrow-neutral). The supply generators (mint/burn/bridgeMint) are the DISCLOSED boundary, excluded —
they move the badge, but only by the disclosed amount (`livingCellA_supply_disclosed`). This subtype
is the turn alphabet over which the per-asset conservation law is INVARIANT. -/
def ConservingForest : Type :=
  { f : FullForestA // ∀ b, turnLedgerDeltaAsset (lowerForestA f) b = 0 }

/-- The successor: run the conserving forest via the REAL `execFullForestA`; stay-put on an
inadmissible turn (fail-closed self-loop) — totality ⇒ a clean `TurnCoalg`. -/
def cellNextA (s : RecChainedState) (cf : ConservingForest) : RecChainedState :=
  (execFullForestA s cf.1).getD s

/-- **The real living cell** as a `Boundary.TurnCoalg`: carrier = the REAL per-asset kernel state,
observation = the per-asset vector, transition = `execFullForestA` (the 46-effect auth-gated tree),
over conserving turns. The structure map IS the shipped executor's behaviour over unbounded time. -/
def livingCellA : TurnCoalg (AssetId → ℤ) ConservingForest where
  Carrier := RecChainedState
  step s := (cellObsA s, cellNextA s)

/-! ## Step 2 — the per-asset conservation oracle (the abstract reference) + the bridge. -/

/-- The per-asset **CONSERVATION ORACLE**: the per-asset vector, INVARIANT (self-loops) — the
conservation law as a constant reference coalgebra. The living cell is SOUND iff bisimilar to this:
its per-asset badge never drifts from conservation over unbounded time. -/
def perAssetOracle : TurnCoalg (AssetId → ℤ) ConservingForest where
  Carrier := AssetId → ℤ
  step v := (v, fun _ => v)

/-- The decode/replay map into the spec: a cell decodes to its per-asset badge. -/
def cellOracleA (s : RecChainedState) : AssetId → ℤ := cellObsA s

/-- The oracle commutes with observation — definitional. -/
theorem cellA_h_obs (s : RecChainedState) :
    livingCellA.obs s = perAssetOracle.obs (cellOracleA s) := rfl

/-- The oracle commutes with transition — **where the per-asset conservation lands**: a committed
conserving forest preserves EVERY asset's total (`execFullForestA_conserves_per_asset`, discharged by
the conserving subtype's `∀ b, Δ = 0`), and the stay-put self-loop trivially conserves. PROVED. -/
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

/-- The golden-oracle bisimulation over ANY turn alphabet — `Cell.bisim_of_oracle` (which is
specialised to the toy `Turn`) generalised to an arbitrary `Adm`, so it applies to the real executor's
`ConservingForest` alphabet. A decode map commuting with observation + transition ⇒ `Impl` is sound
relative to `Spec`. Witness relation: "`y` is the oracle image of `x`." PROVED. -/
theorem bisim_of_oracleA {Obs Adm : Type} (Impl Spec : TurnCoalg Obs Adm)
    (oracle : Impl.Carrier → Spec.Carrier)
    (h_obs  : ∀ x, Impl.obs x = Spec.obs (oracle x))
    (h_step : ∀ x t, oracle (Impl.next x t) = Spec.next (oracle x) t)
    (x : Impl.Carrier) : Sound Impl Spec x := by
  refine ⟨fun a b => b = oracle a, oracle x, ⟨?_, ?_⟩, rfl⟩
  · rintro a b rfl; exact h_obs a
  · rintro a b rfl t; exact (h_step a t).symm

/-- **`livingCellA_sound` (PROVED) — the coalgebraic crown on the REAL executor.** The executable
per-asset, 46-effect, auth-gated forest is **bisimilar to its per-asset conservation oracle from every
state**: its per-asset badge never drifts from conservation, over unbounded (coinductive) time. The
per-asset step-completeness (`execFullForestA_conserves_per_asset`) routed through `cellA_h_step` is
exactly what makes the bisimulation hold. This is `Cell.livingCell_sound` (toy scalar) lifted onto the
SHIPPED executor with the FILL-1 per-asset VECTOR badge — the unification REORIENT §5 was missing,
now on the real machine. -/
theorem livingCellA_sound (s : RecChainedState) : Sound livingCellA perAssetOracle s :=
  bisim_of_oracleA livingCellA perAssetOracle cellOracleA cellA_h_obs cellA_h_step s

/-! ## Step 3 — the disclosed supply boundary + the temporal νF invariant. -/

/-- **`livingCellA_supply_disclosed` (PROVED) — the disclosed boundary, NOT a leak.** A committed
forest (INCLUDING mint/burn) evolves the per-asset badge by EXACTLY the turn's disclosed per-asset
delta — no HIDDEN change. So the badge "drift" on supply ops is fully accounted by the disclosed
actions on the chain; the conserving fragment above is precisely where this delta is `0` and the
constant-oracle bisimulation lives. (`execFullForestA_ledger_per_asset`, the FILL-1 vector.) -/
theorem livingCellA_supply_disclosed (s s' : RecChainedState) (f : FullForestA) (b : AssetId)
    (h : execFullForestA s f = some s') :
    cellObsA s' b = cellObsA s b + turnLedgerDeltaAsset (lowerForestA f) b :=
  execFullForestA_ledger_per_asset s s' f b h

/-- An infinite adversarial schedule of conserving turns (the same shape `Proof/CoinductiveAdversary`
drives the νF coalgebra with; `livingCellA` instantiates that frame, so its `ObsBisim`/
`stepComplete_carries_infinite` apply — here we take the direct invariant). -/
def SchedA : Type := Nat → ConservingForest

/-- The unbounded **trajectory**: unfold the living cell along the schedule (`νF` along the adversary
stream). -/
def trajA (s : RecChainedState) (sched : SchedA) : Nat → RecChainedState
  | 0     => s
  | n + 1 => livingCellA.next (trajA s sched n) (sched n)

/-- **`livingCellA_obs_invariant` (PROVED) — the temporal νF crown: NO DRIFTING FUTURE on the real
machine.** Driven by ANY infinite stream of conserving turns, the real executor's per-asset badge
NEVER drifts from its initial value — at EVERY index of the unbounded trajectory. The coinductive
"sound forever" made concrete on `execFullForestA`: a cell sound for unbounded time. -/
theorem livingCellA_obs_invariant (s : RecChainedState) (sched : SchedA) :
    ∀ n, cellObsA (trajA s sched n) = cellObsA s := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show cellObsA (cellNextA (trajA s sched k) (sched k)) = cellObsA s
      rw [cellObsA_next]; exact ih

/-! ## It runs (`#eval`) — the real living cell on a genuine conserving transfer (non-vacuity). -/

/-- A real CONSERVING forest: actor 0 transfers 30 of asset 0 from cell 0 to cell 1 — a single
`balanceA`, no children. Its per-asset net delta is `0` in every asset (a transfer moves value
between cells; the TOTAL is unchanged), so it inhabits `ConservingForest`: the turn alphabet is
non-empty, the bisimulation is non-vacuous. -/
def transferCF : ConservingForest :=
  ⟨⟨.balanceA ⟨0, 0, 1, 30⟩ 0, []⟩, by
    intro b
    simp only [lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ledgerDeltaAsset, add_zero]⟩

#eval (execFullForestA fma0 transferCF.1).isSome                      -- true (the conserving transfer commits)
#eval (execFullForestA fma0 transferCF.1).map (fun s' => cellObsA s' 0)  -- the asset-0 badge AFTER the turn
#eval cellObsA fma0 0                                                  -- the asset-0 badge BEFORE — EQUAL (conserved)
#eval (execFullForestA fma0 transferCF.1).map (fun s' => decide (cellObsA s' 0 = cellObsA fma0 0))  -- some true

/-! ## Axiom hygiene — the crown keystones pinned to the standard kernel triple (NO `sorryAx`). -/

#assert_axioms bisim_of_oracleA
#assert_axioms cellObsA_next
#assert_axioms cellA_h_step
#assert_axioms livingCellA_sound
#assert_axioms livingCellA_supply_disclosed
#assert_axioms livingCellA_obs_invariant

end Dregg2.Exec
