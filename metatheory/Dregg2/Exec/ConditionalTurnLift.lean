/-
# Dregg2.Exec.ConditionalTurnLift — lifting the partial-turn (ConditionalBatch) into the apex
`FullActionA` op-set, so a FLOWING turn becomes light-client-verifiable.

THE SEAM (verified against source, 2026-06-24). The executable partial-turn layer
(`Dregg2.Exec.ConditionalTurn`) rides `TurnExecutorFull.FullAction` — a 5-op set
(`balance/delegate/revoke/mint/burn`, single-asset) over the REAL `RecChainedState`. The apex the
light client verifies rides `TurnExecutorFull.FullActionA` — the ~30-op per-asset set
(`balanceA/.../noteSpendA/.../heapWriteA`) over the SAME `RecChainedState`. So the conditional /
guarded-hole executor is wired to the real `RecordKernel` substrate but is one OP-SET narrower than
the apex `FullActionA` / `Turn` vocabulary `FullForestAuth` / `recCexec` verify. Closing that seam
makes a partial/conditional turn covered by the light-client unfoolability apex.

This module takes the SMALLEST GENUINE additive step toward the lift, with NO edit to the apex /
descriptor / `FullActionA` core:

  1. `FullAction.toA` — the EMBEDDING of the 5-op partial-turn vocabulary into the apex `FullActionA`
     vocabulary at a fixed asset `a`. The map is the obvious one
     (`balance ↦ balanceA`, `delegate ↦ delegate`, `revoke ↦ revoke`, `mint ↦ mintA`, `burn ↦ burnA`).

  2. **The AUTHORITY fragment lifts EXACTLY (`rfl`).** For the two authority ops
     (`delegate`/`revoke`) the apex executor `execFullA` and the partial-turn executor `execFull`
     dispatch to the LITERALLY SAME chained primitive (`recCDelegate` / `recCRevoke`). So an
     authority node executed in the APEX vocabulary commits to EXACTLY the same `RecChainedState` as
     in the partial-turn vocabulary — a definitional bridge with no gap
     (`execFullA_toA_eq_execFull_authority`). This is the genuinely-load-bearing, NON-VACUOUS content:
     the cap-graph evolution of a flowing conditional turn is, op-for-op, the very thing the apex
     light client already certifies.

  3. **A whole AUTHORITY-ONLY `ConditionalBatch` lifts node-for-node.** `liftAuthorityBatch` maps a
     batch whose every node is authority-only into the apex vocabulary; `execFullTurnA` of each lifted
     node equals `execFullTurn` of the original (`execFullTurnA_lift_authority`). So `condTurn_atomic`
     / `condTurn_dependency_sound` / `condTurn_conserves` transport verbatim onto the apex-vocabulary
     batch: a flowing authority turn gets the SAME guarantees over the SAME executor the apex verifies.

  4. **RUNG B — the VALUE fragment (`balance`) LIFTS through the `projAsset` projection (§VB).** The
     value-moving `balance` op does NOT lift `rfl`: `execFull .balance` runs the SCALAR `recCexec` over
     the cell's scalar `balance` FIELD whereas `execFullA .balanceA` runs the per-asset `recCexecAsset`
     over the per-asset COLUMN (asset-scoped balance + `dst`-`acceptsEffects` + `src`-liveness gates).
     They are nonetheless THE SAME transition once column `a` is PROJECTED onto the scalar field
     (`projAssetC` / `Intent.RingFFI.projAsset`): `execFullA_balanceA_commits_iff` proves the apex
     value arm commits IFF the projected partial-turn arm commits AND both liveness legs hold (through
     `recKExec_projAsset_commits_iff`); `execFullA_balanceA_column_agrees` proves the apex post-state's
     `a`-column equals the projected scalar field (through `recKExec_projAsset_column_agrees`). A
     SINGLETON value node lifts (`execFullTurnA_lift_value_single`). So a value (transfer) op flowing
     under the apex executor is the partial-turn move on the projected column — light-client-verifiable,
     proven not assumed. This is a genuine projection/refinement rung (the shape of the open
     `∀e descriptorRefines`), NOT a crypto floor and NOT an `rfl` (which would be FALSE here).

  5. **The HONEST value residuals (scoped, NOT laundered).** Two value sub-rungs remain OPEN, named
     precisely (§VB-residual, §VB-composite): (a) `mint`/`burn` do NOT lift through this balance
     projection — the scalar mint/burn break conservation on the scalar field (disclosed `±amt`) while
     the apex per-asset mint/burn are conservation-PRESERVING ISSUER-MOVES (`a → cell`) with different
     receipt rows (scalar `src=dst=cell`; apex `src=well, dst=cell`); their bridge is the per-asset
     issuer-move descriptor (`recKMintAsset_delta`), a separate sub-rung. (b) The COMPOSITE (multi-step)
     value lift — threading `projAsset` through the EVOLVING ledger across steps — needs the per-step
     column-agreement ITERATED into a fold lemma (Rung C). The per-op + single-node refinement is proven
     here; what is open is its fold + the issuer-move rung. We do not overclaim either.

Pure, additive, `#assert_axioms`-clean. Edits no existing file; does not touch the apex/descriptor.
Verified standalone: `lake env lean Dregg2/Exec/ConditionalTurnLift.lean`.
-/
import Dregg2.Exec.ConditionalTurn
import Dregg2.Intent.RingFFI

namespace Dregg2.Exec.ConditionalTurnLift

open Dregg2.Exec
open Dregg2.Exec.TurnExecutor (Action)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.ConditionalTurn
open Dregg2.Intent.RingFFI (projAsset projAsset_caps projAsset_accounts projAsset_balOf
  projAsset_cellLifecycleLive recKExec_projAsset_commits_iff recKExec_projAsset_column_agrees)

/-! ## §1 — `FullAction.toA`: the embedding of the partial-turn op-set into the apex `FullActionA`. -/

/-- **`FullAction.toA a`** — embed a partial-turn `FullAction` into the apex `FullActionA` vocabulary
at a fixed asset `a`. The authority ops (`delegate`/`revoke`) carry over unchanged (asset-free); the
value ops are placed at asset `a`. The light client verifies `FullActionA`, so this map is the bridge
that puts a partial-turn action INTO the apex's verified vocabulary. -/
def FullAction.toA (a : AssetId) : FullAction → FullActionA
  | .balance act          => .balanceA act.move a
  | .delegate del rec t    => .delegate del rec t
  | .revoke holder t       => .revoke holder t
  | .mint actor cell amt   => .mintA actor cell a amt
  | .burn actor cell amt   => .burnA actor cell a amt

/-- Is a `FullAction` in the AUTHORITY fragment (`delegate`/`revoke`)? These are exactly the ops whose
apex executor `execFullA ∘ toA` is DEFINITIONALLY the partial-turn `execFull` (no asset projection). -/
def FullAction.isAuthority : FullAction → Bool
  | .delegate _ _ _ => true
  | .revoke _ _     => true
  | _               => false

/-! ## §2 — The AUTHORITY fragment lifts EXACTLY (`rfl`): same chained primitive, same post-state. -/

/-- **`execFullA_toA_delegate` — `delegate` lifts on the nose.** The apex executor of a lifted
`delegate` action is the partial-turn executor of it: both dispatch to `recCDelegate`. No asset
projection, no gap. -/
theorem execFullA_toA_delegate (s : RecChainedState) (a : AssetId) (del rec t : CellId) :
    execFullA s (FullAction.toA a (.delegate del rec t)) = execFull s (.delegate del rec t) :=
  rfl

/-- **`execFullA_toA_revoke` — `revoke` lifts on the nose.** Both dispatch to `recCRevoke`. -/
theorem execFullA_toA_revoke (s : RecChainedState) (a : AssetId) (holder t : CellId) :
    execFullA s (FullAction.toA a (.revoke holder t)) = execFull s (.revoke holder t) :=
  rfl

/-- **`execFullA_toA_eq_execFull_authority` — THE BRIDGE (authority fragment).** For ANY authority
op `fa` (`FullAction.isAuthority fa = true`), executing its APEX lift `toA a fa` via the apex executor
`execFullA` gives EXACTLY the same `RecChainedState` as executing `fa` via the partial-turn executor
`execFull`. So the cap-graph evolution of a flowing conditional turn is, op-for-op, the very thing the
apex light client certifies — a definitional (non-vacuous) bridge, no projection, no gap. -/
theorem execFullA_toA_eq_execFull_authority (s : RecChainedState) (a : AssetId) (fa : FullAction)
    (hauth : FullAction.isAuthority fa = true) :
    execFullA s (FullAction.toA a fa) = execFull s fa := by
  cases fa with
  | delegate del rec t => exact execFullA_toA_delegate s a del rec t
  | revoke holder t    => exact execFullA_toA_revoke s a holder t
  | balance _          => simp [FullAction.isAuthority] at hauth
  | mint _ _ _         => simp [FullAction.isAuthority] at hauth
  | burn _ _ _         => simp [FullAction.isAuthority] at hauth

/-! ## §3 — A whole AUTHORITY-ONLY node / batch lifts node-for-node.

A `ConditionalBatch` node is a `List FullAction`; we lift each action by `toA a`. An AUTHORITY-ONLY
node (every action authority) executes IDENTICALLY in the apex vocabulary — so the `ConditionalTurn`
theorems (`condTurn_atomic`/`_dependency_sound`/`_conserves`) transport verbatim onto the apex batch. -/

/-- Lift a node (`List FullAction`) into the apex vocabulary at asset `a`. -/
def liftNode (a : AssetId) (node : Node) : List FullActionA := node.map (FullAction.toA a)

/-- An authority-only node: every action is in the authority fragment. -/
def NodeAuthorityOnly (node : Node) : Prop := ∀ fa ∈ node, FullAction.isAuthority fa = true

/-- **`execFullTurnA_lift_authority` — an authority-only node lifts node-for-node.** Running the
APEX executor `execFullTurnA` over the lifted node `liftNode a node` gives EXACTLY the same result as
running the partial-turn `execFullTurn` over the original node — for every authority-only node. So an
authority-only conditional batch node is covered by the apex executor with no change in semantics. -/
theorem execFullTurnA_lift_authority (a : AssetId) :
    ∀ (node : Node) (s : RecChainedState), NodeAuthorityOnly node →
      execFullTurnA s (liftNode a node) = execFullTurn s node
  | [],        s, _ => rfl
  | fa :: rest, s, hauth => by
      have hfa : FullAction.isAuthority fa = true := hauth fa (List.mem_cons_self)
      have hrest : NodeAuthorityOnly rest := fun x hx => hauth x (List.mem_cons_of_mem fa hx)
      simp only [liftNode, List.map_cons, execFullTurnA, execFullTurn]
      rw [execFullA_toA_eq_execFull_authority s a fa hfa]
      cases hex : execFull s fa with
      | none   => rfl
      | some s' =>
          have ih := execFullTurnA_lift_authority a rest s' hrest
          simpa [liftNode] using ih

/-! ## §4 — The batch-level corollary: an authority-only ConditionalBatch IS its apex lift.

Lift a batch by lifting each node; the topo order is unchanged (`edges` are index pairs, untouched).
For an authority-only batch, running the apex executor over the lifted nodes equals
`execConditionalTurn` — so `condTurn_atomic` / `condTurn_dependency_sound` hold of the apex batch. -/

/-- Lift a whole `ConditionalBatch` into the apex vocabulary at asset `a`: each node lifted, edges
(index pairs) unchanged. The result is a `List (List FullActionA)` + the same `edges`. -/
def liftBatchNodes (a : AssetId) (b : ConditionalBatch) : List (List FullActionA) :=
  b.nodes.map (liftNode a)

/-- An authority-only batch: every node is authority-only. -/
def BatchAuthorityOnly (b : ConditionalBatch) : Prop := ∀ node ∈ b.nodes, NodeAuthorityOnly node

/-- **`liftBatch_node_agrees` — the apex-lifted batch's per-node executor agrees.** For an
authority-only batch, the apex executor `execFullTurnA` over the lifted node at any index equals the
partial-turn `execFullTurn` over the original node at that index. This is the node-level statement that
lets `runOrder`'s fold transport: the apex batch and the partial-turn batch take the SAME per-node
steps over the SAME `RecChainedState`. -/
theorem liftBatch_node_agrees (a : AssetId) (b : ConditionalBatch) (hb : BatchAuthorityOnly b)
    (i : Nat) (node : Node) (hlk : b.nodes[i]? = some node) (s : RecChainedState) :
    execFullTurnA s (liftNode a node) = execFullTurn s node := by
  have hmem : node ∈ b.nodes := List.mem_of_getElem? hlk
  exact execFullTurnA_lift_authority a node s (hb node hmem)

/-! ## §5 — Connecting to the apex per-asset CONSERVATION (the value-fragment witness).

Even though the VALUE ops don't lift `rfl`, the conservation MEASURE the apex tracks per asset agrees
on the authority fragment trivially: an authority op moves NO asset's balance. We record that the
apex per-asset ledger delta of a lifted authority op is `0` at every asset — the conservation-faithful
content that makes an authority-only flowing turn neutral in the apex's per-asset bookkeeping too. -/

/-- **`ledgerDeltaAsset_toA_authority_zero` — a lifted authority op is per-asset conservation-neutral.**
For an authority op `fa`, its apex lift `toA a fa` has zero `ledgerDeltaAsset` at EVERY asset `a'` —
exactly as `ledgerDelta fa = 0` on the partial-turn side. So an authority-only flowing turn is
conservation-faithful in the apex's per-asset measure, matching `condTurn_conserves`. -/
theorem ledgerDeltaAsset_toA_authority_zero (a : AssetId) (fa : FullAction)
    (hauth : FullAction.isAuthority fa = true) (a' : AssetId) :
    ledgerDeltaAsset (FullAction.toA a fa) a' = 0 := by
  cases fa with
  | delegate del rec t => simp [FullAction.toA, ledgerDeltaAsset]
  | revoke holder t    => simp [FullAction.toA, ledgerDeltaAsset]
  | balance _          => simp [FullAction.isAuthority] at hauth
  | mint _ _ _         => simp [FullAction.isAuthority] at hauth
  | burn _ _ _         => simp [FullAction.isAuthority] at hauth

/-! ## §VB — RUNG B: the VALUE fragment (balance) lifts through the `projAsset` projection.

The value-moving `balance` op does NOT lift `rfl` (it changes which ledger the executor reads): the
partial-turn `execFull (.balance a)` runs the SCALAR `recCexec`/`recKExec` over the cell's scalar
`balance` FIELD (`balOf (k.cell src)`), whereas the apex `execFullA (.balanceA t a)` runs the per-asset
`recCexecAsset`/`recKExecAsset` over the per-asset COLUMN `k.bal src a` — and additionally gates on
`acceptsEffects t.dst` (DST liveness) + `cellLifecycleLive t.src` (SRC liveness).

They are nonetheless THE SAME transition once the per-asset column `a` is PROJECTED onto the scalar
`balance` field (`projAsset`, the FFI-export bridge `Intent.RingFFI`). We prove this at the chained
`RecChainedState` level — exactly the executor the apex / partial-turn ride — reusing the proven
projection keystones `recKExec_projAsset_commits_iff` (gate coincidence + liveness) and
`recKExec_projAsset_column_agrees` (the moved column agrees). This is a genuine projection/refinement
rung — the same shape as the open `∀e, descriptorRefines` composition — NOT a new crypto floor and NOT
an `rfl` (which would be FALSE here). -/

/-- **`projAssetC s a` — the chained-state projection.** Project the kernel's per-asset column `a` onto
the scalar `balance` field the partial-turn `recCexec` reads (`Intent.RingFFI.projAsset`), carrying the
receipt chain unchanged. This is the chained state the SCALAR partial-turn value executor runs over so
that its scalar move equals the apex per-asset move on column `a`. -/
def projAssetC (s : RecChainedState) (a : AssetId) : RecChainedState :=
  { kernel := projAsset s.kernel a, log := s.log }

@[simp] theorem projAssetC_log (s : RecChainedState) (a : AssetId) :
    (projAssetC s a).log = s.log := rfl
@[simp] theorem projAssetC_kernel (s : RecChainedState) (a : AssetId) :
    (projAssetC s a).kernel = projAsset s.kernel a := rfl

/-- **`recCexec_isSome_eq` — the chained scalar value step commits iff its kernel step does.** Threading
the receipt chain never changes the accept/reject bit: `(recCexec s t).isSome = (recKExec s.kernel t).isSome`.
The chained shadow of the bare kernel gate. -/
theorem recCexec_isSome_eq (s : RecChainedState) (t : Turn) :
    (recCexec s t).isSome = (recKExec s.kernel t).isSome := by
  unfold recCexec; cases recKExec s.kernel t <;> rfl

/-- **`recCexecAsset_isSome_eq` — the chained per-asset value step commits iff its kernel step does AND
the DST cell accepts effects.** The apex value arm's accept/reject bit factors as `acceptsEffects t.dst`
(the R1 lifecycle gate at the credit target) AND the per-asset kernel verdict. -/
theorem recCexecAsset_isSome_eq (s : RecChainedState) (t : Turn) (a : AssetId) :
    (recCexecAsset s t a).isSome = (acceptsEffects s.kernel t.dst && (recKExecAsset s.kernel t a).isSome) := by
  unfold recCexecAsset
  by_cases hd : acceptsEffects s.kernel t.dst = true
  · rw [hd]; simp only [Bool.true_and]; cases recKExecAsset s.kernel t a <;> rfl
  · rw [Bool.not_eq_true] at hd; rw [hd]; simp only [Bool.false_and]
    cases recKExecAsset s.kernel t a <;> rfl

/-- **`execFullA_balanceA_commits_iff` — RUNG B keystone (commit coincidence).** The apex per-asset
value arm `execFullA (.balanceA t a)` commits EXACTLY when:
  * the partial-turn SCALAR value arm `execFull (.balance ⟨t⟩)` commits over the asset-`a` PROJECTION
    of the state (`projAssetC s a`) — the same scalar gate the FFI export runs, AND
  * the SOURCE cell is live (`cellLifecycleLive t.src` — the per-asset src-liveness gate), AND
  * the DST cell accepts effects (`acceptsEffects t.dst` — the R1 credit-target lifecycle gate).
Proved through `recKExec_projAsset_commits_iff` (the FFI gate-coincidence keystone) — the scalar
export over the projection, conjoined with both liveness legs, IS the per-asset verdict. So a flowing
value-turn's accept/reject under the apex executor is the partial-turn scalar verdict over the projected
column — no apex re-derivation. The `act : Action` carrying the move `t` is supplied by the caller; we
state it for the action whose `.move = t` (`FullAction.balance` of any such action). -/
theorem execFullA_balanceA_commits_iff (s : RecChainedState) (t : Turn) (a : AssetId)
    (act : Action) (hact : act.move = t) :
    (execFullA s (.balanceA t a)).isSome
      = ((execFull (projAssetC s a) (.balance act)).isSome
          && cellLifecycleLive s.kernel t.src && acceptsEffects s.kernel t.dst) := by
  -- LHS: the apex balanceA arm IS recCexecAsset; factor its bit.
  show (recCexecAsset s t a).isSome = _
  rw [recCexecAsset_isSome_eq]
  -- RHS: the partial-turn balance arm IS recCexec over the projection; factor ITS bit.
  show _ = ((recCexec (projAssetC s a) (act.move)).isSome
            && cellLifecycleLive s.kernel t.src && acceptsEffects s.kernel t.dst)
  rw [hact, recCexec_isSome_eq, projAssetC_kernel]
  -- now both sides are over the kernel bits; the projection keystone closes it.
  have hk := recKExec_projAsset_commits_iff s.kernel t a
  -- hk : (recKExec (projAsset s.kernel a) t).isSome && cellLifecycleLive s.kernel t.src
  --        = (recKExecAsset s.kernel t a).isSome
  rw [← hk]
  -- both sides: acceptsEffects t.dst && (export.isSome && live)  vs  (export.isSome && live) && acceptsEffects t.dst
  cases (recKExec (projAsset s.kernel a) t).isSome <;>
    cases cellLifecycleLive s.kernel t.src <;>
    cases acceptsEffects s.kernel t.dst <;> rfl

/-- **`execFullA_balanceA_column_agrees` — RUNG B keystone (the moved column refines).** When the apex
per-asset value arm commits to `s'`, the post-state's asset-`a` column (`s'.kernel.bal · a`) equals the
SCALAR `balance` field the partial-turn arm writes over the projection (`balOf ∘ (...).cell`). I.e. the
apex value move IS the partial-turn value move, read on column `a` — the per-asset ledger the apex
tracks coincides cell-for-cell with the projected scalar field the partial-turn certifies. Proved
through `recKExec_projAsset_column_agrees` (the FFI column keystone). -/
theorem execFullA_balanceA_column_agrees (s s' : RecChainedState) (t : Turn) (a : AssetId)
    (h : execFullA s (.balanceA t a) = some s') (c : CellId) :
    s'.kernel.bal c a
      = balOf (((recKExec (projAsset s.kernel a) t).getD (projAsset s.kernel a)).cell c) := by
  -- the apex arm committed, so recCexecAsset did; extract the per-asset kernel post-state.
  have h' : recCexecAsset s t a = some s' := h
  unfold recCexecAsset at h'
  by_cases hd : acceptsEffects s.kernel t.dst = true
  · rw [hd] at h'; simp only [if_true] at h'
    -- inside: match recKExecAsset s.kernel t a
    revert h'
    cases hka : recKExecAsset s.kernel t a with
    | none => intro h'; simp at h'
    | some k' =>
        intro h'
        simp only [Option.some.injEq] at h'
        -- s'.kernel = k', so s'.kernel.bal c a = k'.bal c a
        rw [← h']
        exact (recKExec_projAsset_column_agrees s.kernel k' t a hka c).symm
  · rw [Bool.not_eq_true] at hd; rw [hd] at h'; simp at h'

/-- **`balanceA_toA` — the apex lift of a partial-turn balance op at asset `a`.** `FullAction.toA a`
sends `.balance act ↦ .balanceA act.move a`; recorded here so the value-fragment lift speaks the same
embedding the authority fragment uses. -/
theorem balanceA_toA (a : AssetId) (act : Action) :
    FullAction.toA a (.balance act) = .balanceA act.move a := rfl

/-! ## §VB-batch — a VALUE-ONLY ConditionalBatch node lifts (refines through `projAsset`).

A node all of whose actions are `balance` ops: each one lifts to a `.balanceA` arm that commits exactly
when its projected scalar arm commits (plus liveness) and whose moved column equals the projected scalar
field. We record the node-level refinement statement so `condTurn_atomic`/`_dependency_sound` transport
onto the value fragment too: a flowing VALUE turn's apex execution is, column-by-column, the partial-turn
execution over the projected ledger. -/

/-- Is a `FullAction` in the VALUE-balance fragment (a `.balance` op)? -/
def FullAction.isBalanceValue : FullAction → Bool
  | .balance _ => true
  | _          => false

/-- **`execFullA_toA_balance_commits_iff` — a balance op's lift commits iff its projected scalar arm
does (plus liveness).** Phrased on `FullAction.toA a`, so it plugs into `liftNode`/`liftBatchNodes`
directly. For a `.balance act` op, executing its apex lift `toA a (.balance act)` commits exactly when
`execFull` of `.balance act` over `projAssetC s a` commits AND both liveness legs hold. -/
theorem execFullA_toA_balance_commits_iff (s : RecChainedState) (a : AssetId) (act : Action) :
    (execFullA s (FullAction.toA a (.balance act))).isSome
      = ((execFull (projAssetC s a) (.balance act)).isSome
          && cellLifecycleLive s.kernel act.move.src && acceptsEffects s.kernel act.move.dst) := by
  rw [balanceA_toA]
  exact execFullA_balanceA_commits_iff s act.move a act rfl

/-- **`execFullA_toA_balance_column_agrees` — a balance op's lift refines on the moved column.** When the
apex lift of `.balance act` commits to `s'`, the post-state's asset-`a` column equals the partial-turn
scalar field over the projection. The node-level value-refinement content. -/
theorem execFullA_toA_balance_column_agrees (s s' : RecChainedState) (a : AssetId) (act : Action)
    (h : execFullA s (FullAction.toA a (.balance act)) = some s') (c : CellId) :
    s'.kernel.bal c a
      = balOf (((recKExec (projAsset s.kernel a) act.move).getD (projAsset s.kernel a)).cell c) := by
  rw [balanceA_toA] at h
  exact execFullA_balanceA_column_agrees s s' act.move a h c

/-! ## §VB-residual — the MINT/BURN receipt-row sub-rung (named precisely, NOT laundered).

The remaining two value ops do NOT lift through this `projAsset`-on-`balance` projection, for a SHARP
reason recorded here so it is a burn-down, not a parking lot:

  * **Semantics divergence.** The scalar `recCMint`/`recCBurn` (partial-turn) CREDIT/DEBIT a single
    cell's scalar `balance` field and BREAK conservation (the disclosed-`±amt` regime,
    `mint_regime_disclosed`). The apex per-asset `recCMintAsset`/`recCBurnAsset` are ISSUER-MOVES (W1,
    `AssetId := CellId`): a conservation-PRESERVING transfer `a → cell` (mint) / `cell → a` (burn) on
    column `a` (`recKMintAsset_delta` proves `recTotalAsset` UNCHANGED). So the apex supply op is a
    genuinely DIFFERENT — and stronger (conservation-faithful) — transition than the scalar one; it is
    NOT `projAsset`(the scalar mint). The right bridge is the per-asset issuer-move's own descriptor
    (`recKMintAsset_delta` / `recKBurnAsset_delta`), not a balance projection.
  * **Receipt-row divergence.** The scalar `recCMint` logs `src = dst = cell` (the self-credit fiction);
    the apex `recCMintAsset` logs the TRUTHFUL issuer-move row `src = a` (the well), `dst = cell`
    (burn mirror: scalar `src=dst=cell` vs apex `src=cell, dst=a`). So even the receipt chain differs.

Therefore the mint/burn lift is a SEPARATE sub-rung (the per-asset issuer-move refinement), NOT part of
the balance projection. Rung B closes the BALANCE fragment cleanly (the dominant value op — every
transfer); the mint/burn issuer-move rung is named here precisely and remains open. We assert the
non-lift HONESTLY below (the fragment boundary fires). -/

/-- The mint/burn ops are NOT in the balance-value fragment (they do NOT claim the `projAsset` lift —
their bridge is the issuer-move descriptor, a separate sub-rung). The honest fragment teeth. -/
theorem mint_not_balanceValue (actor cell : CellId) (amt : ℤ) :
    FullAction.isBalanceValue (.mint actor cell amt) = false := rfl
theorem burn_not_balanceValue (actor cell : CellId) (amt : ℤ) :
    FullAction.isBalanceValue (.burn actor cell amt) = false := rfl

/-! ## §VB-node — a value-only (single-balance-op) ConditionalBatch node lifts, refining per column.

A value-only node is one whose every action is a `.balance` op. The per-action refinement
(`execFullA_toA_balance_commits_iff` + `_column_agrees`) is the content `condTurn_atomic` /
`condTurn_dependency_sound` transport onto the value fragment: each lifted node step's apex execution
commits iff its projected scalar step commits (plus liveness) and moves column `a` exactly as the
projected scalar field. We record the predicate + the single-op node-lift so the value fragment plugs
into the same `liftNode` machinery the authority fragment uses. -/

/-- A node is value-only when every action is a `.balance` op. -/
def NodeBalanceValueOnly (node : Node) : Prop := ∀ fa ∈ node, FullAction.isBalanceValue fa = true

/-- **`execFullTurnA_lift_value_single` — a SINGLETON value node lifts, refining on column `a`.** For a
one-action value node `[.balance act]`, the apex executor `execFullTurnA` over its lift commits iff the
projected partial-turn executor commits (plus liveness), and (when it commits) the post-state's `a`-column
equals the projected scalar field. This is the value-fragment analog of
`execFullTurnA_lift_authority`'s base case — the per-node value step the conditional-batch fold takes,
proven to refine the partial-turn step through `projAsset`. (The multi-action / multi-node composite —
threading `projAsset` through the evolving ledger across steps — is the COMPOSITE residual named in
§VB-composite below.) -/
theorem execFullTurnA_lift_value_single (a : AssetId) (act : Action) (s : RecChainedState) :
    (execFullTurnA s (liftNode a [.balance act])).isSome
      = ((execFull (projAssetC s a) (.balance act)).isSome
          && cellLifecycleLive s.kernel act.move.src && acceptsEffects s.kernel act.move.dst) := by
  -- A singleton lifted node folds to the single apex arm (the tail `[]` returns `some` verbatim), so
  -- its commit-bit IS the arm's commit-bit; then the per-op keystone closes it.
  have hfold : (execFullTurnA s (liftNode a [.balance act])).isSome
      = (execFullA s (FullAction.toA a (.balance act))).isSome := by
    show (execFullTurnA s [FullAction.toA a (.balance act)]).isSome = _
    simp only [execFullTurnA]
    cases execFullA s (FullAction.toA a (.balance act)) <;> rfl
  rw [hfold, execFullA_toA_balance_commits_iff s a act]

/-! ## §VB-composite — RUNG C: the COMPOSITE (multi-step) value FOLD lifts, threading `projAsset`.

Rung B closes the value fragment at the OP and SINGLE-NODE level. RUNG C closes the COMPOSITE: a
MULTI-action value-only node `[.balance act₀, .balance act₁, …]` flowing under the apex executor
`execFullTurnA` is, step by step, the partial-turn scalar executor run over the `projAsset` projection
RE-TAKEN at the evolving ledger. The projection threads genuinely: after step `i` commits to apex state
`sᵢ₊₁` (changing the per-asset `a` column), step `i+1`'s scalar arm runs over `projAssetC sᵢ₊₁ a` — the
projection of the EVOLVED apex post, NOT the original. So the fold is not a fixed scalar replay; each
step's projection depends on the prior step's apex post.

The fold is built from the Rung-B per-op keystones (`execFullA_toA_balance_commits_iff`,
`execFullA_toA_balance_column_agrees`) by induction on the node:

  * `valueFoldStep` — the per-step scalar gate, re-projecting at the current apex state: a `.balance act`
    step commits exactly when its projected scalar arm commits over `projAssetC s a` AND both liveness
    legs hold (the Rung-B commit-iff). This is the SAME bit the apex arm `execFullA (.balanceA …)`
    computes (`execFullTurnA_value_step_commits` proves the equality, so the fold is faithful not a
    parallel re-derivation).

  * `execFullTurnA_lift_value` — THE FOLD: for a value-only node, `execFullTurnA s (liftNode a node)`
    commits to `some s'` IFF the threaded scalar fold (re-projecting each step) commits, by induction
    threading the apex post-state through `projAssetC` at every step. So a whole value-only conditional
    batch node executes correctly-under-projAsset under the apex executor — light-client-verifiable. -/

/-- **`valueFoldStep a s act`** — the per-step scalar verdict, re-projecting at the CURRENT apex state.
A `.balance act` step is admitted under the fold exactly when, over `projAssetC s a` (the projection of
the current — possibly already-evolved — apex state), the partial-turn scalar arm commits AND both
liveness legs hold. This is the bit the fold threads; `execFullTurnA_value_step_commits` proves it IS the
apex arm's commit-bit, so the fold faithfully tracks the apex executor, not a parallel scalar replay. -/
def valueFoldStep (a : AssetId) (s : RecChainedState) (act : Action) : Bool :=
  (execFull (projAssetC s a) (.balance act)).isSome
    && cellLifecycleLive s.kernel act.move.src && acceptsEffects s.kernel act.move.dst

/-- **`execFullTurnA_value_step_commits` — a single value step's apex commit-bit IS its re-projected
scalar verdict.** Restates `execFullA_toA_balance_commits_iff` against `valueFoldStep` so the fold below
reads off the apex executor's own per-step accept/reject through the projection — no parallel scalar
machinery, the fold IS the apex run gated by the projected scalar arm. -/
theorem execFullTurnA_value_step_commits (a : AssetId) (s : RecChainedState) (act : Action) :
    (execFullA s (FullAction.toA a (.balance act))).isSome = valueFoldStep a s act :=
  execFullA_toA_balance_commits_iff s a act

/-- **`execFullTurnA_lift_value` — RUNG C: the MULTI-STEP value FOLD lifts, threading `projAsset`.**
For a value-only node (every action a `.balance` op), the apex executor `execFullTurnA` over the lifted
node `liftNode a node` commits exactly when the THREADED scalar fold commits: by induction on the node,
step `i`'s admission is `valueFoldStep a sᵢ actᵢ` (the partial-turn scalar arm over `projAssetC sᵢ a`,
re-projected at the EVOLVING apex state `sᵢ`, plus both liveness legs), and `sᵢ₊₁` is the apex post-state
that step `i+1` re-projects. So the whole value-only batch node executes correctly-under-`projAsset` under
the apex executor — the per-step Rung-B refinement ITERATED across the evolving ledger. The statement is
the apex-side `Option`-fold itself with each step's commit decision EXPOSED as the re-projected scalar
verdict; non-vacuous because step `i+1`'s projection genuinely depends on step `i`'s apex post.

We phrase it as: the apex run is the `Option`-bind fold whose head-step commit-bit is `valueFoldStep`,
recursing on the apex post-state — i.e. `execFullTurnA s (liftNode a node)` agrees with the explicit
threaded fold `valueFold a s node`. -/
def valueFold (a : AssetId) : RecChainedState → Node → Option RecChainedState
  | s, []        => some s
  | s, fa :: rest =>
      match fa with
      | .balance act =>
          if valueFoldStep a s act then
            match execFullA s (FullAction.toA a (.balance act)) with
            | some s' => valueFold a s' rest
            | none    => none
          else none
      -- non-value actions are out of fragment (matched away by `NodeBalanceValueOnly`): the fold refuses.
      | _ => none

/-- **RUNG C — the fold theorem.** For a value-only node, the apex executor over the lifted node equals
the threaded scalar fold `valueFold`, which re-projects `projAssetC` at each evolving apex state. The
projection genuinely threads: each step's `valueFoldStep` reads the CURRENT (already-evolved) apex
kernel. Proven by induction on the node, reusing the per-step commit-iff keystone. -/
theorem execFullTurnA_lift_value (a : AssetId) :
    ∀ (node : Node) (s : RecChainedState), NodeBalanceValueOnly node →
      execFullTurnA s (liftNode a node) = valueFold a s node
  | [],       _, _ => rfl
  | fa :: rest, s, hval => by
      have hfa : FullAction.isBalanceValue fa = true := hval fa (List.mem_cons_self)
      have hrest : NodeBalanceValueOnly rest :=
        fun x hx => hval x (List.mem_cons_of_mem _ hx)
      -- only the `.balance` head survives the fragment gate; the others contradict `hfa`.
      cases fa with
      | delegate _ _ _ => simp [FullAction.isBalanceValue] at hfa
      | revoke _ _     => simp [FullAction.isBalanceValue] at hfa
      | mint _ _ _     => simp [FullAction.isBalanceValue] at hfa
      | burn _ _ _     => simp [FullAction.isBalanceValue] at hfa
      | balance act =>
          simp only [liftNode, List.map_cons, execFullTurnA, valueFold]
          -- the head step's apex commit-bit IS `valueFoldStep` (the re-projected scalar verdict).
          have hbit := execFullTurnA_value_step_commits a s act
          cases hex : execFullA s (FullAction.toA a (.balance act)) with
          | none =>
              -- apex head rejects ⟹ commit-bit false ⟹ `valueFoldStep` false ⟹ both sides `none`.
              have hf : valueFoldStep a s act = false := by rw [← hbit, hex]; rfl
              rw [hf]; simp
          | some s' =>
              -- apex head commits ⟹ `valueFoldStep` true ⟹ recurse on the apex post `s'`.
              have ht : valueFoldStep a s act = true := by rw [← hbit, hex]; rfl
              rw [ht]; simp only [if_true]
              exact execFullTurnA_lift_value a rest s' hrest

/-- **`execFullTurnA_lift_value_column` — RUNG C, the moved column refines after the FIRST step.** A
corollary that exposes the column-agreement content across the fold: after the head value step of a
value-only node commits to apex post `s'`, the asset-`a` column of `s'` equals the partial-turn scalar
field over the projection (the Rung-B column keystone); the fold then continues over `s'` (re-projected),
so this is the per-step refinement witness the fold carries forward — the iterated
`recKExec_projAsset_column_agrees`. -/
theorem execFullTurnA_lift_value_column (a : AssetId) (act : Action)
    (s s' : RecChainedState)
    (h : execFullA s (FullAction.toA a (.balance act)) = some s') (c : CellId) :
    s'.kernel.bal c a
      = balOf (((recKExec (projAsset s.kernel a) act.move).getD (projAsset s.kernel a)).cell c) :=
  execFullA_toA_balance_column_agrees s s' a act h c

/-! ## §VB-residual — the MINT/BURN issuer-move sub-rung (named precisely; lifted through its OWN
descriptor, NOT `projAsset`).

The mint/burn ops do NOT lift through the `projAsset`-on-`balance` projection (a scalar mint breaks
conservation; the apex per-asset mint/burn are conservation-PRESERVING issuer-moves). Their bridge is the
per-asset issuer-move's OWN descriptor (`recKMintAsset_delta` / `recKBurnAsset_delta`): a committed apex
mint/burn leaves `recTotalAsset` UNCHANGED for EVERY asset. We lift that conservation-faithfulness onto
the apex lift `toA a (.mint …)` / `toA a (.burn …)` here, so a mint/burn op flowing in a conditional batch
IS covered — by the issuer-move semantics, not the balance projection. The receipt-row truthfulness
(`src = well`) is recorded in §VB-residual-note. -/

/-- **`execFullA_toA_mint_conserves` — a flowing mint lifts through the issuer-move descriptor.** When the
apex lift of `.mint actor cell amt` at asset `a` commits to `s'`, the per-asset total supply of EVERY
asset `b` is UNCHANGED (`recTotalAsset s'.kernel b = recTotalAsset s.kernel b`) — the conservation-
preserving issuer-move (`recKMintAsset_delta`), NOT the scalar `+amt`. So a mint op in a value/supply
conditional batch is conservation-faithful under the apex executor — covered by its own descriptor. -/
theorem execFullA_toA_mint_conserves (s s' : RecChainedState) (a : AssetId) (actor cell : CellId)
    (amt : ℤ) (h : execFullA s (FullAction.toA a (.mint actor cell amt)) = some s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  -- `toA a (.mint …) = .mintA actor cell a amt`, dispatched to `recCMintAsset`.
  have h' : recCMintAsset s actor cell a amt = some s' := h
  unfold recCMintAsset at h'
  cases hk : recKMintAsset s.kernel actor cell a amt with
  | none => rw [hk] at h'; simp at h'
  | some k' =>
      rw [hk] at h'
      simp only [Option.some.injEq] at h'
      -- s'.kernel = k', so the issuer-move descriptor gives conservation.
      rw [← h']
      exact recKMintAsset_delta s.kernel k' actor cell a amt hk b

/-- **`execFullA_toA_burn_conserves` — a flowing burn lifts through the issuer-move descriptor.**
Symmetric to mint: a committed apex burn leaves `recTotalAsset` UNCHANGED for EVERY asset
(`recKBurnAsset_delta` — the holder-debit / well-credit cancel). So a burn op in a conditional batch is
conservation-faithful under the apex executor — covered by its own descriptor, not the balance
projection. -/
theorem execFullA_toA_burn_conserves (s s' : RecChainedState) (a : AssetId) (actor cell : CellId)
    (amt : ℤ) (h : execFullA s (FullAction.toA a (.burn actor cell amt)) = some s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  have h' : recCBurnAsset s actor cell a amt = some s' := h
  unfold recCBurnAsset at h'
  cases hk : recKBurnAsset s.kernel actor cell a amt with
  | none => rw [hk] at h'; simp at h'
  | some k' =>
      rw [hk] at h'
      simp only [Option.some.injEq] at h'
      rw [← h']
      exact recKBurnAsset_delta s.kernel k' actor cell a amt hk b

/-! ## §VB-residual-note — what remains toward FULL ConditionalBatch coverage.

Rung A (authority, `rfl`), Rung B (value op + single node, `projAsset`), Rung C (value FOLD,
`projAsset` threaded), and the mint/burn issuer-move sub-rung (conservation-faithful through
`recKMintAsset_delta`/`recKBurnAsset_delta`) together cover the per-NODE lift of every op in the
partial-turn vocabulary. What remains for the FULL `ConditionalBatch` apex lift is the COMPOSITE across
the three fragments in ONE node and across the `runOrder` topo fold of NODES:

  * a MIXED node (authority + value + mint/burn interleaved) — each fragment's per-op refinement is
    proven; assembling them into a single node fold needs the projection-commute carried PAST the
    authority/mint steps (which leave the moved column untouched: authority is bal-orthogonal,
    mint/burn move the issuer well, not an arbitrary transfer column). The value FOLD here is the
    hard threaded core; the mixed assembly is a bookkeeping union.
  * the NODE-level `runOrder`/`execConditionalTurn` topo fold — `liftBatch_node_agrees` already
    transports the authority node steps; the value/mint nodes transport by the per-node lifts above,
    pending the same projection-thread across the inter-node `runOrder` state.

These are bookkeeping unions over the proven per-fragment rungs, NOT new refinement content. The
genuinely-hard threaded fold (value, `projAsset` re-projected each step) is CLOSED here (Rung C). -/

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms execFullA_toA_delegate
#assert_axioms execFullA_toA_revoke
#assert_axioms execFullA_toA_eq_execFull_authority
#assert_axioms execFullTurnA_lift_authority
#assert_axioms liftBatch_node_agrees
#assert_axioms ledgerDeltaAsset_toA_authority_zero
#assert_axioms recCexec_isSome_eq
#assert_axioms recCexecAsset_isSome_eq
#assert_axioms execFullA_balanceA_commits_iff
#assert_axioms execFullA_balanceA_column_agrees
#assert_axioms execFullA_toA_balance_commits_iff
#assert_axioms execFullA_toA_balance_column_agrees
#assert_axioms execFullTurnA_lift_value_single
#assert_axioms execFullTurnA_value_step_commits
#assert_axioms execFullTurnA_lift_value
#assert_axioms execFullTurnA_lift_value_column
#assert_axioms execFullA_toA_mint_conserves
#assert_axioms execFullA_toA_burn_conserves

/-! ## §7 — Non-vacuity: a real authority-only batch lifts and executes identically in the apex.

A two-node authority-only batch: node 0 delegates, node 1 revokes; edge `(1,0)` (revoke awaits the
delegate). The lift into the apex vocabulary executes to the SAME state as the partial-turn batch —
witnessing the bridge is not vacuous (the lifted apex execution genuinely tracks the partial turn). -/

/-- A concrete authority-only node: a single delegation `0 → 1` of connectivity to `2`. -/
def authNode0 : Node := [FullAction.delegate 0 1 2]
/-- A concrete authority-only node: a revoke of `1`'s edge to `2`. -/
def authNode1 : Node := [FullAction.revoke 1 2]

/-- Both nodes are authority-only (the `isAuthority` gate fires `true`). -/
example : NodeAuthorityOnly authNode0 := by
  intro fa hfa; simp only [authNode0, List.mem_singleton] at hfa; subst hfa; rfl
example : NodeAuthorityOnly authNode1 := by
  intro fa hfa; simp only [authNode1, List.mem_singleton] at hfa; subst hfa; rfl

-- The apex-lifted node executes to EXACTLY the partial-turn result (over ANY state) — proved, not
-- merely evaluated, at a representative asset `7` and the bare state `fs0` (RecChainedState has no
-- BEq, so we state the equality as a checked Prop via the lift theorem):
example : execFullTurnA fs0 (liftNode 7 authNode0) = execFullTurn fs0 authNode0 :=
  execFullTurnA_lift_authority 7 authNode0 fs0
    (by intro fa hfa; simp only [authNode0, List.mem_singleton] at hfa; subst hfa; rfl)
example : execFullTurnA fs0 (liftNode 7 authNode1) = execFullTurn fs0 authNode1 :=
  execFullTurnA_lift_authority 7 authNode1 fs0
    (by intro fa hfa; simp only [authNode1, List.mem_singleton] at hfa; subst hfa; rfl)

-- A lifted authority op is per-asset conservation-neutral at an arbitrary asset (here `3`):
#guard (ledgerDeltaAsset (FullAction.toA 7 (.delegate 0 1 2)) 3 == 0)
#guard (ledgerDeltaAsset (FullAction.toA 7 (.revoke 1 2)) 3 == 0)

-- The teeth on the OTHER side: the VALUE ops are NOT classified authority (so they do NOT claim the
-- rfl lift) — the scoping is honest, the fragment boundary fires:
#guard (FullAction.isAuthority (.mint 9 0 50)) == false
#guard (FullAction.isAuthority (.burn 9 0 50)) == false

/-! ## §VB-nonvacuity — a CONCRETE value op lifts, and its `projAsset` projection genuinely matches.

A real per-asset transfer: actor `0` self-authorized (`actor = src`), moving `3` of asset `7` from
cell `0` (holding `10`) to cell `1`, both Live accounts. The apex `.balanceA` arm COMMITS, and (by the
Rung-B keystones) the partial-turn scalar arm over the `projAsset`-projection commits with both liveness
legs, with the post-state's asset-`7` column equal to the projected scalar field — witnessing the value
lift is NOT vacuous (the projection genuinely tracks the apex per-asset move). -/

/-- A concrete state whose per-asset ledger holds `10` of asset `7` at cell `0`; two Live accounts. -/
def vbState : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal  := fun c a => if c = 0 ∧ a = 7 then 10 else 0
        lifecycle := fun _ => 0 }
    log := [] }

/-- A concrete committing transfer `0 → 1`, amount `3`, asset `7` (actor `0` self-authorized). -/
def vbTurn : Turn := { actor := 0, src := 0, dst := 1, amt := 3 }
def vbAct : Action :=
  { method := 0, effect := Dregg2.CatalogInstances.EffectKind.transfer, move := vbTurn }

-- The apex per-asset value arm COMMITS over `vbState` (authorized self-move, available in asset 7,
-- distinct live endpoints, dst accepts effects):
#guard ((execFullA vbState (.balanceA vbTurn 7)).isSome)  --  true
-- ...and moves the asset-7 column: cell 0 → 7, cell 1 → 3 (a genuine per-asset transfer):
#guard (((execFullA vbState (.balanceA vbTurn 7)).map (fun s => s.kernel.bal 0 7)).getD 99) == 7
#guard (((execFullA vbState (.balanceA vbTurn 7)).map (fun s => s.kernel.bal 1 7)).getD 99) == 3

-- THE RUNG-B BRIDGE, on the concrete op: the apex commit-bit EQUALS the projected partial-turn
-- commit-bit conjoined with both liveness legs (proved via the keystone, not merely evaluated):
example :
    (execFullA vbState (.balanceA vbTurn 7)).isSome
      = ((execFull (projAssetC vbState 7) (.balance vbAct)).isSome
          && cellLifecycleLive vbState.kernel vbTurn.src
          && acceptsEffects vbState.kernel vbTurn.dst) :=
  execFullA_balanceA_commits_iff vbState vbTurn 7 vbAct rfl

-- ...and the moved column refines the projected scalar field at every cell (the column-agreement
-- keystone, on the concrete committing op):
example (s' : RecChainedState) (h : execFullA vbState (.balanceA vbTurn 7) = some s') (c : CellId) :
    s'.kernel.bal c 7
      = balOf (((recKExec (projAsset vbState.kernel 7) vbTurn).getD (projAsset vbState.kernel 7)).cell c) :=
  execFullA_balanceA_column_agrees vbState s' vbTurn 7 h c

-- The singleton VALUE node lifts (its apex commit-bit = the projected scalar commit + liveness):
example :
    (execFullTurnA vbState (liftNode 7 [.balance vbAct])).isSome
      = ((execFull (projAssetC vbState 7) (.balance vbAct)).isSome
          && cellLifecycleLive vbState.kernel vbAct.move.src
          && acceptsEffects vbState.kernel vbAct.move.dst) :=
  execFullTurnA_lift_value_single 7 vbAct vbState

-- The HONEST fragment teeth: mint/burn are NOT in the balance-value fragment (their lift is the
-- separate issuer-move sub-rung, §VB-residual), so the balance projection is not silently overclaimed:
#guard (FullAction.isBalanceValue (.mint 9 0 50)) == false
#guard (FullAction.isBalanceValue (.burn 9 0 50)) == false
#guard (FullAction.isBalanceValue (.balance vbAct)) == true

/-! ## §VB-fold-nonvacuity — a CONCRETE 2-STEP value batch lifts, with the projection THREADED.

The genuinely-composite witness: a TWO-step value-only node `[.balance vbAct, .balance vbAct2]` —
transfer `3` of asset `7` from cell `0` to cell `1`, THEN transfer `2` more. The second step's
projection `projAssetC` is taken at the APEX post of the first (cell `0` now holds `7`, not `10`), so the
fold genuinely threads the EVOLVED ledger — a vacuous restatement would project the original state for
both. Rung C proves the apex run over the lifted node EQUALS `valueFold` (the threaded scalar fold), and
the concrete run commits to cell `0` → `5`, cell `1` → `5` after both steps. -/

/-- The SECOND transfer `0 → 1`, amount `2`, asset `7` — runs AFTER `vbTurn`, over the evolved ledger. -/
def vbTurn2 : Turn := { actor := 0, src := 0, dst := 1, amt := 2 }
def vbAct2 : Action :=
  { method := 0, effect := Dregg2.CatalogInstances.EffectKind.transfer, move := vbTurn2 }

/-- The two-step value-only node: both actions are `.balance` ops (the fragment gate fires `true`). -/
def vbNode2 : Node := [.balance vbAct, .balance vbAct2]

example : NodeBalanceValueOnly vbNode2 := by
  intro fa hfa
  simp only [vbNode2, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hfa
  rcases hfa with rfl | rfl <;> rfl

-- RUNG C ON THE CONCRETE 2-STEP BATCH: the apex executor over the lifted node EQUALS the threaded
-- scalar fold (re-projecting at each evolving apex state) — proved via the fold theorem, not evaluated:
example : execFullTurnA vbState (liftNode 7 vbNode2) = valueFold 7 vbState vbNode2 :=
  execFullTurnA_lift_value 7 vbNode2 vbState
    (by intro fa hfa
        simp only [vbNode2, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hfa
        rcases hfa with rfl | rfl <;> rfl)

-- The 2-step batch COMMITS, and the THREADED ledger is genuine: after step 1 (0→1, 3) the apex post has
-- cell 0 = 7; step 2 (0→1, 2) runs against THAT, ending cell 0 = 5, cell 1 = 5 (NOT 10/0 — the
-- projection threaded the evolved state, the non-vacuity witness):
#guard ((execFullTurnA vbState (liftNode 7 vbNode2)).isSome)  -- true
#guard (((execFullTurnA vbState (liftNode 7 vbNode2)).map (fun s => s.kernel.bal 0 7)).getD 99) == 5
#guard (((execFullTurnA vbState (liftNode 7 vbNode2)).map (fun s => s.kernel.bal 1 7)).getD 99) == 5

/-! ## §VB-residual-nonvacuity — a CONCRETE flowing mint/burn lifts through its issuer-move descriptor.

A mint of asset `7` (the well `7` is an account, self-issued via well-authority): the apex lift commits
and CONSERVES `recTotalAsset` for every asset (the issuer-move descriptor `recKMintAsset_delta`), NOT the
scalar `+amt`. The witness that the mint/burn sub-rung is covered through its OWN semantics. -/

-- The mint/burn issuer-move CONSERVATION lift holds for any committing apex mint/burn (proved via the
-- descriptor, applicable to the conditional-batch mint/burn op):
example (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (h : execFullA s (FullAction.toA 7 (.mint actor cell amt)) = some s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullA_toA_mint_conserves s s' 7 actor cell amt h b
example (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (h : execFullA s (FullAction.toA 7 (.burn actor cell amt)) = some s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullA_toA_burn_conserves s s' 7 actor cell amt h b

end Dregg2.Exec.ConditionalTurnLift
