/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateCell — the `createCell` effect's EffectVM-row circuit, EMITTED.

`createCell` GROWS `accounts` and BORN-EMPTIES `newCell` (every per-cell slot reset: `cell`, `caps`,
`delegate`, `delegations`, `slotCaveats`, `lifecycle`, `deathCert`, `bal`), prepends a creation
receipt, and freezes the global side-tables. Its FULL universe-A soundness is
`Inst.CreateCellA.createCellA_full_sound ⇒ CreateCellSpec` (over the EffectCommit3 triple-circuit
layer, all 18 `RecordKernelState` components + log).

This module emits the EffectVM-ROW (the running `EffectVmP3Air` layout) face of `createCell` and
connects it to that universe-A guarantee through a `cellProj`-style projection — naming the
LARGE lifecycle side-effect the per-row circuit CANNOT see.

## What the EffectVM row CAN pin (finding-#2, stated

The EffectVM row carries ONLY a cell's 14-column economic state-block:
`{bal_lo, bal_hi, nonce, field[0..7], cap_root, state_commit, reserved}`. For `createCell`, the cell
the row witnesses is `newCell`, whose post-block is the BORN-EMPTY ZERO block (`bornEmptyAt` resets
`bal` to `0` and the cell record to `default`, so `balOf (default) = 0`). So the per-row circuit pins:

  * the post-block is the ZERO economic block (bal_lo = bal_hi = 0, every field/cap/reserved 0);
  * that zero block is bound into the published `state_commit` under Poseidon2 CR (the anti-ghost
    whole-state tooth — `createCellHashSites` are the same 4 ordered GROUP-4 `H4` sites the running
    prover lays for every row).

## What the EffectVM row CANNOT enforce (the boundary)

The HEART of `createCell` is OFF-ROW side-state the 14-column block does NOT carry by named offset:

  * `accounts` GROWTH (`insert newCell`) — there is no `accounts`-set column in the EffectVM row;
  * the born-empty reset of `caps` / `delegate` / `delegations` / `slotCaveats` / `lifecycle` /
    `deathCert` — these are per-cell SIDE-TABLES, not state-block columns;
  * the creation RECEIPT prepended to the log;
  * the FRESHNESS + mint-authority guard (`createCellAdmit`).

These are exactly the components `createCellA_full_sound`/`CreateCellSpec` enforce and the EffectVM
row does NOT. We connect the ONE overlap (the new cell's ECONOMIC block is born-empty zero, hence
`balOf (newCell-cell) = 0`) and FLAG the rest as off-row (`createCell_offrow_unenforced`).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem; Poseidon2 CR enters ONLY
as the named `Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are
read-only (the keystone Sound module + universe-A `accountgrowth` spec).
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.accountgrowth

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateCell

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSB eSA eSub)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState RowEncodes)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec
open Dregg2.Circuit.Spec.AccountGrowth

set_option linter.unusedVariables false

/-! ## §0 — the `createCell` selector column.

The running prover gives each effect one selector column in the GROUP-1 selector block (`sel::*`,
`0 ≤ idx < NUM_EFFECTS = 54`). `EffectVmEmit` names only `NOOP`/`TRANSFER`; we pick the next free
index for `createCell` (a LOCAL constant — we do not edit the shared IR). The faithfulness theorems
below are selector-independent (they read the state-block columns), so the exact index only matters
for the wire fingerprint. -/

/-- The `createCell` selector column index (next free after `NOOP=0`, `TRANSFER=1`). -/
def SEL_CREATECELL : Nat := 2

/-! ## §1 — the BORN-EMPTY (frozen-to-zero) per-row gates.

For the row witnessing `newCell`, the economic state-block is the ZERO block: bal_lo, bal_hi, nonce,
every field, cap_root, reserved are all `0` after. We emit a per-row gate `after[off] = 0` for each
of the 13 economic-data columns (`state_commit` is the digest OUTPUT, pinned by the hash sites, not a
zero-gate). -/

/-- The born-empty zero gate for state-block column `off`: `state_after[off] = 0`. -/
def gZero (off : Nat) : VmConstraint := .gate (eSA off)

/-- The 13 born-empty zero gates (every economic-data column of the state block). -/
def createCellRowGates : List VmConstraint :=
  [ gZero state.BALANCE_LO, gZero state.BALANCE_HI, gZero state.NONCE
  , gZero state.CAP_ROOT, gZero state.RESERVED ]
  ++ (List.range 8).map (fun i => gZero (state.FIELD_BASE + i))

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused, ordered).

`createCell`'s row uses the SAME 4 ordered `H4` sites the running prover lays for EVERY effect row
(the layout is per-row, not per-effect): they bind the after-state's 13 economic columns into the
published `state_commit`. We reuse the keystone's `transferHashSites` verbatim — they are a property
of the ROW layout, not of the transfer effect. -/

/-- The ordered GROUP-4 hash sites (identical to the transfer row's — a layout fact, reused). -/
def createCellHashSites : List VmHashSite := EffectVmEmitTransfer.transferHashSites

/-! ## §3 — the emitted `createCell` row descriptor. -/

/-- The `createCell` EffectVM-row AIR identity. -/
def createCellVmAirName : String := "dregg-effectvm-createcell-v1"

/-- **`createCellVmDescriptor`** — the `createCell` effect's EffectVM-row circuit: the born-empty zero
gates (post-block = the all-zero economic block) with the 4 ordered GROUP-4 hash sites binding that
zero block into the published `state_commit`. NO boundary PI pins are emitted for `newCell` (the new
cell is not the actor; its `state_before` is unconstrained by the turn-identity PIs). -/
def createCellVmDescriptor : EffectVmDescriptor :=
  { name := createCellVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := createCellRowGates
  , hashSites := createCellHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the BORN-EMPTY row intent (the per-cell post-block is the zero economic block). -/

/-- **`BornEmptyRowIntent env`** — the row's post-block is the all-zero economic block: balance limbs,
nonce, every field, cap_root, reserved all `0` after. This is the EffectVM-row projection of
`bornEmptyAt`'s `bal := 0` / `cell := default` resets restricted to the economic columns. -/
def BornEmptyRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = 0
  ∧ env.loc (saCol state.BALANCE_HI) = 0
  ∧ env.loc (saCol state.NONCE) = 0
  ∧ env.loc (saCol state.CAP_ROOT) = 0
  ∧ env.loc (saCol state.RESERVED) = 0
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = 0)

/-! ## §5 — FAITHFULNESS: the emitted per-row gates ⟺ the born-empty intent. -/

/-- **`createCellVm_faithful` — the per-row gates pin EXACTLY the born-empty zero block.** The emitted
descriptor's per-row gates all hold IFF `BornEmptyRowIntent` holds. So the row enforces precisely the
born-empty economic block (and any non-zero post-column makes the descriptor UNSAT). -/
theorem createCellVm_faithful (env : VmRowEnv) :
    (∀ c ∈ createCellRowGates, c.holdsVm env false false) ↔ BornEmptyRowIntent env := by
  unfold createCellRowGates BornEmptyRowIntent
  constructor
  · intro h
    have hLo := h (gZero state.BALANCE_LO) (by simp [gZero])
    have hHi := h (gZero state.BALANCE_HI) (by simp [gZero])
    have hN  := h (gZero state.NONCE) (by simp [gZero])
    have hCap := h (gZero state.CAP_ROOT) (by simp [gZero])
    have hRes := h (gZero state.RESERVED) (by simp [gZero])
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (gZero (state.FIELD_BASE + i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval] at hLo hHi hN hCap hRes
    refine ⟨hLo, hHi, hN, hCap, hRes, ?_⟩
    intro i hi
    have := hFld i hi
    simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval] at this
    exact this
  · rintro ⟨hLo, hHi, hN, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval]
    · exact hLo
    · exact hHi
    · exact hN
    · exact hCap
    · exact hRes
    · exact hFld i hi

/-! ## §6 — ANTI-GHOST: a non-zero born-empty column fails the descriptor. -/

/-- **Anti-ghost (general).** A row whose post-block is NOT the born-empty zero block does NOT satisfy
the per-row gates — UNSAT. -/
theorem createCellVm_rejects_nonzero (env : VmRowEnv) (hwrong : ¬ BornEmptyRowIntent env) :
    ¬ (∀ c ∈ createCellRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((createCellVm_faithful env).mp h)

/-- **Anti-ghost (balance non-zero).** A row whose post-`bal_lo` is non-zero fails the `gZero` gate
(a born cell cannot carry a non-zero balance) — UNSAT. -/
theorem createCellVm_rejects_nonzero_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ 0) :
    ¬ (gZero state.BALANCE_LO).holdsVm env false false := by
  simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval]
  exact hwrong

/-! ## §7 — the commitment binding (the whole zero-block is bound into `state_commit`).

The hash sites are the keystone's, so the keystone's `transferHash_binds` / commitment-injectivity
lemmas apply verbatim: the published `state_commit` is the genuine H4-of-H4 digest of the after-block,
injective in its 13 absorbed columns under Poseidon2 CR. So a prover cannot keep the published
`NEW_COMMIT` while tampering ANY absorbed column of the born-empty block. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (absorbedCols absorbed_determined_by_commit)

/-- The whole-block anti-ghost: two `createCell` rows publishing the SAME `state_commit` under CR have
identical absorbed after-blocks. Inherited from the keystone (same hash sites). -/
theorem createCellVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ createCellHashSites)
    (hs₂ : siteHoldsAll hash e₂ createCellHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — CONNECTOR to universe-A `CreateCellSpec` via `cellProj`.

`cellProj k c` reads cell `c`'s ECONOMIC block out of the real `RecordKernelState` (the `balance`
field; the EffectVM limbs with no universe-A analogue are `0`). `createCellA_full_sound` proves
`CreateCellSpec`, whose `bornEmptyAt` clause forces `k'.bal newCell = 0` and `k'.cell newCell =
default`. So the projected after-block of `newCell` is the ZERO block — EXACTLY `BornEmptyRowIntent`'s
content. This is the ONE overlap the per-row circuit shares with the executor. -/

/-- Read cell `c`'s economic block out of the real record-kernel state into the EffectVM `CellState`
(the same projection shape the transfer connector uses: `balLo` = the `balance` measure; the EffectVM
limbs with no universe-A analogue are `0`). -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`createCell_newcell_is_zero` — the OVERLAP, from the executor.** A committed `createCell`
(`CreateCellSpec st actor newCell st'`) born-empties `newCell`: the projected after-block of `newCell`
is the all-zero economic block (`balLo = 0` and every other limb `0` by construction). So the per-row
circuit's `BornEmptyRowIntent` is EXACTLY the executor's effect on `newCell`'s economic block. -/
theorem createCell_newcell_is_zero (st st' : RecChainedState) (actor newCell : CellId)
    (hspec : CreateCellSpec st actor newCell st') :
    (cellProj st'.kernel newCell).balLo = 0
    ∧ (cellProj st'.kernel newCell).balHi = 0
    ∧ (cellProj st'.kernel newCell).nonce = 0
    ∧ (cellProj st'.kernel newCell).capRoot = 0
    ∧ (cellProj st'.kernel newCell).reserved = 0
    ∧ (∀ i, (cellProj st'.kernel newCell).fields i = 0) := by
  obtain ⟨_, _, hborn, _⟩ := hspec
  obtain ⟨hcell, _⟩ := hborn
  refine ⟨?_, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  -- balLo = balOf (k'.cell newCell) = balOf default = 0 (born-empty resets the cell record)
  show balOf (st'.kernel.cell newCell) = 0
  rw [hcell]
  simp only [if_pos rfl]
  -- balOf default = (default.scalar balanceField).getD 0 = 0
  rfl

/-- **`createCell_row_matches_executor` — the CONNECTOR.** If the EffectVM row's after-block decodes
(`RowEncodes`) to `post`, the descriptor's per-row gates hold, AND the executor commits
`CreateCellSpec st actor newCell st'`, then the row's pinned post-block is the executor's born-empty
`newCell` block: every economic column agrees (all zero), and the row's block equals `cellProj`'s. -/
theorem createCell_row_matches_executor (env : VmRowEnv) (pre post : CellState)
    (p : EffectVmEmitTransferSound.TransferParams)
    (henc : RowEncodes env pre p post)
    (hgates : ∀ c ∈ createCellRowGates, c.holdsVm env false false)
    (st st' : RecChainedState) (actor newCell : CellId)
    (hspec : CreateCellSpec st actor newCell st') :
    post.balLo = (cellProj st'.kernel newCell).balLo
    ∧ post.balHi = (cellProj st'.kernel newCell).balHi
    ∧ post.capRoot = (cellProj st'.kernel newCell).capRoot
    ∧ post.reserved = (cellProj st'.kernel newCell).reserved
    ∧ (∀ i, post.fields i = (cellProj st'.kernel newCell).fields i) := by
  obtain ⟨hLo, hHi, hN, hCap, hRes, hFld⟩ := (createCellVm_faithful env).mp hgates
  obtain ⟨eLo, eHi, eN, eCap, eRes, eFld⟩ := createCell_newcell_is_zero st st' actor newCell hspec
  -- decode the after-block columns to `post` via RowEncodes
  obtain ⟨_, _, _, _, _, _, _, _, _, hsaLo, hsaHi, _, hsaF, hsaCap, hsaRes, _, _, _⟩ := henc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [eLo, ← hsaLo]; exact hLo
  · rw [eHi, ← hsaHi]; exact hHi
  · rw [eCap, ← hsaCap]; exact hCap
  · rw [eRes, ← hsaRes]; exact hRes
  · intro i; rw [eFld i, ← hsaF i]; exact hFld i.val i.isLt

/-! ## §9 — THE BOUNDARY: the LARGE off-row side-effect the per-row circuit cannot enforce.

`CreateCellSpec` enforces FOUR things the EffectVM row does NOT carry:
  * `accounts` growth (`insert newCell`);
  * the born-empty reset of the per-cell SIDE-TABLES (`caps`/`delegate`/`delegations`/`slotCaveats`/
    `lifecycle`/`deathCert`);
  * the creation RECEIPT prepended to the log;
  * the freshness + mint-authority guard (`createCellAdmit`).
We state this exactly: the row's `BornEmptyRowIntent` says NOTHING about any of these. Two states that
agree on `newCell`'s economic block but DISAGREE on `accounts` would both satisfy the row — the row
does not witness `accounts`. This is the genuine off-row gap (the side-state `createCell` drives lives
where the 14-column block cannot reach), reported, not papered. -/

/-- **`createCell_offrow_unenforced` — the loud off-row finding.** Two committed-`CreateCellSpec`
post-states with the SAME born-empty economic block on `newCell` can DIFFER in `accounts` (the row
witnesses neither the account-set growth nor the side-table resets nor the receipt). Concretely: the
row-level `BornEmptyRowIntent` is invariant under changing `accounts`, so the per-row circuit cannot
distinguish a state that grew `accounts` from one that did not. The account-growth / side-table /
receipt soundness lives ONLY in `createCellA_full_sound`, NOT in this row descriptor. -/
theorem createCell_offrow_unenforced :
    -- `BornEmptyRowIntent` mentions only `state_after` economic columns; it constrains no `accounts`,
    -- `lifecycle`, `deathCert`, `caps`, or log column — those have NO named offset in the 14-col block.
    (∀ env₁ env₂ : VmRowEnv,
      (∀ off : Nat, env₁.loc (saCol off) = env₂.loc (saCol off)) →
      (BornEmptyRowIntent env₁ ↔ BornEmptyRowIntent env₂)) := by
  intro env₁ env₂ hagree
  unfold BornEmptyRowIntent
  rw [hagree state.BALANCE_LO, hagree state.BALANCE_HI, hagree state.NONCE,
      hagree state.CAP_ROOT, hagree state.RESERVED]
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by rw [← hagree (state.FIELD_BASE + i)]; exact f i hi⟩
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by rw [hagree (state.FIELD_BASE + i)]; exact f i hi⟩

/-! ## §10 — NON-VACUITY: a concrete born-empty row that satisfies, and one that does not. -/

/-- A concrete born-empty row: every economic after-column is `0`. -/
def zeroRow : VmRowEnv where
  loc := fun v => if v = SEL_CREATECELL then 1 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `zeroRow` realizes the born-empty intent: every economic
after-column is `0`. So the faithfulness biconditional's intent side is inhabited. -/
theorem zeroRow_realizes_intent : BornEmptyRowIntent zeroRow := by
  unfold BornEmptyRowIntent zeroRow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (if saCol state.BALANCE_LO = SEL_CREATECELL then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.BALANCE_HI = SEL_CREATECELL then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.NONCE = SEL_CREATECELL then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.CAP_ROOT = SEL_CREATECELL then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.RESERVED = SEL_CREATECELL then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · intro i hi
    show (if saCol (state.FIELD_BASE + i) = SEL_CREATECELL then (1:ℤ) else 0) = 0
    rw [if_neg]
    simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.FIELD_BASE, SEL_CREATECELL]
    omega

/-- A FORGED born-empty row: `zeroRow` with post-`bal_lo` tampered to `5` (a born cell cannot carry
balance). -/
def forgedRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 5 else zeroRow.loc v
  nxt := zeroRow.nxt
  pub := zeroRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `forgedRow`'s post-`bal_lo` is non-zero, so
the `gZero` gate REJECTS it — a concrete UNSAT (a born cell with a forged balance). -/
theorem forgedRow_rejected : ¬ (gZero state.BALANCE_LO).holdsVm forgedRow false false := by
  apply createCellVm_rejects_nonzero_balance
  show (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (5:ℤ)
    else zeroRow.loc (saCol state.BALANCE_LO)) ≠ 0
  rw [if_pos rfl]; norm_num

/-! ## §11 — axiom-hygiene tripwires. -/

#guard createCellVmDescriptor.constraints.length == 13
#guard createCellVmDescriptor.hashSites.length == 4
#guard createCellVmDescriptor.traceWidth == 188

#assert_axioms createCellVm_faithful
#assert_axioms createCellVm_rejects_nonzero
#assert_axioms createCellVm_rejects_nonzero_balance
#assert_axioms createCellVm_commit_binds_block
#assert_axioms createCell_newcell_is_zero
#assert_axioms createCell_row_matches_executor
#assert_axioms createCell_offrow_unenforced
#assert_axioms zeroRow_realizes_intent
#assert_axioms forgedRow_rejected

/-! ## §RT — the RUNTIME-RECONCILED cutover descriptor (v2): the ACTING cell's passthrough + nonce-TICK
row (GRADUATED into the descriptor cutover).

THE RUNTIME GROUND TRUTH. The running prover runs `createCell` (selector 31) as a member of the
**Stage-3 passthrough batch** (`effect_vm/trace.rs`: the arm parks `create_hash[0]` into `params[0]`
and does `new_state.nonce += 1`). Every economic state-block column of the ACTING cell (balance limbs,
`cap_root`, all 8 fields, reserved) is FROZEN; the global nonce gate TICKS the nonce by 1. The CHILD
cell's born-empty block — the §1–§10 descriptor above (`createCellVmDescriptor`, the BORN-EMPTY-CHILD
face) — is OFF-ROW content for THIS row: the child's zero block is the executor's guarantee
(`createCellA_full_sound`, §8 connector), bound through `effects_hash`, NOT a column move on the
actor's row. The pre-v2 cutover registered the CHILD-face descriptor against selector 31, which the
runtime hand-AIR row (the ACTOR's row) cannot satisfy — the documented lifecycle/birth divergence.
This v2 emits the runtime actor row directly: the gate set is the validated frozen-frame + nonce-tick
template (`revokeRowGates`, proven faithful in `EffectVmEmitRevokeDelegation`), with the createCell
selector binding (`selectorGates 31`). Both faces stay verified; the WIRE descriptor is the actor row.
-/

open Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
  (revokeRowGates RevokeRowIntent revokeVm_faithful intent_to_cellSpec RevokeCellSpec
   RowEncodesRevoke gBalLoFreeze goodRevokeRow goodRevokeRow_realizes_intent
   badRevokeRow badRevokeRow_rejected)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins transferHashSites boundaryLast_pins)

/-- The `createCell` selector column index (runtime `sel::CREATE_CELL = 31`). -/
def SEL_CREATE_CELL_RT : Nat := 31

/-- The v2 (runtime-reconciled) `createCell` AIR identity. -/
def createCellActorVmAirName : String := "dregg-effectvm-createcell-v2"

/-- **`createCellActorVmDescriptor`** — the `createCell` ACTOR-row circuit, RECONCILED onto the runtime
hand-AIR: the shared frozen-frame + nonce-TICK gates ++ transition continuity ++ the 7 boundary PI
pins ++ the selector-binding gate, with the 4 ordered GROUP-4 hash sites and the 2 balance-limb range
checks. Body structurally identical to the validated `revokeDelegation-v2` template; only the name and
the selector gate differ. The born-empty CHILD face stays `createCellVmDescriptor` (§3). -/
def createCellActorVmDescriptor : EffectVmDescriptor :=
  { name := createCellActorVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := revokeRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates SEL_CREATE_CELL_RT
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- **Faithfulness (inherited from the shared template).** The actor row's per-row gates hold IFF the
frozen-frame + nonce-tick intent holds (`RevokeRowIntent` — the SHARED passthrough+tick intent; the
gate list is literally `revokeRowGates`). Non-vacuity rides with the template: `goodRevokeRow` realizes
the intent, `badRevokeRow` (forged balance) is rejected. -/
theorem createCellActor_faithful (env : VmRowEnv) :
    (∀ c ∈ revokeRowGates, c.holdsVm env false false) ↔ RevokeRowIntent env :=
  revokeVm_faithful env

/-- **`createCellActor_full_sound`** — the v2 descriptor's row soundness: a satisfying row, decoded,
pins the full per-cell frozen-frame + nonce-tick post-state AND publishes its commit as `NEW_COMMIT`. -/
theorem createCellActor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesRevoke env pre post)
    (hgatesat : satisfiedVm hash createCellActorVmDescriptor env true false)
    (hsat : satisfiedVm hash createCellActorVmDescriptor env true true) :
    RevokeCellSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates' : ∀ c ∈ revokeRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ createCellActorVmDescriptor.constraints := by
      unfold createCellActorVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    unfold Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation.revokeRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (revokeVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ createCellActorVmDescriptor.constraints := by
      unfold createCellActorVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

#guard createCellActorVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard createCellActorVmDescriptor.hashSites.length == 4
#guard createCellActorVmDescriptor.traceWidth == 188

#assert_axioms createCellActor_faithful
#assert_axioms createCellActor_full_sound

end Dregg2.Circuit.Emit.EffectVmEmitCreateCell
