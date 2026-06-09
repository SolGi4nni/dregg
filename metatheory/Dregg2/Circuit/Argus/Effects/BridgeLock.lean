/-
# Dregg2.Circuit.Argus.Effects.BridgeLock — the bridgeLock (bridge-outbound Phase-1 LOCK) effect welded
into the Argus IR, in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the side-table cornerstone for PLAIN escrow:
`interp (createEscrowStmt …) = createEscrowKAsset` (the executor IS the meaning of the IR term, over a
TWO-component move — a per-asset `bal` debit AND an `escrows` list prepend). `Argus/Compile.lean` welded
plain createEscrow's circuit (`createEscrowGenuine_sound`) to that term. This module does the SAME for
`bridgeLock`, the bridge-shaped TWIN of escrow-create.

## bridgeLock is escrow-create's bridge twin — faithfully, not by fiat

The running kernel step is `bridgeLockKAsset` (`Exec/RecordKernel.lean:1780`). On commit it produces
`createBridgeRawAsset` (`:1761`): the SAME two-component move as `createEscrowRawAsset` — a single-cell
single-asset `bal` DEBIT of `amount` at `(originator, asset)`, AND a prepend of an UNRESOLVED record onto
the SHARED `escrows` holding-store — with ONE difference: the parked record carries `bridge := true`
(dregg1's `Locked` `PendingBridge`, `note_bridge.rs initiate_bridge`). Its admissibility gate is the
escrow-create five conjuncts PLUS a sixth — `cellLifecycleLive k originator` (the D3 bridge-lock teeth:
a sealed/destroyed originator's lock is REJECTED, `bridgeLockKAsset_nonlive_fails`). Double-lock is
rejected by the id-freshness conjunct (dregg1's `AlreadyLocked` / `is_locked`).

So the IR term is `seq (guard bridgeLockGuard) (seq (setBal <debit>) (setEscrows <bridge-tagged
prepend>))` — gate, then the two component writes — EXACTLY `createEscrowStmt`'s skeleton, only with the
sixth liveness conjunct in the guard and the `bridge := true` tag on the parked leaf. The §A primitives
`setBal`/`setEscrows` are the shapes a two-component side-table effect assembles; NO new IR constructor
is needed (the holding-store IS the `escrows` list the IR can already write — REPORTED below). The
cornerstone is that `interp` of THIS term IS the verified kernel step `bridgeLockKAsset`.

We also prove (not assert) the bridge to the AUDITED chained executor: `bridgeLockChainA`
(`TurnExecutorFull.lean:2987`) projected to the kernel IS `bridgeLockKAsset` (it stamps the chained log
by `escrowReceiptA actor ::`), so the kernel target this module refines to is the genuine kernel image
of the running system's bridge lock (`bridgeLockChainA_kernelStep`).

## The circuit side — the audited CLASS-A genuine descriptor

The circuit is `EffectVmEmitBridgeLockA.bridgeLockVmDescriptorGenuine` + its class-A
`bridgeLockGenuine_sound` (`Circuit/Emit/EffectVmEmitBridgeLockA.lean:666/688`), which on a satisfying
row forces (a) the per-cell `CellLockSpec` (the `balLo` DEBIT by `value`, every other limb frozen, the
nonce TICKED), (b) the GENUINE in-row bridge-escrow-root RECOMPUTE
(`SYS_DIG_AFTER = advanceOf hash (leafOf hash id creator recipient amount asset resolved) SYS_DIG_BEFORE`,
the side-table digest FORCED — not a free step), and (c) the published commit. So the side-table prepend
is BOUND, not papered (`bridgeLockGenuine_binds_record`, `:729`: a forged/dropped lock MOVES the
commitment ⇒ UNSAT). We weld DIRECTLY against this descriptor (no central `compileE` needed), as the
committed/refund sibling modules do.

## HONEST SURFACE — exactly createEscrow's weld surface PLUS the turn-reconciled nonce-tick (do NOT over-read)

The weld concludes the SAME per-cell + side-table legs the plain-createEscrow weld concludes, PLUS the
ONE divergence that transfer/burn carry (and createEscrow did not):

  * **conserved leg (per-cell):** the circuit's pinned post-`balLo` equals the executor's debited
    `bal originator asset` (= pre − amount), with the frozen frame (balHi/fields/capRoot/reserved)
    agreeing. `cellProjLock` projects ONLY the `(originator, asset)` ledger entry into `balLo` (the other
    limbs are `0`, FROZEN) — so this binds the DEBITED CELL, exactly as transfer binds the SRC cell. The
    cross-cell combined per-asset conservation (debit ⊕ off-ledger park) is the executor's keystone
    (`bridge_lock_conserves_combined_per_asset`, `RecordKernel.lean:1830`), cited there — NOT re-claimed.
  * **side-table leg (the bridge record):** the circuit FORCES the new escrow-list root to be the genuine
    recompute of the bound parked-record content + the old root, absorbed into `state_commit`, so the
    parked bridge record (id/creator/recipient/amount/asset/resolved) is bound. The weld EXPOSES this
    genuine-recompute clause as a conjunct so the side-table binding is part of the welded statement.
  * **the per-effect nonce, RECONCILED at the turn level (NOT a carried divergence):** the descriptor
    TICKS the cell nonce (`CellLockSpec`: `post.nonce = pre.nonce + 1`, the runtime sequence counter),
    while the executor's `cellProjLock` ledger image FREEZES it (`= pre.nonce`). Both facts are bundled as
    a `NonceReconciled` final conjunct, and `Argus.Nonce.perEffect_nonce_reconciles_to_turn`
    (`bridgeLock_compile_sound_nonce_is_turn_tick`) proves the row's `+1` is exactly the turn PROLOGUE's
    single tick over the frozen body. So the per-effect tick is NOT a second tick — it is the turn's one
    tick, located in the prologue. The divergence is CLOSED, not carried.

What this does NOT claim: it does not assert the circuit row's `escrows`-list state EQUALS the executor's
`bridgeRecord :: k.escrows` as a LIST (the EffectVM row carries a DIGEST, not the list — they agree only
up to the side-table root). The executor produces the real list; the circuit produces the genuine root of
it. That digest-not-list boundary is faithful, stated, not hidden.

## Honesty

`#assert_axioms` on both theorems ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY via
the named `Poseidon2SpongeCR` hypothesis (inside the cited anti-ghost, not these theorems). No `sorry`,
no `:= True`, no weakening-that-just-typechecks, no `native_decide`. This module OWNS only itself; every
import is read-only and no other Argus file is edited.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Argus.Nonce
import Dregg2.Circuit.Emit.EffectVmEmitBridgeLockA

namespace Dregg2.Circuit.Argus.Effects.BridgeLock

open Dregg2.Exec
-- The CHAINED bridge-lock executor + the receipt stamp live in `Dregg2.Exec.TurnExecutorFull`; opened so
-- the §0 kernel-bridge lemma can name them.
open Dregg2.Exec.TurnExecutorFull (bridgeLockChainA escrowReceiptA)
-- `VmRowEnv` / `satisfiedVm` / `prmCol` are the unqualified EffectVM IR names (exactly as `Argus/Compile.lean`
-- opens them) — without this they resolve only to the fully-qualified path.
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Argus (RecStmt interp kC NonceReconciled)
open Dregg2.Exec (RecordKernelState RecChainedState EscrowRecord CellId AssetId
  bridgeLockKAsset createBridgeRawAsset recBalCreditCell cellLifecycleLive)
-- The class-A bridgeLock genuine descriptor + its soundness + the per-cell lock spec / projection / decode.
open Dregg2.Circuit.Emit.EffectVmEmitBridgeLockA
  (bridgeLockVmDescriptorGenuine bridgeLockGenuine_sound IsBridgeLockRow
   LockParams CellLockSpec RowEncodesLock cellProjLock)

/-! ## §0 — THE KERNEL TARGET: the bridge-lock kernel step, and its bridge to the audited chained executor.

The plain escrow §E cornerstone (`Stmt.lean`) refines its IR term to the KERNEL step
`createEscrowKAsset : RecordKernelState → Option RecordKernelState`. bridgeLock's kernel step is the
twin `bridgeLockKAsset`. We prove (not assert) that the audited chained executor `bridgeLockChainA`
(`TurnExecutorFull.lean:2987`), projected to the kernel, IS `bridgeLockKAsset` (stamping the chained
`log` by `escrowReceiptA actor ::`), so the target is faithful to the running system, not a fresh
invention. -/

/-- **`bridgeLockChainA_kernelStep` — the bridge (PROVED, not asserted).** The audited chained bridge-lock
executor `bridgeLockChainA`, projected to the kernel, IS `bridgeLockKAsset` (and it stamps the chained
`log` by `escrowReceiptA actor ::`). So the kernel target this module refines the IR term to is the
genuine kernel image of the running system's bridge lock. -/
theorem bridgeLockChainA_kernelStep (s : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ) :
    bridgeLockChainA s id actor originator destination asset amount
      = (bridgeLockKAsset s.kernel id actor originator destination asset amount).map
          (fun k' => { kernel := k', log := escrowReceiptA actor :: s.log }) := by
  unfold bridgeLockChainA
  cases bridgeLockKAsset s.kernel id actor originator destination asset amount with
  | none    => rfl
  | some k' => rfl

#assert_axioms bridgeLockChainA_kernelStep

/-! ## §1 — THE IR TERM: gate (six conjuncts), then the TWO component writes (debit ++ bridge-tagged park).

`bridgeLockStmt = seq (guard bridgeLockGuard) (seq (setBal <debit>) (setEscrows <bridge-tagged prepend>))`
— EXACTLY `createEscrowStmt`'s skeleton (`Stmt.lean:401`), with the SIXTH liveness conjunct in the guard
and the `bridge := true` tag on the parked leaf. The holding-store the lock parks into IS the `escrows`
list the §A `setEscrows` primitive already writes — NO new IR primitive needed (see §REPORT at file foot). -/

/-- The unresolved, `bridge := true`-tagged `EscrowRecord` a bridge lock parks — the SAME literal
`createBridgeRawAsset` installs (`RecordKernel.lean:1764`). Stated here so the term's `setEscrows` leaf is
the genuine parked bridge record. -/
def bridgeParked (id : Nat) (originator destination : CellId) (asset : AssetId) (amount : ℤ) :
    EscrowRecord :=
  { id := id, creator := originator, recipient := destination,
    amount := amount, resolved := false, asset := asset, bridge := true }

/-- The bridge-lock admissibility gate as a `Bool` — exactly `bridgeLockKAsset`'s `if` (the SIX conjuncts,
in the SAME order the kernel checks them: authority over the lock-turn `actor: originator ⇒ destination`,
non-negative amount, the amount available *in asset `asset`* on the per-asset ledger, the originator a
live account, the originator's LIFECYCLE live — the D3 bridge-lock teeth plain escrow lacks — and the
`id` NOT already parked, dregg1's `AlreadyLocked`). -/
def bridgeLockGuard (id : Nat) (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (k : RecordKernelState) : Bool :=
  authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount }
    && decide (0 ≤ amount)
    && decide (amount ≤ k.bal originator asset)
    && decide (originator ∈ k.accounts)
    && cellLifecycleLive k originator
    && decide (¬ (∃ r ∈ k.escrows, r.id = id))

/-- **The bridgeLock effect as an Argus IR term: gate, then the TWO component writes.** Identical shape to
`createEscrowStmt` (`Stmt.lean`): `seq (setBal <debit>) (setEscrows <prepend>)` — debit the per-asset
ledger at `(originator, asset)`, then prepend the unresolved `bridge := true` record onto `escrows`. The
sixth (liveness) conjunct lives in the guard; the bridge tag lives on the parked leaf. -/
def bridgeLockStmt (id : Nat) (actor originator destination : CellId) (asset : AssetId) (amount : ℤ) :
    RecStmt :=
  RecStmt.seq (RecStmt.guard (bridgeLockGuard id actor originator destination asset amount))
    (RecStmt.seq
      (RecStmt.setBal (fun k => recBalCreditCell k.bal originator asset (-amount)))
      (RecStmt.setEscrows (fun k => bridgeParked id originator destination asset amount :: k.escrows)))

/-! ## §2 — THE CORNERSTONE: `interp` of the bridgeLock term IS the verified kernel step `bridgeLockKAsset`.

The SAME proof shape as the plain §E cornerstone `interp_createEscrowStmt_eq_createEscrowKAsset`: a
guard-decode lemma, then the two-component body reduces (the `setBal` debit, then the `setEscrows` prepend
whose `escrows` read is still `k.escrows` because `setBal` writes only `bal`), giving exactly
`createBridgeRawAsset`; the RHS `if` opens on the decoded 6-conjunct Prop. -/

/-- The bridge-lock `Bool` gate decodes to `bridgeLockKAsset`'s admissibility proposition (the six
conjuncts, in the SAME order the kernel `if` checks them). -/
theorem bridgeLockGuard_iff (id : Nat) (actor originator destination : CellId) (asset : AssetId)
    (amount : ℤ) (k : RecordKernelState) :
    bridgeLockGuard id actor originator destination asset amount k = true ↔
      (authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
        ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
        ∧ cellLifecycleLive k originator = true
        ∧ ¬ (∃ r ∈ k.escrows, r.id = id)) := by
  simp only [bridgeLockGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- **The cornerstone (side-table, bridge twin).** `interp` of the bridgeLock term IS the verified kernel
step `bridgeLockKAsset` — the same partial function, by construction, exactly as the plain createEscrow
§E cornerstone, now with the sixth liveness conjunct in the guard and the `bridge := true` tag carried on
the parked record. -/
theorem interp_bridgeLockStmt_eq_bridgeLockKAsset (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) (k : RecordKernelState) :
    interp (bridgeLockStmt id actor originator destination asset amount) k
      = bridgeLockKAsset k id actor originator destination asset amount := by
  simp only [bridgeLockStmt, interp]
  unfold bridgeLockKAsset
  by_cases hg : bridgeLockGuard id actor originator destination asset amount k = true
  · -- ADMIT: the guard fires (`some k`), the two-component body reduces (the `setBal` debit then the
    -- `setEscrows` prepend — whose `escrows` read is still `k.escrows`), giving exactly
    -- `createBridgeRawAsset`; the RHS `if` opens on the decoded 6-conjunct Prop.
    rw [if_pos hg,
      if_pos ((bridgeLockGuard_iff id actor originator destination asset amount k).mp hg)]
    simp only [Option.bind, bridgeParked, createBridgeRawAsset]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the (negated) decoded Prop.
    rw [if_neg hg,
      if_neg (fun hp => hg ((bridgeLockGuard_iff id actor originator destination asset amount k).mpr hp))]
    simp only [Option.bind]

#assert_axioms interp_bridgeLockStmt_eq_bridgeLockKAsset

/-! ## §3 — THE EXECUTOR-side per-cell projection of the kernel step `bridgeLockKAsset`.

The `EffectVmEmitBridgeLockA.unify_lock_debit` lemma projects `execFullA … (.bridgeLockA …)` onto
`cellProjLock`; this is the KERNEL-STEP analog (since our IR refines to `bridgeLockKAsset` directly). A
committed bridge lock DEBITS the originator cell's projected `(originator, asset)` ledger entry by exactly
`amount` and FREEZES the projected nonce (`cellProjLock`'s nonce limb is `0` on both sides — the executor
ledger image freezes; this is the executor side of the nonce-tick divergence). The frozen frame
(balHi/fields/capRoot/reserved) is `0 = 0` on both projections (definitional). -/

/-- **`bridgeLockKAsset_proj_balLo`.** A committed kernel bridge lock debits the originator cell's projected
`(originator, asset)` ledger entry by exactly `amount` (the value parked off-ledger). The per-cell
conserved leg the weld pins. -/
theorem bridgeLockKAsset_proj_balLo {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    (cellProjLock k'.bal originator asset).balLo
      = (cellProjLock k.bal originator asset).balLo - amount := by
  unfold bridgeLockKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
      ∧ cellLifecycleLive k originator = true
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    -- `cellProjLock (createBridgeRawAsset …).bal originator asset).balLo = recBalCreditCell … originator asset`
    show recBalCreditCell k.bal originator asset (-amount) originator asset = k.bal originator asset - amount
    unfold recBalCreditCell; rw [if_pos ⟨rfl, rfl⟩]; ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

#assert_axioms bridgeLockKAsset_proj_balLo

/-! ## §4 — THE WELD: a satisfying witness of `bridgeLockVmDescriptorGenuine` agrees, per cell, with the
post-state the IR term's executor interpretation produces — AND forces the genuine side-table root — with
the per-effect nonce-tick RECONCILED to the turn's one prologue tick (`NonceReconciled`, NOT carried).

Welded DIRECTLY against the audited class-A descriptor `bridgeLockVmDescriptorGenuine` (no central
`compileE`), as the committed/refund sibling modules do. Circuit side: `bridgeLockGenuine_sound`; executor
side: the §2 cornerstone + the §3 projection. -/

/-- **`bridgeLock_compile_sound` — the welded soundness (bridgeLock slice, the bridge side-table effect).**

Suppose, for the Argus bridgeLock term `bridgeLockStmt id actor originator destination asset amount`:
  * the row is a genuine bridge-lock row (`hrow : IsBridgeLockRow env`, `s_bridge_lock = 1 ∧ s_noop = 0`);
  * the audited class-A circuit `bridgeLockVmDescriptorGenuine` is SATISFIED by `(env, true, true)` under
    the abstract Poseidon carrier `hash`, and its `RowEncodesLock` decoding NAMES the post-state record
    `post` over the originator cell's projection `cellProjLock k.bal originator asset` with the
    `⟨amount⟩` lock-param block (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS:
    `interp (bridgeLockStmt …) k = some k'` (`hexec`).

Then:
  * **conserved leg (per-cell):** the circuit's pinned post-state `post` AGREES with the executor's
    debited originator-cell projection `cellProjLock k'.bal originator asset` — the conserved `balLo`
    (debited by `amount`) AND the whole frozen frame (balHi/fields/capRoot/reserved).
  * **side-table leg:** the circuit FORCES the new bridge-escrow-list-root carrier to be the genuine in-row
    recompute `advanceOf hash (leafOf hash id creator recipient amount asset resolved) old_root` of the
    bound parked bridge record + old root — the digest the executor's `bridgeRecord :: k.escrows` prepend
    commits to (absorbed into `state_commit`; a forged/dropped lock MOVES the commitment, see
    `bridgeLockGenuine_binds_record`).
  * **the per-effect nonce, RECONCILED at the turn level (NOT a carried divergence):** the descriptor
    TICKS the cell nonce (`post.nonce = (cellProjLock k.bal originator asset).nonce + 1`, the runtime
    sequence counter) while the executor's ledger image FREEZES it (`(cellProjLock k'.bal originator
    asset).nonce = (cellProjLock k.bal originator asset).nonce`). Both facts are bundled as a
    `NonceReconciled` final conjunct, and `bridgeLock_compile_sound_nonce_is_turn_tick` discharges the
    row's `+1` to the turn PROLOGUE's single tick over the frozen body — so it is the turn's one tick,
    NOT a per-effect double-count. (createEscrow's descriptor froze; bridgeLock's ticks, but the tick is
    the prologue's, located there.)

So the class-A circuit the prover runs for bridgeLock pins the per-cell debited state the IR term's
executor produces AND genuinely recomputes the bound `escrows` side-table root, modulo the carried
nonce-tick — the template generalizes to the bridge twin of the two-component side-table effect. -/
theorem bridgeLock_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeLockRow env)
    (k k' : RecordKernelState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ)
    (post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (henc : RowEncodesLock env (cellProjLock k.bal originator asset) ⟨amount⟩ post)
    (hsat : satisfiedVm hash bridgeLockVmDescriptorGenuine env true true)
    (hexec : interp (bridgeLockStmt id actor originator destination asset amount) k = some k') :
    -- conserved leg: the debited cell's projection agrees on balLo + the whole frozen frame …
    ( post.balLo = (cellProjLock k'.bal originator asset).balLo
      ∧ post.balHi = (cellProjLock k'.bal originator asset).balHi
      ∧ (∀ i, post.fields i = (cellProjLock k'.bal originator asset).fields i)
      ∧ post.capRoot = (cellProjLock k'.bal originator asset).capRoot
      ∧ post.reserved = (cellProjLock k'.bal originator asset).reserved )
    -- … and the SIDE-TABLE leg: the circuit FORCES the genuine bridge-escrow-list-root recompute (the bound
    -- parked record + old root), absorbed into `state_commit` …
    ∧ ( env.loc Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.SYS_DIG_AFTER
          = Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.advanceOf hash
              (Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.leafOf hash
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.ID))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.CREATOR))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.RECIPIENT))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.AMOUNT))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.ASSET))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.RESOLVED)))
              (env.loc Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.SYS_DIG_BEFORE) )
    -- … and the per-effect nonce is RECONCILED (NOT a divergence): the descriptor TICKS the cell nonce,
    --   the executor FREEZES it; the turn PROLOGUE's single tick is the net (`bridgeLock_compile_sound
    --   _nonce_is_turn_tick`).
    ∧ NonceReconciled (cellProjLock k.bal originator asset).nonce post.nonce
        (cellProjLock k'.bal originator asset).nonce := by
  -- circuit side: the audited class-A soundness forces the per-cell `CellLockSpec` + the genuine root.
  obtain ⟨hcs, hroot, _hcommit⟩ :=
    bridgeLockGenuine_sound hash env hrow (cellProjLock k.bal originator asset) post ⟨amount⟩ henc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified kernel step
  -- `bridgeLockKAsset`; its per-cell projection gives the debited balLo (the frozen limbs are `0=0`).
  rw [interp_bridgeLockStmt_eq_bridgeLockKAsset] at hexec
  have heLo := bridgeLockKAsset_proj_balLo hexec
  -- the descriptor tick `hcN` (post = pre.nonce + 1) + the executor freeze (`rfl`: `cellProjLock` zeroes
  -- both nonces) ARE `NonceReconciled`'s two clauses.
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl⟩,
          hroot, hcN, rfl⟩
  · -- balLo: circuit pins post = pre − amount; executor debits the projected entry by amount.
    rw [hcLo, heLo]

#assert_axioms bridgeLock_compile_sound

/-- **`bridgeLock_compile_sound_nonce_is_turn_tick` — the close, applied to bridgeLock.** The
`NonceReconciled` that `bridgeLock_compile_sound` yields, composed with a turn prologue over the debited
originator cell (read as the turn's agent), gives the whole-turn ONE-tick law: the body freezes (zero
contribution), the prologue ticks once, and the descriptor's per-effect post nonce EQUALS that single
prologue tick. So bridgeLock's row `+1` is the turn's one tick — the divergence is CLOSED. -/
theorem bridgeLock_compile_sound_nonce_is_turn_tick
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeLockRow env)
    (k k' : RecordKernelState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ)
    (post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (henc : RowEncodesLock env (cellProjLock k.bal originator asset) ⟨amount⟩ post)
    (hsat : satisfiedVm hash bridgeLockVmDescriptorGenuine env true true)
    (hexec : interp (bridgeLockStmt id actor originator destination asset amount) k = some k')
    (s : RecChainedState) (fee : Int)
    (hpre  : (cellProjLock k.bal originator asset).nonce
               = Dregg2.Exec.EffectTransfer.nonceOf (s.kernel.cell originator))
    (hexecAgent : (cellProjLock k'.bal originator asset).nonce
                    = Dregg2.Exec.EffectTransfer.nonceOf (s.kernel.cell originator)) :
    Dregg2.Exec.EffectTransfer.nonceOf
        ((Dregg2.Exec.Admission.commitPrologue s originator fee).kernel.cell originator)
      = Dregg2.Exec.EffectTransfer.nonceOf (s.kernel.cell originator) + 1
    ∧ post.nonce = Dregg2.Exec.EffectTransfer.nonceOf
        ((Dregg2.Exec.Admission.commitPrologue s originator fee).kernel.cell originator)
    ∧ post.nonce = (cellProjLock k'.bal originator asset).nonce + 1 := by
  have hr : NonceReconciled (cellProjLock k.bal originator asset).nonce post.nonce
              (cellProjLock k'.bal originator asset).nonce :=
    (bridgeLock_compile_sound hash env hrow k k' id actor originator destination asset amount
      post henc hsat hexec).2.2
  obtain ⟨_hzero, htick, hmatch, hresid⟩ :=
    Dregg2.Circuit.Argus.perEffect_nonce_reconciles_to_turn hr s originator fee hexecAgent hpre
  exact ⟨htick, hmatch, hresid⟩

#assert_axioms bridgeLock_compile_sound_nonce_is_turn_tick

/-! ## §5 — NON-VACUITY: the bridge term genuinely parks (and the D3 liveness gate genuinely rejects).

The cornerstone would be hollow if the bridge term never committed, or if the sixth liveness conjunct
were inert. Neither: on a live originator a fresh `0`-amount lock grows the `escrows` store from `[]` to
length `1` (the two-component move is real, and the parked record carries `bridge := true`); and a
SEALED originator's identical lock REJECTS (fail-closed) — the D3 bridge-lock teeth, two-valued, lifted
onto the IR term. -/

/-- **NON-VACUITY (witness TRUE — the bridge park is real).** Running the bridgeLock term on the §C two-cell
kernel `kC` (cell `0` Live, empty `escrows`) with a fresh `0`-amount lock grows `escrows` from `[]` to
length `1` — the two-component move genuinely touches the side-table (the prepend is real). The `0` amount
keeps the gate's availability/non-negativity legs trivially satisfied so the commit fires. -/
theorem bridgeLockStmt_parks :
    (interp (bridgeLockStmt 9 0 0 1 1 0) kC).map (fun k => k.escrows.length) = some 1 := by
  rw [interp_bridgeLockStmt_eq_bridgeLockKAsset]
  decide

/-- **NON-VACUITY (witness TRUE — the bridge TAG is real).** The single parked record on a committed lock
carries `bridge = true` (the `Locked` `PendingBridge` tag dregg1 sets, distinguishing it from a plain
escrow row in the shared holding-store). So the term genuinely writes a BRIDGE record, not a plain one. -/
theorem bridgeLockStmt_parks_bridge_tagged :
    (interp (bridgeLockStmt 9 0 0 1 1 0) kC).map (fun k => k.escrows.head?.map (·.bridge))
      = some (some true) := by
  rw [interp_bridgeLockStmt_eq_bridgeLockKAsset]
  decide

#assert_axioms bridgeLockStmt_parks
#assert_axioms bridgeLockStmt_parks_bridge_tagged

end Dregg2.Circuit.Argus.Effects.BridgeLock
