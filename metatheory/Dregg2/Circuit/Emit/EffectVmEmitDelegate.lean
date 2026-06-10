/-
# Dregg2.Circuit.Emit.EffectVmEmitDelegate — the AUTHORITY-UNATTENUATED DELEGATE effect `delegate`,
  CONNECTED to the runnable EffectVM `cap_root` column descriptor + the validated universe-A
  `delegate_full_sound`.

## ONE circuit — `delegate` is a `cap_root` COLUMN MOVE (the same runnable row as `attenuateA`)

`delegate` (`Inst/delegate.lean`) is a `caps`-touching v2 instance: it touches the `caps` table as a
WHOLE-FUNCTION injective digest (`funcComponent (·.caps) D hD`), predicted post value
`recDelegateCaps s.kernel.caps del rec t` (the Granovetter unattenuated grant of the delegator's held
`t`-conferring cap to the recipient), freezes the other 16 kernel fields, and is GATED by the
connectivity premise `delegateGuard` (the delegator already holds a `t`-conferring cap). Its validation
`delegate_full_sound ⇒ DelegateSpec` is DONE in universe A.

On the running EffectVM row layout `delegate` is EXACTLY the cap-graph row `attenuateA` emits: the post
`cap_root` is the digest of the post cap-table, every other state column frozen, the moved post-state
(cap_root included) bound into the published `state_commit` under Poseidon2 CR. So this module REUSES
the validated `EffectVmEmitAttenuateA` cap-root-move descriptor (`attenuateVmDescriptor`, its
`AttenRowIntent`/`CapCellSpec` faithfulness, anti-ghost, and GROUP-4 commitment tooth) — it is the SAME
ONE runnable circuit (a `cap_root` move + frame freeze), NOT a parallel spec — and adds the `delegate`
CONNECTOR: the projected post-`cap_root` is universe-A's `recDelegateCaps` digest.

## The CONNECTOR — `capRootProj` to `delegate_full_sound`

`capRootProj D k = D k.caps` reads the SAME whole-function digest `D : Caps → ℤ` that universe-A's
`Delegate.capsComponent D hD` uses. `unify_delegate` shows: when `DelegateSpec` holds (so
`k'.caps = recDelegateCaps k.caps del rec t`), the projected post-`cap_root` is EXACTLY
`D (recDelegateCaps k.caps del rec t)` — the column move the descriptor pins. So the runnable `cap_root`
transition IS universe-A's validated `caps`-digest transition; not a fourth spec.

## BOUNDARY (precise)

  * **IR GAP — needs IR extension: cap-root hash-site** (inherited from `EffectVmEmitAttenuateA`). The
    `cap_root` column carries the SCALAR digest `D caps` of the cap-table FUNCTION; the EffectVM IR's
    `VmHashSite` cannot re-derive `cap_root` IN-circuit from the cap-table rows. So the descriptor pins
    the `cap_root` COLUMN transition (witness supplies the digest) and binds it into `state_commit`, but
    the cap-table-is-Merkled binding lives in the `Function.Injective D` portal (carried,
    realizable), the SAME bar `delegate_full_sound` uses. We connect through `capRootProj`.

  * **The Granovetter GUARD (`delegateGuard`) is NOT a `cap_root` ROW gate.** Unlike `attenuateA` (whose
    guard is the trivial `True`), `delegate` is gated by the connectivity premise. That guard is enforced
    by universe-A's `delegate_full_sound` (the `propBit (delegateGuard)` column of `delegateE`), NOT by
    the cap-root-move row gates this module reuses. So `unify_delegate_via_full_sound` carries the guard
    through `delegate_full_sound`'s hypothesis; the runnable cap-root row pins only the MOVE, with the
    guard a separate (already-validated) gate. Flagged, not papered.

  * PER-CELL / PER-ROW; cross-row composition is the turn layer (`TurnEmit`), cited not claimed.
  * `state.RESERVED` not bound by the commitment (inherited finding).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
`Poseidon2SpongeCR hash`; the cap-table digest ONLY as `Function.Injective D`. No `sorry`, no `:= True`,
no `native_decide`, no `rfl`-posing-as-bridge. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Inst.delegate

namespace Dregg2.Circuit.Emit.EffectVmEmitDelegate

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptor gCapMove AttenRowIntent CapCellSpec capRootProj
   attenuateVm_faithful attenuateVm_rejects_wrong_capRoot attenuateDescriptor_full_sound
   IsAttenRow CapRowEncodes intent_to_capCellSpec)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.Inst.Delegate (DelegateArgs delegateE delegate_full_sound)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (DelegateSpec recDelegateCaps)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The runnable descriptor IS the reused cap-root-move circuit.

`delegate` emits the SAME runnable EffectVM row as `attenuateA`: a `cap_root` column MOVE to the post
cap-table digest, every other state column frozen, the moved post-state bound into `state_commit`. We
name it for `delegate` and re-export the validated faithfulness/anti-ghost as the `delegate` row's. -/

/-- **`delegateVmDescriptor`** — the runnable `delegate` circuit: definitionally the validated
cap-root-move descriptor (`attenuateVmDescriptor`). The `delegate`-specific content is the post
`cap_root` digest VALUE the witness supplies (universe-A's `recDelegateCaps` digest, §3). -/
def delegateVmDescriptor : EffectVmDescriptor := attenuateVmDescriptor

/-- The runnable `delegate` row pins EXACTLY the cap-graph intent (post `cap_root` = the supplied
digest, frame frozen) — the validated `attenuateVm_faithful`, re-exported for `delegate`. -/
theorem delegateVm_faithful (env : VmRowEnv) :
    (∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates, c.holdsVm env false false)
      ↔ AttenRowIntent env :=
  attenuateVm_faithful env

/-- **Anti-ghost.** A `delegate` row whose post-`cap_root` is NOT the supplied post-cap-digest fails the
cap-root MOVE gate (UNSAT) — the validated `attenuateVm_rejects_wrong_capRoot`. -/
theorem delegateVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT)
      ≠ env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.paramA.CAP_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gCapMove).holdsVm env false false :=
  attenuateVm_rejects_wrong_capRoot env hwrong

/-! ## §2 — The structured per-cell soundness (reused). -/

/-- **`delegateDescriptor_full_sound`** — satisfying the runnable `delegate` row's gates under the
cap-row decoding forces the structured per-cell `CapCellSpec` (post `cap_root` = the predicted digest,
frame frozen) — the validated `attenuateDescriptor_full_sound`. -/
theorem delegateDescriptor_full_sound (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates,
        c.holdsVm env false false) :
    CapCellSpec pre post capDigestNew :=
  attenuateDescriptor_full_sound env pre post capDigestNew henc hgates

/-! ## §3 — THE CONNECTOR — `capRootProj` to universe-A's `delegate_full_sound`. -/

/-- The predicted post cap-digest the descriptor's `param.CAP_DIGEST_NEW` carries for `delegate`: `D` of
the post cap-table `recDelegateCaps caps del rec t`. -/
def delegateCapDigestNew (D : Caps → ℤ) (s : RecChainedState) (args : DelegateArgs) : ℤ :=
  D (recDelegateCaps s.kernel.caps args.del args.recipient args.target)

/-- **`unify_delegate` — THE CONNECTOR.** When universe-A's `DelegateSpec` holds, the projected
post-`cap_root` is EXACTLY the delegate cap-digest `delegateCapDigestNew D s args` — the column move the
runnable descriptor pins. So `CapCellSpec`'s `cap_root` clause IS universe-A's `caps`-clause, projected
to the digest column. -/
theorem unify_delegate (D : Caps → ℤ) (s : RecChainedState) (args : DelegateArgs)
    (s' : RecChainedState)
    (hspec : DelegateSpec s args.del args.recipient args.target s') :
    capRootProj D s'.kernel = delegateCapDigestNew D s args := by
  -- DelegateSpec's `caps` clause: `s'.kernel.caps = recDelegateCaps s.kernel.caps del rec t`.
  obtain ⟨_hguard, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D (recDelegateCaps s.kernel.caps args.del args.recipient args.target)
  rw [hcaps]

/-- **`unify_delegate_via_full_sound` — the runnable column move inherits the VALIDATED guarantee.**
Chaining universe-A's `delegate_full_sound` (a satisfying v2 full-state witness, with the Granovetter
GUARD enforced by the `propBit (delegateGuard)` column, ⟹ `DelegateSpec`) with `unify_delegate`: a
satisfying universe-A witness forces the projected post-`cap_root` to the delegate cap-digest — the EXACT
column the runnable descriptor's `param.CAP_DIGEST_NEW` carries. So the runnable `cap_root` move is
universe-A's validated `caps` transition (guard included), not a fourth spec. -/
theorem unify_delegate_via_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (delegateE D hD) (encodeE2 S (delegateE D hD) s args s')) :
    capRootProj D s'.kernel = delegateCapDigestNew D s args :=
  unify_delegate D s args s' (delegate_full_sound S D hD hRest hLog s args s' h)

/-! ## §4 — NON-VACUITY: the reused row's witnesses fire (the descriptor is inhabited + refutable).

`EffectVmEmitAttenuateA.capGoodRow`/`capBadRow` are concrete `cap_root`-move rows that realize / violate
the intent; they are the runnable `delegate` row's witnesses too (same descriptor). We confirm the
faithfulness fires on the good row and the anti-ghost on the bad row, re-exported for `delegate`. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (capGoodRow capBadRow capGoodRow_realizes_intent capBadRow_rejected)

/-- **NON-VACUITY (witness TRUE).** The good cap-root row realizes the cap-graph intent — so the runnable
`delegate` descriptor's intent side is inhabited (not `False`). -/
theorem delegateGoodRow_realizes_intent : AttenRowIntent capGoodRow := capGoodRow_realizes_intent

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** The forged cap-root row is REJECTED by the
cap-root MOVE gate — a concrete UNSAT for the runnable `delegate` descriptor. -/
theorem delegateBadRow_rejected : ¬ (VmConstraint.gate gCapMove).holdsVm capBadRow false false :=
  capBadRow_rejected

/-! ## §G — THE GENUINE CLASS-A `delegate` — `cap_root` RECOMPUTED in-row (inherits the shared primitive).

`delegate` is the SAME runnable cap-graph row as `attenuateA`, so it inherits the GENUINE class-A descriptor
`attenuateVmDescriptorGenuine` (the opaque `param.CAP_DIGEST_NEW` move REPLACED by the FORCED in-row
recompute `new_cap_root = hash[edge_leaf, old_cap_root]`, `edge_leaf = hash[holder,target,rights,op]`). The
`delegate`-specific content is the OP tag `capOp.DELEGATE = 1` carried in the edge leaf (so the recomputed
root pins that this is a DELEGATE mutation), and the connector `unify_delegate` to universe-A's
`recDelegateCaps`. We re-export the genuine soundness + edge-binding anti-ghost for `delegate`. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorGenuine attenuateGenuineRowGates CapCellSpecGenuine
   attenuateGenuine_sound attenuateGenuine_binds_edge)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds capRecomputeSites)
open Dregg2.Circuit.Emit.EffectVmEmit (saCol sbCol prmCol VmRowEnv VmConstraint siteHoldsAll)

/-- **`delegateVmDescriptorGenuine`** — the GENUINE `delegate` circuit: definitionally the shared genuine
cap-root-recompute descriptor. The `delegate` content is the OP tag + the `recDelegateCaps` connector. -/
def delegateVmDescriptorGenuine : EffectVmDescriptor := attenuateVmDescriptorGenuine

/-- **`delegateGenuine_sound` — THE CLASS-A THEOREM for `delegate`.** Satisfying the genuine descriptor's
frame-freeze gates AND the in-row cap-root recompute forces the GENUINE full per-cell post-state:
`post.capRoot` is the FORCED advance `hash[edge_leaf, pre.capRoot]` (NOT an opaque parameter), every other
field frozen. Inherited from the shared `attenuateGenuine_sound`. -/
theorem delegateGenuine_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState) (capDigestNew : ℤ)
    (henc : Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env) :
    CapCellSpecGenuine hash env pre post :=
  attenuateGenuine_sound hash env pre post capDigestNew henc hgates hrec

/-- **`delegateGenuine_binds_edge` — the genuine class-A anti-ghost for `delegate`.** Two genuine `delegate`
rows with EQUAL published `state_commit` share the old `cap_root` AND every bound edge field
(holder/target/rights/op) — so tampering the delegated cap-edge moves `cap_root`, moves `state_commit` ⇒
UNSAT. Inherited from the shared `attenuateGenuine_binds_edge`. -/
theorem delegateGenuine_binds_edge (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsCommit₁ : siteHoldsAll hash e₁ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateHashSites)
    (hsCommit₂ : siteHoldsAll hash e₂ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateHashSites)
    (hrec₁ : capRootHolds hash e₁) (hrec₂ : capRootHolds hash e₂)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (sbCol state.CAP_ROOT) = e₂.loc (sbCol state.CAP_ROOT)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP) :=
  attenuateGenuine_binds_edge hash hCR e₁ e₂ hsCommit₁ hsCommit₂ hrec₁ hrec₂ hcommit

/-! ## §W — THE MAGNESIUM LIFT: `delegate`'s RUNNABLE descriptor binds the FULL 17-field post-state.

`delegate` is the SAME runnable cap-graph row as `attenuateA`, so it inherits the SHARED cap-graph WIDE
descriptor `attenuateVmDescriptorWide` (`EffectVmEmitAttenuateA §W`): the cap-root MOVE + frame freeze
gates UNCHANGED, but widened to `EFFECT_VM_WIDTH_SYSROOTS` with `wideHashSites` so the published
`state_commit` now absorbs the `system_roots` digest. A satisfying wide row pins the FULL 17-field
post-state (per-cell block — incl. the moved `cap_root` — AND the 8 side-table roots). `delegate`'s
kernel step `recDelegateCaps` edits ONLY `caps`; the 8 side-table roots are FROZEN, so the full clause is
the per-cell `CapCellSpec` (cap_root = `delegateCapDigestNew`) AND `postRoots = preRoots`. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorWide CapFullClause capRunnableSpec cap_runnable_full_sound
   cap_runnable_binds_full_state cap_runnable_rejects_cap_root_tamper cap_runnable_rejects_root_tamper
   IsAttenRow CapRowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (absorbedCols)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots)

/-- **`delegateVmDescriptorWide`** — the runnable `delegate` FULL-state circuit: definitionally the shared
cap-graph WIDE descriptor (`attenuateVmDescriptorWide`), 188-wide with `wideHashSites`. The
`delegate`-specific content is the post `cap_root` digest VALUE the witness supplies
(`delegateCapDigestNew D s args` = the `recDelegateCaps` digest), connected below. -/
def delegateVmDescriptorWide : EffectVmDescriptor := attenuateVmDescriptorWide

/-- **`delegate_runnable_full_sound` — THE MAGNESIUM CROWN for `delegate`.** A row satisfying the runnable
`delegate` WIDE descriptor (`satisfiedVm`, first/last active), under the structured decode (the post
`cap_root` carrying `delegateCapDigestNew D s args`, the roots frozen), pins the FULL 17-field cap-graph
post-state: the per-cell `cap_root` MOVE to the delegate digest + frame freeze (binding `cell`/`caps`/
`bal`-here + frame) AND the frozen `system_roots` sub-block (binding the 8 side-table roots). The
`cap_root` value is universe-A's validated `recDelegateCaps` digest via `unify_delegate` (cited). -/
theorem delegate_runnable_full_sound (D : Caps → ℤ) (s : RecChainedState) (args : DelegateArgs)
    (preRoots : SysRoots) (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState)
    (postRoots : SysRoots)
    (hrow : IsAttenRow env)
    (henc : CapRowEncodes env pre post (delegateCapDigestNew D s args))
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash delegateVmDescriptorWide env true true) :
    CapFullClause (delegateCapDigestNew D s args) preRoots pre post postRoots :=
  cap_runnable_full_sound (delegateCapDigestNew D s args) preRoots hash env pre post postRoots
    hrow henc hroots hsat

/-- **`delegate_runnable_binds_full_state` — the whole-17-field anti-ghost for `delegate`.** Two wide
`delegate` rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) agree on EVERY
absorbed state-block column (the moved `cap_root` included) AND every side-table root — so a prover cannot
keep `NEW_COMMIT` while tampering ANY of the 17 fields. Inherited from the shared
`cap_runnable_binds_full_state`. -/
theorem delegate_runnable_binds_full_state (capDigestNew : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash delegateVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash delegateVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂
    ∧ (∀ i : Fin Dregg2.Exec.SystemRoots.N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  cap_runnable_binds_full_state capDigestNew preRoots hash hCR
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

#assert_axioms delegate_runnable_full_sound
#assert_axioms delegate_runnable_binds_full_state

/-! ## §5 — Axiom-hygiene tripwires (the honesty tripwire). -/

#assert_axioms delegateVm_faithful
#assert_axioms delegateVm_rejects_wrong_capRoot
#assert_axioms delegateDescriptor_full_sound
#assert_axioms unify_delegate
#assert_axioms unify_delegate_via_full_sound
#assert_axioms delegateGoodRow_realizes_intent
#assert_axioms delegateBadRow_rejected
#assert_axioms delegateGenuine_sound
#assert_axioms delegateGenuine_binds_edge

end Dregg2.Circuit.Emit.EffectVmEmitDelegate
