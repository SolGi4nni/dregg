/-
# Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation — the AUTHORITY-REVOCATION effect `revokeDelegationA`,
  CONNECTED to the runnable EffectVM `cap_root` column descriptor + the validated universe-A
  `revokeDelegationA_full_sound`.

## ONE circuit — `revokeDelegationA` is a `cap_root` COLUMN MOVE (the same runnable row as `attenuateA`)

`revokeDelegationA` (`Inst/revokeDelegationA.lean`) is a `caps`-touching v2 instance: it touches the
`caps` table as a WHOLE-FUNCTION injective digest, predicted post value `removeEdgeCaps caps holder t`
(the REMOVAL of the `t`-conferring edge from `holder`'s slot — every other holder's slot whole), freezes
the other 16 kernel fields, and is UNCONDITIONAL (the trivial `True` guard — revocation always commits).
Its validation `revokeDelegationA_full_sound ⇒ RevokeSpec` is DONE.

On the running EffectVM row layout it is EXACTLY the cap-graph row `attenuateA` emits — a `cap_root`
COLUMN MOVE to the post (smaller) cap-table digest, every other state column frozen, the moved post-state
bound into `state_commit` under Poseidon2 CR. This module REUSES the validated `EffectVmEmitAttenuateA`
cap-root-move descriptor (ONE circuit) and adds the `revokeDelegationA` CONNECTOR.

## The CONNECTOR — `capRootProj` to `revokeDelegationA_full_sound`

`unify_revoke`: when `RevokeSpec` holds (so `k'.caps = removeEdgeCaps k.caps holder t`), the projected
post-`cap_root` `D k'.caps` is EXACTLY `D (removeEdgeCaps k.caps holder t)` — the column move the
descriptor pins. So the runnable `cap_root` transition IS universe-A's validated `caps`-digest
transition; not a fourth spec.

## HONEST BOUNDARY (precise)

  * **IR GAP — needs IR extension: cap-root hash-site** (inherited). The `cap_root` column is the SCALAR
    digest of the cap-table FUNCTION; the IR cannot re-derive it IN-circuit from the cap-table rows. The
    cap-table-is-genuinely-Merkled binding lives in `Function.Injective D` (carried, realizable), the
    SAME bar `revokeDelegationA_full_sound` uses. We connect through `capRootProj`.

  * **REMOVAL (the edge is genuinely gone) is INSIDE the `caps` value, not a separate row gate.** The
    runnable `cap_root` move pins `post.caps = D⁻¹(cap_root)`; that this post cap-table is the held-cap
    table with the `holder→t` edge REMOVED (`removeEdgeCaps …`) is a property of universe-A's predicted
    `caps` VALUE, enforced by `Function.Injective D` + `revokeDelegationA_full_sound`, NOT by an
    in-circuit removal gate. The runnable row binds the WHOLE post cap-table digest; revocation
    semantics ride the validated universe-A value, reported here, not re-proved in-row.

  * PER-CELL / PER-ROW; `state.RESERVED` not commitment-bound (inherited findings).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR`;
cap-table digest ONLY as `Function.Injective D`. No `sorry`/`:= True`/`native_decide`/rfl-bridge.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Inst.revokeDelegationA

namespace Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptor gCapMove AttenRowIntent CapCellSpec capRootProj
   attenuateVm_faithful attenuateVm_rejects_wrong_capRoot attenuateDescriptor_full_sound
   CapRowEncodes)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.Inst.RevokeDelegationA (RevokeArgs revokeDelegationE revokeDelegationA_full_sound)
open Dregg2.Circuit.Spec.AuthorityRevocation (RevokeSpec removeEdgeCaps)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The runnable descriptor IS the reused cap-root-move circuit. -/

/-- **`revokeVmDescriptor`** — the runnable `revokeDelegationA` circuit: definitionally the validated
cap-root-move descriptor. The effect-specific content is the post `cap_root` digest VALUE (§3). -/
def revokeVmDescriptor : EffectVmDescriptor := attenuateVmDescriptor

/-- The runnable `revokeDelegationA` row pins EXACTLY the cap-graph intent — the validated faithfulness. -/
theorem revokeVm_faithful (env : VmRowEnv) :
    (∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates, c.holdsVm env false false)
      ↔ AttenRowIntent env :=
  attenuateVm_faithful env

/-- **Anti-ghost.** A `revokeDelegationA` row whose post-`cap_root` ≠ the supplied digest fails the MOVE
gate (UNSAT). -/
theorem revokeVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT)
      ≠ env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.paramA.CAP_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gCapMove).holdsVm env false false :=
  attenuateVm_rejects_wrong_capRoot env hwrong

/-! ## §2 — The structured per-cell soundness (reused). -/

/-- **`revokeDescriptor_full_sound`** — satisfying the runnable row's gates under the cap-row decoding
forces the structured per-cell `CapCellSpec` — the validated `attenuateDescriptor_full_sound`. -/
theorem revokeDescriptor_full_sound (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates,
        c.holdsVm env false false) :
    CapCellSpec pre post capDigestNew :=
  attenuateDescriptor_full_sound env pre post capDigestNew henc hgates

/-! ## §3 — THE CONNECTOR — `capRootProj` to universe-A's `revokeDelegationA_full_sound`. -/

/-- The predicted post cap-digest the descriptor's `param.CAP_DIGEST_NEW` carries for
`revokeDelegationA`: `D` of the post cap-table `removeEdgeCaps caps holder t`. -/
def revokeCapDigestNew (D : Caps → ℤ) (s : RecChainedState) (args : RevokeArgs) : ℤ :=
  D (removeEdgeCaps s.kernel.caps args.holder args.t)

/-- **`unify_revoke` — THE CONNECTOR.** When `RevokeSpec` holds, the projected post-`cap_root` is EXACTLY
the edge-removed cap-digest `revokeCapDigestNew D s args` — the column move the runnable descriptor pins. -/
theorem unify_revoke (D : Caps → ℤ) (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (hspec : RevokeSpec s args.holder args.t s') :
    capRootProj D s'.kernel = revokeCapDigestNew D s args := by
  -- RevokeSpec's `caps` clause: `s'.kernel.caps = removeEdgeCaps s.kernel.caps holder t`.
  obtain ⟨_hguard, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D (removeEdgeCaps s.kernel.caps args.holder args.t)
  rw [hcaps]

/-- **`unify_revoke_via_full_sound` — inherits the VALIDATED guarantee.** Chaining
`revokeDelegationA_full_sound` (a satisfying v2 full-state witness ⟹ `RevokeSpec`) with `unify_revoke`:
a satisfying universe-A witness forces the projected post-`cap_root` to the edge-removed cap-digest — the
EXACT column the runnable descriptor's `param.CAP_DIGEST_NEW` carries. -/
theorem unify_revoke_via_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.RevokeDelegationA.RestIffNoCaps S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (revokeDelegationE D hD) (encodeE2 S (revokeDelegationE D hD) s args s')) :
    capRootProj D s'.kernel = revokeCapDigestNew D s args :=
  unify_revoke D s args s' (revokeDelegationA_full_sound S D hD hRest hLog s args s' h)

/-! ## §4 — NON-VACUITY (the reused row's witnesses fire). -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (capGoodRow capBadRow capGoodRow_realizes_intent capBadRow_rejected)

/-- **NON-VACUITY (witness TRUE).** The good cap-root row realizes the intent — the runnable
`revokeDelegationA` descriptor's intent side is inhabited. -/
theorem revokeGoodRow_realizes_intent : AttenRowIntent capGoodRow := capGoodRow_realizes_intent

/-- **NON-VACUITY (witness FALSE / anti-ghost).** The forged cap-root row is REJECTED — a concrete UNSAT. -/
theorem revokeBadRow_rejected : ¬ (VmConstraint.gate gCapMove).holdsVm capBadRow false false :=
  capBadRow_rejected

/-! ## §5 — Axiom-hygiene tripwires. -/

#assert_axioms revokeVm_faithful
#assert_axioms revokeVm_rejects_wrong_capRoot
#assert_axioms revokeDescriptor_full_sound
#assert_axioms unify_revoke
#assert_axioms unify_revoke_via_full_sound
#assert_axioms revokeGoodRow_realizes_intent
#assert_axioms revokeBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
