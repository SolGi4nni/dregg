/-
# Dregg2.Circuit.Emit.EffectVmEmitDelegateAtten — the ATTENUATED-DELEGATE effect `delegateAttenA`,
  CONNECTED to the runnable EffectVM `cap_root` column descriptor + the validated universe-A
  `delegateAttenA_full_sound`.

## ONE circuit — `delegateAttenA` is a `cap_root` COLUMN MOVE (the same runnable row as `attenuateA`)

`delegateAttenA` (`Inst/delegateAttenA.lean`) is a `caps`-touching v2 instance: it touches the `caps`
table as a WHOLE-FUNCTION injective digest, predicted post value
`grant caps recv (attenuate keep (heldCapTo caps del t))` (the recipient's slot GAINS an ATTENUATED copy
of the delegator's held `t`-conferring cap), freezes the other 16 kernel fields, GATED by
`DelegateAttenGuard`. Its validation `delegateAttenA_full_sound ⇒ DelegateAttenSpec` is DONE.

On the running EffectVM row layout it is EXACTLY the cap-graph row `attenuateA` emits — a `cap_root`
COLUMN MOVE to the post cap-table digest, every other state column frozen, the moved post-state bound
into `state_commit` under Poseidon2 CR. This module REUSES the validated `EffectVmEmitAttenuateA`
cap-root-move descriptor (ONE circuit) and adds the `delegateAttenA` CONNECTOR.

## The CONNECTOR — `capRootProj` to `delegateAttenA_full_sound`

`unify_delegateAtten`: when `DelegateAttenSpec` holds (so `k'.caps = grant caps recv (attenuate keep
(heldCapTo caps del t))`), the projected post-`cap_root` `D k'.caps` is EXACTLY `D` of that attenuated
grant — the column move the descriptor pins. So the runnable `cap_root` transition IS universe-A's
validated `caps`-digest transition; not a fourth spec.

## HONEST BOUNDARY (precise)

  * **IR GAP — needs IR extension: cap-root hash-site** (inherited). The `cap_root` column is the SCALAR
    digest of the cap-table FUNCTION; the IR cannot re-derive it IN-circuit from the cap-table rows. The
    cap-table-is-genuinely-Merkled binding lives in `Function.Injective D` (carried, realizable), the
    SAME bar `delegateAttenA_full_sound` uses. We connect through `capRootProj`.

  * **The attenuation premise (`DelegateAttenGuard`) is NOT a `cap_root` ROW gate.** It is enforced by
    `delegateAttenA_full_sound`'s `propBit (DelegateAttenGuard)` column, NOT by the cap-root-move row
    gates this module reuses. `unify_delegateAtten_via_full_sound` carries it through the hypothesis;
    the runnable row pins only the MOVE. Flagged, not papered.

  * **ATTENUATION (narrower-or-equal rights) is INSIDE the `caps` value, not a separate row gate.** The
    runnable `cap_root` move pins `post.caps = D⁻¹(cap_root)`; that the granted cap is the ATTENUATED
    `attenuate keep …` (rights ⊆ the held cap) is a property of universe-A's predicted `caps` VALUE
    (`grant … (attenuate keep …)`), enforced by `Function.Injective D` + `delegateAttenA_full_sound`,
    NOT by an in-circuit subset gate. So the runnable row binds the WHOLE post cap-table digest; the
    attenuation semantics ride the validated universe-A value, reported here, not re-proved in-row.

  * PER-CELL / PER-ROW; `state.RESERVED` not commitment-bound (inherited findings).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR`;
cap-table digest ONLY as `Function.Injective D`. No `sorry`/`:= True`/`native_decide`/rfl-bridge.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Inst.delegateAttenA

namespace Dregg2.Circuit.Emit.EffectVmEmitDelegateAtten

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptor gCapMove AttenRowIntent CapCellSpec capRootProj
   attenuateVm_faithful attenuateVm_rejects_wrong_capRoot attenuateDescriptor_full_sound
   CapRowEncodes)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.Inst.DelegateAttenA (DelegateAttenArgs delegateAttenE delegateAttenA_full_sound)
open Dregg2.Circuit.Spec.AuthorityAttenuation (DelegateAttenSpec)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The runnable descriptor IS the reused cap-root-move circuit. -/

/-- **`delegateAttenVmDescriptor`** — the runnable `delegateAttenA` circuit: definitionally the validated
cap-root-move descriptor. The effect-specific content is the post `cap_root` digest VALUE (§3). -/
def delegateAttenVmDescriptor : EffectVmDescriptor := attenuateVmDescriptor

/-- The runnable `delegateAttenA` row pins EXACTLY the cap-graph intent — the validated faithfulness. -/
theorem delegateAttenVm_faithful (env : VmRowEnv) :
    (∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates, c.holdsVm env false false)
      ↔ AttenRowIntent env :=
  attenuateVm_faithful env

/-- **Anti-ghost.** A `delegateAttenA` row whose post-`cap_root` ≠ the supplied digest fails the MOVE
gate (UNSAT). -/
theorem delegateAttenVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT)
      ≠ env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.paramA.CAP_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gCapMove).holdsVm env false false :=
  attenuateVm_rejects_wrong_capRoot env hwrong

/-! ## §2 — The structured per-cell soundness (reused). -/

/-- **`delegateAttenDescriptor_full_sound`** — satisfying the runnable row's gates under the cap-row
decoding forces the structured per-cell `CapCellSpec` — the validated `attenuateDescriptor_full_sound`. -/
theorem delegateAttenDescriptor_full_sound (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates,
        c.holdsVm env false false) :
    CapCellSpec pre post capDigestNew :=
  attenuateDescriptor_full_sound env pre post capDigestNew henc hgates

/-! ## §3 — THE CONNECTOR — `capRootProj` to universe-A's `delegateAttenA_full_sound`. -/

/-- The predicted post cap-digest the descriptor's `param.CAP_DIGEST_NEW` carries for `delegateAttenA`:
`D` of the ATTENUATED grant `grant caps recv (attenuate keep (heldCapTo caps del t))`. -/
def delegateAttenCapDigestNew (D : Caps → ℤ) (s : RecChainedState) (args : DelegateAttenArgs) : ℤ :=
  D (grant s.kernel.caps args.recv (attenuate args.keep (heldCapTo s.kernel.caps args.del args.t)))

/-- **`unify_delegateAtten` — THE CONNECTOR.** When `DelegateAttenSpec` holds, the projected post-`cap_root`
is EXACTLY the attenuated-grant cap-digest `delegateAttenCapDigestNew D s args` — the column move the
runnable descriptor pins. -/
theorem unify_delegateAtten (D : Caps → ℤ) (s : RecChainedState) (args : DelegateAttenArgs)
    (s' : RecChainedState)
    (hspec : DelegateAttenSpec s args.del args.recv args.t args.keep s') :
    capRootProj D s'.kernel = delegateAttenCapDigestNew D s args := by
  -- DelegateAttenSpec's `caps` clause: `s'.kernel.caps = grant caps recv (attenuate keep (heldCapTo …))`.
  obtain ⟨_hguard, hcaps, _⟩ := hspec
  show D s'.kernel.caps
      = D (grant s.kernel.caps args.recv (attenuate args.keep (heldCapTo s.kernel.caps args.del args.t)))
  rw [hcaps]

/-- **`unify_delegateAtten_via_full_sound` — inherits the VALIDATED guarantee.** Chaining
`delegateAttenA_full_sound` (the attenuation GUARD enforced by `propBit (DelegateAttenGuard)`, ⟹
`DelegateAttenSpec`) with `unify_delegateAtten`: a satisfying universe-A witness forces the projected
post-`cap_root` to the attenuated-grant cap-digest — the EXACT column the descriptor pins. -/
theorem unify_delegateAtten_via_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (delegateAttenE D hD) (encodeE2 S (delegateAttenE D hD) s args s')) :
    capRootProj D s'.kernel = delegateAttenCapDigestNew D s args :=
  unify_delegateAtten D s args s' (delegateAttenA_full_sound S D hD hRest hLog s args s' h)

/-! ## §4 — NON-VACUITY (the reused row's witnesses fire). -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (capGoodRow capBadRow capGoodRow_realizes_intent capBadRow_rejected)

/-- **NON-VACUITY (witness TRUE).** The good cap-root row realizes the intent — the runnable
`delegateAttenA` descriptor's intent side is inhabited. -/
theorem delegateAttenGoodRow_realizes_intent : AttenRowIntent capGoodRow := capGoodRow_realizes_intent

/-- **NON-VACUITY (witness FALSE / anti-ghost).** The forged cap-root row is REJECTED — a concrete UNSAT. -/
theorem delegateAttenBadRow_rejected : ¬ (VmConstraint.gate gCapMove).holdsVm capBadRow false false :=
  capBadRow_rejected

/-! ## §5 — Axiom-hygiene tripwires. -/

#assert_axioms delegateAttenVm_faithful
#assert_axioms delegateAttenVm_rejects_wrong_capRoot
#assert_axioms delegateAttenDescriptor_full_sound
#assert_axioms unify_delegateAtten
#assert_axioms unify_delegateAtten_via_full_sound
#assert_axioms delegateAttenGoodRow_realizes_intent
#assert_axioms delegateAttenBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitDelegateAtten
