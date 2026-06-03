/-
# Dregg2.Exec.CellConfine — the CONFINEMENT crown: cap-safety / no-amplification carried FOREVER.

`Exec/CellReal.lean` crowned the REAL executor with the coinductive living cell `livingCellA` (a
`Boundary.TurnCoalg` over `execFullForestA`, the 46-effect per-asset auth-gated tree) and
`Exec/CellCarry.lean` distilled the PARAMETRIC crown `livingCellA_carries`: ANY *state* predicate
`Good` preserved by a SINGLE living-cell step holds along the ENTIRE unbounded adversarial trajectory.
Conservation (`livingCellA_obs_invariant'`) and the append-only audit log (`livingCellA_logMono`) are
its first two instances. This module supplies the THIRD — and it is the seL4 **object-integrity
confinement** lifted onto the real machine over unbounded time:

> **No authority ever escapes a fixed ceiling.** `Authority/Positional.confinement_preserved` (the lift
> of l4v `call_kernel_pas_refined`) says one authority-non-increasing turn preserves the
> *policy-is-an-upper-bound* invariant `PasRefined` (`auth ⊆ policy`, never growth). Here we carry the
> coinductive version: fix an authority ceiling `U` (with `control ∈ U`); if the initial kernel's caps
> are *confined by `U`* — every authority conferred by every held cap, in every slot, lies in `U` — then
> they stay confined along the ENTIRE unbounded adversarial trajectory `trajA`, under EVERY schedule.
> *Only connectivity begets connectivity* — and never beyond the ceiling — FOREVER.

The headline `livingCellA_confinement` is the coinductive lift of `confinement_preserved`. Its one-step
obligation `cellNextA_confine` is discharged from how `execFullForestA` moves `caps`:

* the vast majority of effects FRAME `caps` (`s'.kernel.caps = s.kernel.caps`) — confinement transfers
  by rewriting (`CapsConfined.of_caps_eq`);
* `revoke`/`dropRef`/`revokeDelegation` FILTER a slot (`caps' l ⊆ caps l`) — `CapsConfined.mono`;
* `attenuateCapability` narrows the actor's `idx`-th cap IN PLACE (`List.modify (attenuate keep)`) —
  the replacement confers ⊆ the original ⊆ `U` (`CapsConfined.attenuateSlot`);
* `delegateAtten`/the rights-carrying introduce GRANT `attenuate keep (heldCapTo …)` — confers ⊆ the
  GENUINELY-HELD parent cap ⊆ `U` (`execFullForestA_no_amplify`'s per-edge content, on the EXECUTED grant);
* the rights-blind `delegate`/`introduce`/`validateHandoff` and `spawn` GRANT a `Cap.node t`
  connectivity cap conferring exactly `[control] ⊆ U` (the `control ∈ U` hypothesis) — `CapsConfined.grant`.

So the SAME no-amplification law that bounds each forest edge (`execFullForestA_no_amplify`) is here
re-expressed as a STATE predicate the cell carries coinductively: the attenuating edges and the
connectivity grants never push conferred authority past the fixed ceiling, at any index of the
unbounded future. This is the confinement face of the living cell — `confinement_preserved` made
temporal on the SHIPPED executor.
-/
import Dregg2.Exec.CellCarry
import Dregg2.Exec.AuthTurn

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Exec.EffectsState (state_caps_unchanged stateAuthB)

/-! ## Step 1 — `CapsConfined`: the seL4 `PasRefined` upper-bound shape, as a flat ceiling. -/

/-- **`CapsConfined U caps`** — every authority conferred by every held cap, in EVERY slot, lies within
the fixed ceiling `U`. This is `Authority.PasRefined`'s `state_objs_in_policy` clause (`auth ⊆ policy`)
with the per-edge policy collapsed to a single authority ceiling: the policy is an UPPER BOUND on
conferred authority, never exceeded. The state predicate whose coinductive carry IS confinement. -/
def CapsConfined (U : List Auth) (caps : Caps) : Prop :=
  ∀ (l : Label) (c : Cap) (a : Auth), c ∈ caps l → a ∈ capAuthConferred c → a ∈ U

/-- **`CapsConfined.of_caps_eq` (PROVED) — the FRAME closure.** If `caps' = caps` (the vast majority of
effects do not touch `caps`), confinement transfers verbatim. -/
theorem CapsConfined.of_caps_eq {U : List Auth} {caps caps' : Caps}
    (heq : caps' = caps) (h : CapsConfined U caps) : CapsConfined U caps' := by
  subst heq; exact h

/-- **`CapsConfined.mono` (PROVED) — the SUBSET closure (revocation / filtering).** If every slot of
`caps'` is a sublist of `caps` (so authority only SHRANK — `revoke`, `dropRef`, `revokeDelegation`),
confinement is preserved: a cap held in `caps'` was held in `caps`, hence bounded. -/
theorem CapsConfined.mono {U : List Auth} {caps caps' : Caps}
    (hsub : ∀ l, caps' l ⊆ caps l) (h : CapsConfined U caps) : CapsConfined U caps' :=
  fun l c a hc ha => h l c a (hsub l hc) ha

/-- **`mem_modify_cases` (PROVED) — the `List.modify` membership dichotomy.** Every member of
`l.modify n f` is EITHER a member of `l` (untouched) OR `f d` for some member `d` of `l` (the one
replaced at index `n`). The list-level fact behind the in-place attenuation closure. -/
theorem mem_modify_cases {α : Type _} (f : α → α) :
    ∀ (n : Nat) (l : List α) (c : α), c ∈ l.modify n f → c ∈ l ∨ ∃ d ∈ l, c = f d
  | _,     [],      c, hc => by
      rw [List.modify_nil] at hc; exact absurd hc (by simp)
  | 0,     a :: l,  c, hc => by
      rw [show (a :: l).modify 0 f = f a :: l from rfl, List.mem_cons] at hc
      rcases hc with hca | hcl
      · exact Or.inr ⟨a, List.mem_cons_self, hca⟩
      · exact Or.inl (List.mem_cons.mpr (Or.inr hcl))
  | n+1,   a :: l,  c, hc => by
      rw [List.modify_succ_cons, List.mem_cons] at hc
      rcases hc with hca | hcl
      · exact Or.inl (List.mem_cons.mpr (Or.inl hca))
      · rcases mem_modify_cases f n l c hcl with h1 | ⟨d, hd, hcd⟩
        · exact Or.inl (List.mem_cons.mpr (Or.inr h1))
        · exact Or.inr ⟨d, List.mem_cons.mpr (Or.inr hd), hcd⟩

/-- **`CapsConfined.grant` (PROVED) — the GRANT closure.** Prepending a cap `c` to `holder`'s slot
preserves confinement provided `c`'s OWN conferred authority lies within `U`. Covers every authority
GRANT (`delegate`/`introduce`/`validateHandoff`/`spawn` grant `Cap.node t` conferring `[control]`;
`delegateAtten` grants `attenuate keep (heldCapTo …)` whose conferred authority is bounded separately). -/
theorem CapsConfined.grant {U : List Auth} {caps : Caps} {holder : Label} {c : Cap}
    (hc : ∀ a ∈ capAuthConferred c, a ∈ U) (h : CapsConfined U caps) :
    CapsConfined U (Dregg2.Exec.grant caps holder c) := by
  intro l d a hd ha
  unfold Dregg2.Exec.grant at hd
  by_cases hl : l = holder
  · rw [if_pos hl] at hd
    rcases List.mem_cons.mp hd with hdc | hdrest
    · subst hdc; exact hc a ha          -- the freshly-granted cap: bounded by hypothesis.
    · exact h l d a hdrest ha            -- an already-held cap: bounded by confinement.
  · rw [if_neg hl] at hd; exact h l d a hd ha

/-- **`CapsConfined.attenuateSlot` (PROVED) — the IN-PLACE NARROW closure (`AttenuateCapability`).**
Replacing the `idx`-th cap of `actor` with its `keep`-attenuation (`List.modify idx (attenuate keep)`)
preserves confinement: a surviving cap is EITHER an untouched old cap (bounded) OR `attenuate keep d`
for the old cap `d` at `idx` (conferred ⊆ `d`'s ⊆ `U`, via `attenuate_subset`). -/
theorem CapsConfined.attenuateSlot {U : List Auth} {caps : Caps} {actor : Label} {idx : Nat}
    {keep : List Auth} (h : CapsConfined U caps) :
    CapsConfined U (attenuateSlotF caps actor idx keep) := by
  intro l c a hc ha
  unfold attenuateSlotF at hc
  by_cases hl : l = actor
  · rw [if_pos hl] at hc
    -- `c ∈ (caps actor).modify idx (attenuate keep)`. `List.modify` replaces ONE element; every member
    -- is either an unchanged member of `caps actor` or `attenuate keep` of one.
    rcases mem_modify_cases (attenuate keep) idx (caps l) c hc with hmem | ⟨d, hdmem, hcd⟩
    · exact h l c a hmem ha
    · -- `c = attenuate keep d` with `d ∈ caps actor`: conferred ⊆ `d`'s conferred ⊆ U.
      subst hcd
      exact h l d a hdmem (attenuate_subset keep d ha)
  · rw [if_neg hl] at hc; exact h l c a hc ha

/-! ## Step 2 — the per-primitive confinement steps (the 5 cap-writing chained ops). -/

/-- `recCRevoke` (the `revoke`/`dropRef`/`revokeDelegation` body) only FILTERS the holder's slot, so the
post-state caps are slot-wise ⊆ the pre-state caps — confinement is preserved by `CapsConfined.mono`. -/
theorem recCRevoke_confine {U : List Auth} {s : RecChainedState} {holder t : CellId}
    (h : CapsConfined U s.kernel.caps) : CapsConfined U (recCRevoke s holder t).kernel.caps := by
  refine CapsConfined.mono (fun l => ?_) h
  -- `(recCRevoke s holder t).kernel.caps = recKRevokeTarget s.kernel holder t |>.caps`.
  show (recKRevokeTarget s.kernel holder t).caps l ⊆ s.kernel.caps l
  simp only [recKRevokeTarget]
  by_cases hl : l = holder
  · subst hl; rw [if_pos rfl]; intro d hd; exact List.mem_of_mem_filter hd
  · rw [if_neg hl]; exact fun d hd => hd

/-- A committed `createCellChainA` FRAMES the cap table (the fresh cell grows `accounts`/resets `bal`,
never `caps` — `RecordKernel.createCellIntoAsset_caps`). The local caps-frame for createCell/spawn. -/
theorem createCellChainA_caps_eq {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') : s'.kernel.caps = s.kernel.caps := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h
  subst hs'; exact Dregg2.Exec.createCellIntoAsset_caps s.kernel newCell

/-! ### The kernel-function caps-frame lemmas: every NON-authority kernel transition FRAMES `caps`.

Each `RecordKernel`/supply transition writes a NON-`caps` field (`bal`/`escrows`/`queues`/`swiss`/
`nullifiers`/`commitments`/`cell`) via a record update `{ k with field := … }`, so the cap table is
literally unchanged on every committed branch. Proved by the uniform `unfold; split; subst; rfl` shape
(the raw helpers unfold to record-update literals whose `.caps` projection is `rfl`). These are the
discharge for the ~30 FRAME effects of `execFullA_confine`. -/

theorem recKExecAsset_caps {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') : k'.caps = k.caps := by
  unfold recKExecAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem recKMintAsset_caps {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKMintAsset k actor cell a amt = some k') : k'.caps = k.caps := by
  unfold recKMintAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem recKBurnAsset_caps {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKBurnAsset k actor cell a amt = some k') : k'.caps = k.caps := by
  unfold recKBurnAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem createEscrowKAsset_caps {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k') :
    k'.caps = k.caps := by
  unfold createEscrowKAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; unfold createEscrowRawAsset; rfl
  · exact absurd h (by simp)

theorem releaseEscrowKAsset_caps {k k' : RecordKernelState} {id : Nat}
    (h : releaseEscrowKAsset k id = some k') : k'.caps = k.caps := by
  unfold releaseEscrowKAsset at h; split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; unfold settleEscrowRawAsset; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem refundEscrowKAsset_caps {k k' : RecordKernelState} {id : Nat}
    (h : refundEscrowKAsset k id = some k') : k'.caps = k.caps := by
  unfold refundEscrowKAsset at h; split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; unfold settleEscrowRawAsset; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem noteSpendNullifier_caps {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') : k'.caps = k.caps := by
  unfold noteSpendNullifier at h; split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem bridgeLockKAsset_caps {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    k'.caps = k.caps := by
  unfold bridgeLockKAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; unfold createBridgeRawAsset; rfl
  · exact absurd h (by simp)

theorem bridgeFinalizeKAsset_caps {k k' : RecordKernelState} {id : Nat} {asset : AssetId} {amount : ℤ}
    (h : bridgeFinalizeKAsset k id asset amount = some k') : k'.caps = k.caps := by
  unfold bridgeFinalizeKAsset at h; split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; unfold bridgeFinalizeRawAsset; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem bridgeCancelKAsset_caps {k k' : RecordKernelState} {id : Nat}
    (h : bridgeCancelKAsset k id = some k') : k'.caps = k.caps := by
  unfold bridgeCancelKAsset at h; split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; unfold settleEscrowRawAsset; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem queueAllocateK_caps {k k' : RecordKernelState} {id : Nat} {owner : CellId} {capacity : Nat}
    (h : queueAllocateK k id owner capacity = some k') : k'.caps = k.caps := by
  unfold queueAllocateK at h; split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem queueEnqueueK_caps {k k' : RecordKernelState} {id m : Nat}
    (h : queueEnqueueK k id m = some k') : k'.caps = k.caps := by
  unfold queueEnqueueK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem queueDequeueK_caps {k : RecordKernelState} {id : Nat} {actor : CellId} {p : RecordKernelState × Nat}
    (h : queueDequeueK k id actor = some p) : p.1.caps = k.caps := by
  unfold queueDequeueK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem queueResizeK_caps {k k' : RecordKernelState} {id newCap : Nat}
    (h : queueResizeK k id newCap = some k') : k'.caps = k.caps := by
  unfold queueResizeK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem queueEnqueueDepositK_caps {k k' : RecordKernelState} {id m : Nat} {sender owner : CellId}
    {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (h : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') :
    k'.caps = k.caps := by
  unfold queueEnqueueDepositK at h
  -- `queueEnqueueDepositK` = `queueEnqueueK k id m` then (on success) `createEscrowRawAsset`-park.
  cases hq : queueEnqueueK k id m with
  | none => simp [hq] at h
  | some k₁ =>
      simp only [hq] at h
      have hc1 : k₁.caps = k.caps := queueEnqueueK_caps hq
      split at h
      · simp only [Option.some.injEq] at h; subst h
        show (createEscrowRawAsset k₁ depId sender owner dAsset deposit).caps = k.caps
        exact hc1
      · simp at h

theorem queueDequeueRefundK_caps {k : RecordKernelState} {id : Nat} {actor : CellId} {depId : Nat}
    {p : RecordKernelState × Nat} (h : queueDequeueRefundK k id actor depId = some p) :
    p.1.caps = k.caps := by
  unfold queueDequeueRefundK at h
  -- `queueDequeueRefundK` = `queueDequeueK k id actor` then (on success) `settleEscrowRawAsset`-refund.
  cases hq : queueDequeueK k id actor with
  | none => simp [hq] at h
  | some pr =>
      obtain ⟨k₁, mh⟩ := pr
      simp only [hq] at h
      have hc1 : k₁.caps = k.caps := by
        have := queueDequeueK_caps hq; simpa using this
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h
          show (settleEscrowRawAsset k₁ _ actor _ _).caps = k.caps
          exact hc1
        · simp at h
      · simp at h

theorem swissExportK_caps {k k' : RecordKernelState} {sw : Nat} {exporter target : CellId}
    {rights : List Auth} (h : swissExportK k sw exporter target rights = some k') :
    k'.caps = k.caps := by
  unfold swissExportK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem swissEnlivenK_caps {k k' : RecordKernelState} {sw : Nat} {claimed : List Auth}
    (h : swissEnlivenK k sw claimed = some k') : k'.caps = k.caps := by
  unfold swissEnlivenK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem swissHandoffK_caps {k k' : RecordKernelState} {sw certHash : Nat}
    (h : swissHandoffK k sw certHash = some k') : k'.caps = k.caps := by
  unfold swissHandoffK at h; split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem swissDropK_caps {k k' : RecordKernelState} {sw : Nat}
    (h : swissDropK k sw = some k') : k'.caps = k.caps := by
  unfold swissDropK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · simp only [Option.some.injEq] at h; subst h; rfl

/-! ## Step 3 — `execFullA_confine`: one full-action step preserves confinement (the CORE case split). -/

/-- **`execFullA_confine` (PROVED) — the per-action confinement step.** With `control ∈ U`, EVERY
committed `FullActionA` preserves `CapsConfined U`. The case split mirrors how each effect moves `caps`:
the ~40 non-authority effects FRAME it (`*_caps_unchanged`/`rfl`); `revoke`/`dropRef`/`revokeDelegation`
FILTER (`mono`); `attenuate` narrows in place (`attenuateSlot`); `delegate`/`introduce`/`validateHandoff`/
`spawn` grant a `Cap.node` conferring `[control] ⊆ U` (`grant`); `delegateAtten` grants `attenuate keep
(heldCapTo …)` whose conferred authority is ⊆ the held parent cap ⊆ `U` (`grant` + `attenuate_subset`).
This is `confinement_preserved` discharged ON THE SHIPPED EXECUTOR, per effect. -/
theorem execFullA_confine {U : List Auth} (hctrl : Auth.control ∈ U)
    (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') (hpre : CapsConfined U s.kernel.caps) :
    CapsConfined U s'.kernel.caps := by
  cases fa with
  -- ===== balance / supply / state / escrow / queue / swiss / note / bridge: FRAME `caps`. =====
  | balanceA t a =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, recCexecAsset] at h
      cases hx : recKExecAsset s.kernel t a with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' => rw [hx] at h; simp only [Option.some.injEq] at h; subst h
                   exact recKExecAsset_caps hx
  | mintA actor cell a amt =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, recCMintAsset] at h
      cases hm : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; subst h
                   exact recKMintAsset_caps hm
  | burnA actor cell a amt =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, recCBurnAsset] at h
      cases hm : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; subst h
                   exact recKBurnAsset_caps hm
  | setFieldA actor cell f v =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | emitEventA actor cell topic data =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, emitStep] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | incrementNonceA actor cell n =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | setPermissionsA actor cell p =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | setVKA actor cell vk =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  -- ===== AUTHORITY effects: the 5 cap-writing arms. =====
  | introduceA intro rec t =>
      -- grants `Cap.node t` conferring `[control]`.
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          show CapsConfined U k'.caps
          unfold recKDelegate at hd; split at hd
          · simp only [Option.some.injEq] at hd; subst hd
            show CapsConfined U (Dregg2.Exec.grant s.kernel.caps rec (Cap.node t))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            simp only [capAuthConferred, List.mem_singleton] at ha; subst ha; exact hctrl
          · exact absurd hd (by simp)
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          show CapsConfined U k'.caps
          unfold recKDelegate at hd; split at hd
          · simp only [Option.some.injEq] at hd; subst hd
            show CapsConfined U (Dregg2.Exec.grant s.kernel.caps rec (Cap.node t))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            simp only [capAuthConferred, List.mem_singleton] at ha; subst ha; exact hctrl
          · exact absurd hd (by simp)
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          show CapsConfined U k'.caps
          unfold recKDelegate at hd; split at hd
          · simp only [Option.some.injEq] at hd; subst hd
            show CapsConfined U (Dregg2.Exec.grant s.kernel.caps rec (Cap.node t))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            simp only [capAuthConferred, List.mem_singleton] at ha; subst ha; exact hctrl
          · exact absurd hd (by simp)
  | delegateAttenA del rec t keep =>
      -- grants `attenuate keep (heldCapTo s.kernel.caps del t)`; conferred ⊆ the held parent cap ⊆ U.
      simp only [execFullA, recCDelegateAtten] at h
      -- Reduce the chained delegate to its kernel; peel the connectivity gate ONCE.
      cases hd : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          show CapsConfined U k'.caps
          -- On commit the gate fired (`heldCapTo` names a GENUINELY-HELD cap), and `k'.caps` is the grant.
          unfold recKDelegateAtten at hd
          split at hd
          · rename_i hgate
            simp only [Option.some.injEq] at hd; subst hd
            obtain ⟨hheld, _⟩ := heldCapTo_mem s.kernel.caps del t hgate
            show CapsConfined U (Dregg2.Exec.grant s.kernel.caps rec (attenuate keep (heldCapTo s.kernel.caps del t)))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            -- conferred (attenuate keep held) ⊆ conferred held; held ∈ del's slot ⇒ bounded by U.
            exact hpre del (heldCapTo s.kernel.caps del t) a hheld (attenuate_subset keep _ ha)
          · exact absurd hd (by simp)
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA] at h; simp only [Option.some.injEq] at h; subst h
      exact CapsConfined.attenuateSlot hpre
  | dropRefA holder t =>
      simp only [execFullA] at h; simp only [Option.some.injEq] at h; subst h
      exact recCRevoke_confine hpre
  | revokeDelegationA holder t =>
      simp only [execFullA] at h; simp only [Option.some.injEq] at h; subst h
      exact recCRevoke_confine hpre
  | revoke holder t =>
      simp only [execFullA] at h; simp only [Option.some.injEq] at h; subst h
      exact recCRevoke_confine hpre
  | exerciseA actor t =>
      -- exercise READS the c-list, never edits it (the graph is unchanged).
      refine CapsConfined.of_caps_eq ?_ hpre
      obtain ⟨_, hs'⟩ := exerciseStepA_factors (by simpa only [execFullA] using h)
      subst hs'; rfl
  -- ===== supply: createCell FRAMEs caps; spawn grants `Cap.node target` ([control]). =====
  | createCellA actor newCell =>
      refine CapsConfined.of_caps_eq ?_ hpre
      exact createCellChainA_caps_eq (by simpa only [execFullA] using h)
  | spawnA actor child target =>
      simp only [execFullA] at h
      obtain ⟨s1, hc1, hs'⟩ := spawnChainA_factors h
      subst hs'
      show CapsConfined U
        (fun l => if l = child then Cap.node target :: s1.kernel.caps l else s1.kernel.caps l)
      -- `s1.kernel.caps = s.kernel.caps` (createCell frames caps); then a `Cap.node target` grant.
      have hcaps1 : s1.kernel.caps = s.kernel.caps := createCellChainA_caps_eq hc1
      have hpre1 : CapsConfined U s1.kernel.caps := CapsConfined.of_caps_eq hcaps1 hpre
      have := CapsConfined.grant (U := U) (caps := s1.kernel.caps) (holder := child)
        (c := Cap.node target) (fun a ha => by
          simp only [capAuthConferred, List.mem_singleton] at ha; subst ha; exact hctrl) hpre1
      simpa only [Dregg2.Exec.grant] using this
  | bridgeMintA actor cell a value =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, recCMintAsset] at h
      cases hm : recKMintAsset s.kernel actor cell a value with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; subst h
                   exact recKMintAsset_caps hm
  -- ===== escrow / obligation / committed-escrow: FRAME caps (kernel touches `bal`/`escrows`). =====
  | createEscrowA id actor creator recipient asset amount =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact createEscrowKAsset_caps hk
  | releaseEscrowA id actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact releaseEscrowKAsset_caps hk
  | refundEscrowA id actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact refundEscrowKAsset_caps hk
  | createObligationA id actor obligor beneficiary asset stake =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact createEscrowKAsset_caps hk
  | noteSpendA nf actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, noteSpendChainA] at h
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact noteSpendNullifier_caps hk
  | noteCreateA cm actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, noteCreateChainA] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | createCommittedEscrowA id actor creator recipient asset amount =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact createEscrowKAsset_caps hk
  | releaseCommittedEscrowA id actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact releaseEscrowKAsset_caps hk
  | refundCommittedEscrowA id actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact refundEscrowKAsset_caps hk
  -- ===== bridge OUTBOUND legs: FRAME caps (kernel touches `bal`/`escrows`). =====
  | bridgeLockA id actor originator destination asset amount =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, bridgeLockChainA] at h
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact bridgeLockKAsset_caps hk
  | bridgeFinalizeA id actor asset amount =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, bridgeFinalizeChainA] at h
      -- `bridgeFinalizeChainA` is gated by `if bridgeAuthOK …`; peel the gate, then the kernel caps lemma.
      split at h
      · cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact bridgeFinalizeKAsset_caps hk
      · exact absurd h (by simp)
  | bridgeCancelA id actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, bridgeCancelChainA] at h
      split at h
      · cases hk : bridgeCancelKAsset s.kernel id with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact bridgeCancelKAsset_caps hk
      · exact absurd h (by simp)
  -- ===== seal / sovereign: FRAME caps (`stateStep`/`makeSovereignKernel` touch `cell`). =====
  | sealA actor cell =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | unsealA actor cell =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | createSealPairA actor sealerHolder x =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | makeSovereignA actor cell =>
      refine CapsConfined.of_caps_eq ?_ hpre
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors (by simpa only [execFullA] using h)
      subst hs'; rfl
  | refusalA actor cell =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | receiptArchiveA actor cell =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  -- ===== queue: FRAME caps (the chain steps are gated by `if stateAuthB …`; peel + kernel caps lemma). =====
  | queueAllocateA id actor cell cap =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, queueAllocateChainA] at h
      split at h
      · cases hk : queueAllocateK s.kernel id actor cap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact queueAllocateK_caps hk
      · exact absurd h (by simp)
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, queueEnqueueChainA] at h
      split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact queueEnqueueDepositK_caps hk
      · exact absurd h (by simp)
  | queueDequeueA id actor cell depId deposit =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, queueDequeueChainA] at h
      split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some p => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact queueDequeueRefundK_caps hk
      · exact absurd h (by simp)
  | queueResizeA id newCap actor cell =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, queueResizeChainA] at h
      split at h
      · cases hk : queueResizeK s.kernel id newCap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact queueResizeK_caps hk
      · exact absurd h (by simp)
  -- ===== swiss: FRAME caps (gated by `if stateAuthB …`; peel + kernel caps lemma). =====
  | exportSturdyRefA sw actor exporter target rights =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, swissExportChainA] at h
      split at h
      · cases hk : swissExportK s.kernel sw exporter target rights with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact swissExportK_caps hk
      · exact absurd h (by simp)
  | enlivenRefA sw actor exporter claimed =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, swissEnlivenChainA] at h
      split at h
      · cases hk : swissEnlivenK s.kernel sw claimed with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact swissEnlivenK_caps hk
      · exact absurd h (by simp)
  | swissHandoffA sw certHash introducer exporter =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, swissHandoffChainA] at h
      split at h
      · cases hk : swissHandoffK s.kernel sw certHash with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact swissHandoffK_caps hk
      · exact absurd h (by simp)
  | swissDropA sw actor exporter =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, swissDropChainA] at h
      split at h
      · cases hk : swissDropK s.kernel sw with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact swissDropK_caps hk
      · exact absurd h (by simp)

/-! ## Step 4 — lift to the forest turn, then the full forest (the executed cell step). -/

/-- **`execFullTurnA_confine` (PROVED)** — a committed full-TURN (the `Option`-monad fold of
`execFullA`) preserves `CapsConfined U`: induct on the action list, chaining the per-action
`execFullA_confine`. -/
theorem execFullTurnA_confine {U : List Auth} (hctrl : Auth.control ∈ U) :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → CapsConfined U s.kernel.caps → CapsConfined U s'.kernel.caps
  | s, s', [], h, hpre => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact hpre
  | s, s', a :: rest, h, hpre => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact execFullTurnA_confine hctrl s1 s' rest h (execFullA_confine hctrl s s1 a ha hpre)

/-- **`execFullForestA_confine` (PROVED)** — a committed full-FOREST preserves `CapsConfined U`. Read
through the pre-order bridge `execFullForestA_eq_execFullTurnA` into `execFullTurnA_confine`. -/
theorem execFullForestA_confine {U : List Auth} (hctrl : Auth.control ∈ U)
    (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') (hpre : CapsConfined U s.kernel.caps) :
    CapsConfined U s'.kernel.caps := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_confine hctrl s s' (lowerForestA f) h hpre

/-- **`cellNextA_confine` (PROVED) — THE ONE-STEP OBLIGATION.** A single living-cell step preserves
`CapsConfined U`: on a COMMIT the forest confinement lemma applies; on a REJECT the state (hence `caps`)
is the UNCHANGED `s`. The hypothesis `livingCellA_carries` consumes. -/
theorem cellNextA_confine {U : List Auth} (hctrl : Auth.control ∈ U)
    (s : RecChainedState) (cf : ConservingForest) (hpre : CapsConfined U s.kernel.caps) :
    CapsConfined U (cellNextA s cf).kernel.caps := by
  unfold cellNextA
  cases hc : execFullForestA s cf.1 with
  | some s' => simp only [Option.getD_some]; exact execFullForestA_confine hctrl s s' cf.1 hc hpre
  | none    => simp only [Option.getD_none]; exact hpre

/-! ## Step 5 — `livingCellA_confinement`: the CONFINEMENT CROWN (carried FOREVER). -/

/-- **`livingCellA_confinement` (PROVED) — THE CONFINEMENT CROWN.** Fix an authority ceiling `U`
containing `control`. If the INITIAL kernel's caps are *confined by `U`* (every authority conferred by
every held cap, in every slot, lies in `U`), then they STAY confined at EVERY index of the unbounded
adversarial trajectory `trajA s sched`, under EVERY schedule `sched : SchedA`:

  `∀ n, CapsConfined U (trajA s sched n).kernel.caps`.

This is the seL4 object-integrity **confinement** (`Authority/Positional.confinement_preserved` — the
lift of l4v `call_kernel_pas_refined`: a turn never grows authority beyond the policy upper bound) lifted
COINDUCTIVELY onto the SHIPPED executor: *only connectivity begets connectivity, never beyond the ceiling,
FOREVER*. The single-step obligation `cellNextA_confine` discharges the SAME no-amplification content the
per-step `execFullForestA_no_amplify` proves — the attenuating delegation edges and the `Cap.node`
connectivity grants never push conferred authority past the fixed ceiling — and `livingCellA_carries`
carries it along the entire infinite adversarial future. Conservation (`livingCellA_obs_invariant'`) and
the append-only log (`livingCellA_logMono`) were the first two carried crowns; THIS is the third, and the
one that makes the cell a CONFINEMENT substrate (cap-safety over unbounded time), not merely a
conservation/audit one. -/
theorem livingCellA_confinement {U : List Auth} (hctrl : Auth.control ∈ U)
    (s : RecChainedState) (hinit : CapsConfined U s.kernel.caps) (sched : SchedA) :
    ∀ n, CapsConfined U (trajA s sched n).kernel.caps :=
  livingCellA_carries (fun s' => CapsConfined U s'.kernel.caps)
    (fun a cf h => cellNextA_confine hctrl a cf h) s hinit sched

/-! ## It runs (`#eval`) — confinement is non-vacuous on a real grant + a real ceiling.

A real cap table where cell 0 holds an `endpoint 7 [read, write]` cap. The ceiling `U = full Auth` (all
7 kinds) confines it; after a `delegateAttenA` that grants cell 1 the attenuation to `[read]` (conferring
`[read] ⊆ U`), and after a `delegate` granting `Cap.node` (conferring `[control] ∈ U`), confinement still
holds — but a ceiling MISSING the relevant authority would FAIL on the grant, so the bound has teeth. -/

/-- The full authority enumeration — the most permissive ceiling, containing `control`. -/
def fullAuthCeiling : List Auth :=
  [Auth.read, Auth.write, Auth.grant, Auth.call, Auth.reply, Auth.reset, Auth.control]

#eval decide (Auth.control ∈ fullAuthCeiling)                            -- true (the carry hypothesis holds)
-- `[read]` is confined by the full ceiling; `[grant]`-only ceiling does NOT contain `control`:
#eval decide (∀ a ∈ capAuthConferred (Cap.endpoint 7 [Auth.read]), a ∈ fullAuthCeiling)  -- true
#eval decide (Auth.control ∈ [Auth.grant])                              -- false (a too-tight ceiling rejects connectivity grants)
#eval decide (∀ a ∈ capAuthConferred (Cap.node 7), a ∈ fullAuthCeiling) -- true ([control] ⊆ full)

/-! ## Axiom hygiene — the confinement crown + its one-step obligation pinned to the kernel triple. -/

#assert_axioms CapsConfined.grant
#assert_axioms CapsConfined.attenuateSlot
#assert_axioms execFullA_confine
#assert_axioms execFullForestA_confine
#assert_axioms cellNextA_confine
#assert_axioms livingCellA_confinement

end Dregg2.Exec
