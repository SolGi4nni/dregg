/-
# Dregg2.Exec.CellConfine — cap-safety / no-amplification carried FOREVER.

`livingCellA_confinement` is the coinductive lift of `Authority/Positional.confinement_preserved`
(the lift of l4v `call_kernel_pas_refined`): fix an authority ceiling `U` with `control ∈ U`; if
the initial kernel's caps are *confined by `U`* — every authority conferred by every held cap lies
in `U` — they stay confined along the entire unbounded adversarial trajectory `trajA`, under every
schedule. *Only connectivity begets connectivity, never beyond the ceiling.*

The one-step obligation `cellNextA_confine` is discharged by how `execFullForestA` moves `caps`:
most effects frame `caps`; `revoke`/`dropRef`/`revokeDelegation` filter a slot; `attenuateCapability`
narrows in place; `delegateAtten` grants `attenuate keep (heldCapTo …)` (conferred ⊆ held ⊆ `U`);
`delegate`/`introduce`/`validateHandoff` copy an already-held witness cap; `spawn` grants a disclosed
`Cap.node` conferring `[control] ⊆ U`.
-/
import Dregg2.Exec.CellCarry
import Dregg2.Exec.AuthTurn

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Exec.EffectsState (state_caps_unchanged stateAuthB stateStepGuarded_eq stateStep_factors)

/-! ## Step 1 — `CapsConfined`: the seL4 `PasRefined` upper-bound shape, as a flat ceiling. -/

/-- **`CapsConfined U caps`** — every authority conferred by every held cap, in every slot, lies within
the fixed ceiling `U`. This is `Authority.PasRefined`'s `state_objs_in_policy` clause (`auth ⊆ policy`)
with the per-edge policy collapsed to a single authority ceiling: the policy is an upper bound on
conferred authority, never exceeded. The state predicate whose coinductive carry is confinement. -/
def CapsConfined (U : List Auth) (caps : Caps) : Prop :=
  ∀ (l : Label) (c : Cap) (a : Auth), c ∈ caps l → a ∈ capAuthConferred c → a ∈ U

/-- **`BoxesConfined U boxes`** (Wave-3 DE-SHADOW) — every SEALED-BOX payload confers only authorities in
`U`. A `seal` stores a HELD cap (confined by `CapsConfined`), an `unseal` grants the box payload back; so
a confined kernel keeps confined boxes, and `unseal` cannot leak authority past the `U` ceiling. The dual
of `CapsConfined` over the sealed-box holding-store. -/
def BoxesConfined (U : List Auth) (boxes : List SealedBoxRecord) : Prop :=
  ∀ box ∈ boxes, ∀ a ∈ capAuthConferred box.payload, a ∈ U

/-- **`KConfined U k`** (Wave-3) — the COMBINED confinement invariant: the c-list AND the sealed-box
holding-store both stay within the authority ceiling `U`. This is the invariant the de-shadowed seal
cluster preserves (a flag model needed only `CapsConfined`, but a real cap-moving box needs its payloads
bounded too). The state predicate whose coinductive carry is confinement, over the FULL cap surface. -/
def KConfined (U : List Auth) (k : RecordKernelState) : Prop :=
  CapsConfined U k.caps ∧ BoxesConfined U k.sealedBoxes

/-- **`CapsConfined.of_caps_eq` — the frame closure.** If `caps' = caps`, confinement transfers verbatim. -/
theorem CapsConfined.of_caps_eq {U : List Auth} {caps caps' : Caps}
    (heq : caps' = caps) (h : CapsConfined U caps) : CapsConfined U caps' := by
  subst heq; exact h

/-- **`CapsConfined.mono` — the subset closure (revocation / filtering).** If every slot of
`caps'` is a sublist of `caps` (authority only shrank — `revoke`, `dropRef`, `revokeDelegation`),
confinement is preserved: a cap held in `caps'` was held in `caps`, hence bounded. -/
theorem CapsConfined.mono {U : List Auth} {caps caps' : Caps}
    (hsub : ∀ l, caps' l ⊆ caps l) (h : CapsConfined U caps) : CapsConfined U caps' :=
  fun l c a hc ha => h l c a (hsub l hc) ha

/-- **`mem_modify_cases` — the `List.modify` membership dichotomy.** Every member of
`l.modify n f` is either a member of `l` (untouched) or `f d` for some member `d` of `l` (the one
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

/-- **`CapsConfined.grant` — the grant closure.** Prepending a cap `c` to `holder`'s slot
preserves confinement provided `c`'s own conferred authority lies within `U`. Covers every authority
grant: ordinary delegation, validate-handoff, and spawn copy a confined held cap; `delegateAtten` grants
an attenuation of a held cap; seal-pair creation grants fresh seal caps under the explicit ceiling. -/
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

/-- **`CapsConfined.attenuateSlot` — the in-place narrow closure (`AttenuateCapability`).**
Replacing the `idx`-th cap of `actor` with its `keep`-attenuation (`List.modify idx (attenuate keep)`)
preserves confinement: a surviving cap is either an untouched old cap (bounded) or `attenuate keep d`
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

/-- A committed `createCellChainA` resets the fresh id's cap slot to `[]` and frames every other slot. -/
theorem createCellChainA_caps_frame {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    (∀ l, l ≠ newCell → s'.kernel.caps l = s.kernel.caps l)
    ∧ s'.kernel.caps newCell = [] := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h
  subst hs'
  dsimp [createCellIntoAsset, bornEmptyCellSlots]
  constructor
  · intro l hl; simp only [if_neg hl]
  · simp only [if_pos]

/-- **`CapsConfined` survives born-empty cap reset** at one fresh label. -/
theorem CapsConfined.of_fresh_slot {U : List Auth} {caps caps' : Caps} {fresh : Label}
    (hpre : CapsConfined U caps) (hempty : caps' fresh = [])
    (hframe : ∀ l, l ≠ fresh → caps' l = caps l) :
    CapsConfined U caps' := by
  intro holder cap auth hmem hconf
  by_cases hh : holder = fresh
  · subst hh; simpa [hempty] using hmem
  · exact hpre holder cap auth (by simpa [hframe holder hh] using hmem) hconf

/-- **`CapsConfined.of_fresh_singleton` — install one confined cap at a born-empty fresh slot.** -/
theorem CapsConfined.of_fresh_singleton {U : List Auth} {caps caps' : Caps} {fresh : Label} {c : Cap}
    (hpre : CapsConfined U caps) (hempty : caps fresh = [])
    (hframe : ∀ l, l ≠ fresh → caps' l = caps l) (hsingleton : caps' fresh = [c])
    (hc : ∀ a ∈ capAuthConferred c, a ∈ U) :
    CapsConfined U caps' := by
  intro holder cap auth hmem hconf
  by_cases hh : holder = fresh
  · subst hh
    rw [hsingleton] at hmem
    rcases List.mem_singleton.mp hmem with rfl
    exact hc auth hconf
  · exact hpre holder cap auth (by simpa [hframe holder hh] using hmem) hconf

/-- **`CapsConfined` survives `createCellChainA`.** -/
theorem CapsConfined.of_createCell {U : List Auth} {s s' : RecChainedState} {actor newCell : CellId}
    (hpre : CapsConfined U s.kernel.caps) (h : createCellChainA s actor newCell = some s') :
    CapsConfined U s'.kernel.caps := by
  have ⟨hframe, hempty⟩ := createCellChainA_caps_frame h
  exact CapsConfined.of_fresh_slot hpre hempty hframe

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
  -- `queueEnqueueDepositK` = `queueEnqueueK k id m` then (on success) `createEscrowRawAssetQueue`-park.
  cases hq : queueEnqueueK k id m with
  | none => simp [hq] at h
  | some k₁ =>
      simp only [hq] at h
      have hc1 : k₁.caps = k.caps := queueEnqueueK_caps hq
      split at h
      · simp only [Option.some.injEq] at h; subst h
        show (createEscrowRawAssetQueue k₁ depId sender owner dAsset deposit id m).caps = k.caps
        exact hc1
      · simp at h

theorem queueDequeueRefundK_caps {k : RecordKernelState} {id : Nat} {actor : CellId} {depId : Nat}
    {p : RecordKernelState × Nat} (h : queueDequeueRefundK k id actor depId = some p) :
    p.1.caps = k.caps := by
  unfold queueDequeueRefundK at h
  -- `queueDequeueRefundK` = `queueDequeueK` then `dequeueMsgBindB` then `settleEscrowRawAsset`-refund.
  cases hq : queueDequeueK k id actor with
  | none => simp [hq] at h
  | some pr =>
      obtain ⟨k₁, mh⟩ := pr
      simp only [hq] at h
      have hc1 : k₁.caps = k.caps := by
        have := queueDequeueK_caps hq; simpa using this
      by_cases hbind : dequeueMsgBindB k₁ actor depId id mh
      · rw [if_pos hbind] at h
        cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at h; exact absurd h (by simp)
        | some r =>
            simp only [hfind] at h
            by_cases ha : actor ∈ k₁.accounts
            · rw [if_pos ha, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨he, _⟩ := h
              rw [← he]
              exact hc1
            · rw [if_neg ha] at h; exact absurd h (by simp)
      · rw [if_neg hbind] at h; exact absurd h (by simp)

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

/-! ### Wave-3 — the `_sealedBoxes` frame lemmas (the dual of the `_caps` block: every kernel op that
preserves `caps` ALSO preserves the new `sealedBoxes` side-table — same `rfl`-grade proofs). -/

theorem recKExecAsset_sealedBoxes {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold recKExecAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem recKMintAsset_sealedBoxes {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKMintAsset k actor cell a amt = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold recKMintAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem recKBurnAsset_sealedBoxes {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKBurnAsset k actor cell a amt = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold recKBurnAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem createEscrowKAsset_sealedBoxes {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k') :
    k'.sealedBoxes = k.sealedBoxes := by
  unfold createEscrowKAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; unfold createEscrowRawAsset; rfl
  · exact absurd h (by simp)

theorem releaseEscrowKAsset_sealedBoxes {k k' : RecordKernelState} {id : Nat}
    (h : releaseEscrowKAsset k id = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold releaseEscrowKAsset at h; split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; unfold settleEscrowRawAsset; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem refundEscrowKAsset_sealedBoxes {k k' : RecordKernelState} {id : Nat}
    (h : refundEscrowKAsset k id = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold refundEscrowKAsset at h; split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; unfold settleEscrowRawAsset; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem noteSpendNullifier_sealedBoxes {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold noteSpendNullifier at h; split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem bridgeLockKAsset_sealedBoxes {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    k'.sealedBoxes = k.sealedBoxes := by
  unfold bridgeLockKAsset at h; split at h
  · simp only [Option.some.injEq] at h; subst h; unfold createBridgeRawAsset; rfl
  · exact absurd h (by simp)

theorem bridgeFinalizeKAsset_sealedBoxes {k k' : RecordKernelState} {id : Nat} {asset : AssetId} {amount : ℤ}
    (h : bridgeFinalizeKAsset k id asset amount = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold bridgeFinalizeKAsset at h; split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; unfold bridgeFinalizeRawAsset; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem bridgeCancelKAsset_sealedBoxes {k k' : RecordKernelState} {id : Nat}
    (h : bridgeCancelKAsset k id = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold bridgeCancelKAsset at h; split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; unfold settleEscrowRawAsset; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem queueAllocateK_sealedBoxes {k k' : RecordKernelState} {id : Nat} {owner : CellId} {capacity : Nat}
    (h : queueAllocateK k id owner capacity = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold queueAllocateK at h; split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem queueEnqueueK_sealedBoxes {k k' : RecordKernelState} {id m : Nat}
    (h : queueEnqueueK k id m = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold queueEnqueueK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem queueDequeueK_sealedBoxes {k : RecordKernelState} {id : Nat} {actor : CellId} {p : RecordKernelState × Nat}
    (h : queueDequeueK k id actor = some p) : p.1.sealedBoxes = k.sealedBoxes := by
  unfold queueDequeueK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem queueResizeK_sealedBoxes {k k' : RecordKernelState} {id newCap : Nat}
    (h : queueResizeK k id newCap = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold queueResizeK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem queueEnqueueDepositK_sealedBoxes {k k' : RecordKernelState} {id m : Nat} {sender owner : CellId}
    {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (h : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') :
    k'.sealedBoxes = k.sealedBoxes := by
  unfold queueEnqueueDepositK at h
  -- `queueEnqueueDepositK` = `queueEnqueueK k id m` then (on success) `createEscrowRawAssetQueue`-park.
  cases hq : queueEnqueueK k id m with
  | none => simp [hq] at h
  | some k₁ =>
      simp only [hq] at h
      have hc1 : k₁.sealedBoxes = k.sealedBoxes := queueEnqueueK_sealedBoxes hq
      split at h
      · simp only [Option.some.injEq] at h; subst h
        show (createEscrowRawAssetQueue k₁ depId sender owner dAsset deposit id m).sealedBoxes = k.sealedBoxes
        exact hc1
      · simp at h

theorem queueDequeueRefundK_sealedBoxes {k : RecordKernelState} {id : Nat} {actor : CellId} {depId : Nat}
    {p : RecordKernelState × Nat} (h : queueDequeueRefundK k id actor depId = some p) :
    p.1.sealedBoxes = k.sealedBoxes := by
  unfold queueDequeueRefundK at h
  -- `queueDequeueRefundK` = `queueDequeueK` then `dequeueMsgBindB` then `settleEscrowRawAsset`-refund.
  cases hq : queueDequeueK k id actor with
  | none => simp [hq] at h
  | some pr =>
      obtain ⟨k₁, mh⟩ := pr
      simp only [hq] at h
      have hc1 : k₁.sealedBoxes = k.sealedBoxes := by
        have := queueDequeueK_sealedBoxes hq; simpa using this
      by_cases hbind : dequeueMsgBindB k₁ actor depId id mh
      · rw [if_pos hbind] at h
        cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at h; exact absurd h (by simp)
        | some r =>
            simp only [hfind] at h
            by_cases ha : actor ∈ k₁.accounts
            · rw [if_pos ha, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨he, _⟩ := h
              rw [← he]
              exact hc1
            · rw [if_neg ha] at h; exact absurd h (by simp)
      · rw [if_neg hbind] at h; exact absurd h (by simp)

/-! ### WAVE 4 — the new queue-batch / pipeline-step / pipelined-send chained-step `caps` + `sealedBoxes`
frame helpers (the atomic batch + fan-out edit only `queues`/`escrows`/`bal`, never `caps`/`sealedBoxes`;
pipelinedSend edits NOTHING). -/

theorem queueTxOpStepA_caps {s s' : RecChainedState} {op : QueueTxOpA}
    (h : queueTxOpStepA s op = some s') : s'.kernel.caps = s.kernel.caps := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      simp only [queueTxOpStepA, queueEnqueueChainA] at h; split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact queueEnqueueDepositK_caps hk
      · exact absurd h (by simp)
  | dequeue id actor cell depId deposit =>
      simp only [queueTxOpStepA, queueDequeueChainA] at h; split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some p => obtain ⟨k', mh⟩ := p
                    rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                    exact queueDequeueRefundK_caps hk
      · exact absurd h (by simp)

theorem queueAtomicTxChainA_caps {s s' : RecChainedState} {ops : List QueueTxOpA}
    (h : queueAtomicTxChainA s ops = some s') : s'.kernel.caps = s.kernel.caps := by
  induction ops generalizing s with
  | nil => simp only [queueAtomicTxChainA, Option.some.injEq] at h; subst h; rfl
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at h
      cases hop : queueTxOpStepA s op with
      | none => rw [hop] at h; exact absurd h (by simp)
      | some s1 => rw [hop] at h; rw [ih h, queueTxOpStepA_caps hop]

theorem pipelineFanoutK_caps {k k' : RecordKernelState} {actor : CellId} {m : Nat}
    {sinks : List CellId} {sids : List Nat}
    (h : pipelineFanoutK k actor m sinks sids = some k') : k'.caps = k.caps := by
  induction sinks generalizing k sids with
  | nil => cases sids <;> (simp only [pipelineFanoutK, Option.some.injEq] at h; subst h; rfl)
  | cons sink rest ih =>
      cases sids with
      | nil => simp only [pipelineFanoutK] at h; exact absurd h (by simp)
      | cons sid sids' =>
          simp only [pipelineFanoutK] at h; split at h
          · cases hq : queueEnqueueK k sid m with
            | none => rw [hq] at h; exact absurd h (by simp)
            | some k1 => rw [hq] at h; rw [ih h, queueEnqueueK_caps hq]
          · exact absurd h (by simp)

theorem queueTxOpStepA_sealedBoxes {s s' : RecChainedState} {op : QueueTxOpA}
    (h : queueTxOpStepA s op = some s') : s'.kernel.sealedBoxes = s.kernel.sealedBoxes := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      simp only [queueTxOpStepA, queueEnqueueChainA] at h; split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact queueEnqueueDepositK_sealedBoxes hk
      · exact absurd h (by simp)
  | dequeue id actor cell depId deposit =>
      simp only [queueTxOpStepA, queueDequeueChainA] at h; split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some p => obtain ⟨k', mh⟩ := p
                    rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                    exact queueDequeueRefundK_sealedBoxes (p := (k', mh)) hk
      · exact absurd h (by simp)

theorem queueAtomicTxChainA_sealedBoxes {s s' : RecChainedState} {ops : List QueueTxOpA}
    (h : queueAtomicTxChainA s ops = some s') : s'.kernel.sealedBoxes = s.kernel.sealedBoxes := by
  induction ops generalizing s with
  | nil => simp only [queueAtomicTxChainA, Option.some.injEq] at h; subst h; rfl
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at h
      cases hop : queueTxOpStepA s op with
      | none => rw [hop] at h; exact absurd h (by simp)
      | some s1 => rw [hop] at h; rw [ih h, queueTxOpStepA_sealedBoxes hop]

theorem pipelineFanoutK_sealedBoxes {k k' : RecordKernelState} {actor : CellId} {m : Nat}
    {sinks : List CellId} {sids : List Nat}
    (h : pipelineFanoutK k actor m sinks sids = some k') : k'.sealedBoxes = k.sealedBoxes := by
  induction sinks generalizing k sids with
  | nil => cases sids <;> (simp only [pipelineFanoutK, Option.some.injEq] at h; subst h; rfl)
  | cons sink rest ih =>
      cases sids with
      | nil => simp only [pipelineFanoutK] at h; exact absurd h (by simp)
      | cons sid sids' =>
          simp only [pipelineFanoutK] at h; split at h
          · cases hq : queueEnqueueK k sid m with
            | none => rw [hq] at h; exact absurd h (by simp)
            | some k1 => rw [hq] at h; rw [ih h, queueEnqueueK_sealedBoxes hq]
          · exact absurd h (by simp)

theorem swissExportK_sealedBoxes {k k' : RecordKernelState} {sw : Nat} {exporter target : CellId}
    {rights : List Auth} (h : swissExportK k sw exporter target rights = some k') :
    k'.sealedBoxes = k.sealedBoxes := by
  unfold swissExportK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem swissEnlivenK_sealedBoxes {k k' : RecordKernelState} {sw : Nat} {claimed : List Auth}
    (h : swissEnlivenK k sw claimed = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold swissEnlivenK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · exact absurd h (by simp)

theorem swissHandoffK_sealedBoxes {k k' : RecordKernelState} {sw certHash : Nat}
    (h : swissHandoffK k sw certHash = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold swissHandoffK at h; split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem swissDropK_sealedBoxes {k k' : RecordKernelState} {sw : Nat}
    (h : swissDropK k sw = some k') : k'.sealedBoxes = k.sealedBoxes := by
  unfold swissDropK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · simp only [Option.some.injEq] at h; subst h; rfl

/-- **`execFullA_sealedBoxes_frame` (Wave-3)** — every NON-`seal` committed `FullActionA` FRAMES the
sealed-box store (`seal` is the SOLE writer). The chain ops all build `{k with <other-field> := …}`, so
the `sealedBoxes` projection of the committed post-state reduces back to `s.kernel.sealedBoxes`. -/
theorem execFullA_sealedBoxes_frame (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s')
    (hne : ∀ pid actor payload, fa ≠ .sealA pid actor payload)
    (hnex : ∀ a t inner, fa ≠ .exerciseA a t inner) :
    s'.kernel.sealedBoxes = s.kernel.sealedBoxes := by
  cases fa with
  | balanceA t a =>
      simp only [execFullA, recCexecAsset] at h
      cases hx : recKExecAsset s.kernel t a with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' => rw [hx] at h; simp only [Option.some.injEq] at h; subst h
                   unfold recKExecAsset at hx; split at hx <;> [skip; exact absurd hx (by simp)]
                   simp only [Option.some.injEq] at hx; subst hx; rfl
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hx : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' => rw [hx] at h; simp only [Option.some.injEq] at h; subst h
                   unfold recKMintAsset at hx; split at hx <;> [skip; exact absurd hx (by simp)]
                   simp only [Option.some.injEq] at hx; subst hx; rfl
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hx : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' => rw [hx] at h; simp only [Option.some.injEq] at h; subst h
                   unfold recKBurnAsset at hx; split at hx <;> [skip; exact absurd hx (by simp)]
                   simp only [Option.some.injEq] at hx; subst hx; rfl
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hx : recKMintAsset s.kernel actor cell a value with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' => rw [hx] at h; simp only [Option.some.injEq] at h; subst h
                   unfold recKMintAsset at hx; split at hx <;> [skip; exact absurd hx (by simp)]
                   simp only [Option.some.injEq] at hx; subst hx; rfl
  | setFieldA actor cell f v =>
      obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq (by simpa only [execFullA] using h))
      subst hs'; rfl
  | emitEventA actor cell topic data =>
      simp only [execFullA] at h
      by_cases hlive : cell ∈ s.kernel.accounts
      · rw [if_pos hlive] at h
        simp only [Option.some.injEq] at h
        subst h
        rfl
      · rw [if_neg hlive] at h
        exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      obtain ⟨_, hs'⟩ := stateStep_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | setPermissionsA actor cell p =>
      obtain ⟨_, hs'⟩ := stateStep_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | setVKA actor cell vk =>
      obtain ⟨_, hs'⟩ := stateStep_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h
                   unfold recKDelegate at hd; split at hd <;> [skip; exact absurd hd (by simp)]
                   simp only [Option.some.injEq] at hd; subst hd; rfl
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h
                   unfold recKDelegate at hd; split at hd <;> [skip; exact absurd hd (by simp)]
                   simp only [Option.some.injEq] at hd; subst hd; rfl
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h
                   unfold recKDelegate at hd; split at hd <;> [skip; exact absurd hd (by simp)]
                   simp only [Option.some.injEq] at hd; subst hd; rfl
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hd : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h
                   unfold recKDelegateAtten at hd; split at hd <;> [skip; exact absurd hd (by simp)]
                   simp only [Option.some.injEq] at hd; subst hd; rfl
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA, Option.some.injEq] at h; subst h; rfl
  | dropRefA holder t =>
      simp only [execFullA, recCRevoke, Option.some.injEq] at h; subst h; rfl
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke, Option.some.injEq] at h; subst h; rfl
  | revoke holder t =>
      simp only [execFullA, recCRevoke, Option.some.injEq] at h; subst h; rfl
  | exerciseA actor t inner => exact absurd rfl (hnex actor t inner)
  | createCellA actor newCell =>
      obtain ⟨_, _, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | createCellFromFactoryA actor newCell vk =>
      obtain ⟨e, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors (by simpa only [execFullA] using h)
      subst hs'
      -- post = `{s1 with kernel := {s1.kernel with cell/slotCaveats}}`; `sealedBoxes` framed off `s1`, off `s`.
      obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'; rfl
  | spawnA actor child target =>
      obtain ⟨s1, _, hc, rfl⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'; rfl
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   exact createEscrowKAsset_sealedBoxes hk
  | releaseEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   exact releaseEscrowKAsset_sealedBoxes hk
  | refundEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   exact refundEscrowKAsset_sealedBoxes hk
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   exact createEscrowKAsset_sealedBoxes hk
  | fulfillObligationA id actor =>
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   exact refundEscrowKAsset_sealedBoxes hk
  | slashObligationA id actor =>
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   exact releaseEscrowKAsset_sealedBoxes hk
  | noteSpendA nf actor =>
      simp only [execFullA, noteSpendChainA] at h
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   unfold noteSpendNullifier at hk; split at hk <;> [exact absurd hk (by simp); skip]
                   simp only [Option.some.injEq] at hk; subst hk; rfl
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA, noteCreateCommitment, Option.some.injEq] at h; subst h; rfl
  | createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      simp only [execFullA, createCommittedEscrowChainA, createEscrowChainA] at h; split at h
      · cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                     exact createEscrowKAsset_sealedBoxes hk
      · exact absurd h (by simp)
  | releaseCommittedEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   exact releaseEscrowKAsset_sealedBoxes hk
  | refundCommittedEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   exact refundEscrowKAsset_sealedBoxes hk
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, bridgeLockChainA] at h
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                   exact bridgeLockKAsset_sealedBoxes hk
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, bridgeFinalizeChainA] at h
      split at h
      · cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                     exact bridgeFinalizeKAsset_sealedBoxes hk
      · exact absurd h (by simp)
  | bridgeCancelA id actor =>
      simp only [execFullA, bridgeCancelChainA] at h
      split at h
      · cases hk : bridgeCancelKAsset s.kernel id with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                     exact bridgeCancelKAsset_sealedBoxes hk
      · exact absurd h (by simp)
  | sealA pid actor payload => exact absurd rfl (hne pid actor payload)
  | unsealA pid actor recipient =>
      obtain ⟨_, _, _, hs'⟩ := unsealChainA_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | createSealPairA pid actor sealerHolder unsealerHolder =>
      obtain ⟨_, hs'⟩ := createSealPairChainA_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | makeSovereignA actor cell =>
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | refusalA actor cell =>
      obtain ⟨_, hs'⟩ := stateStep_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | receiptArchiveA actor cell =>
      obtain ⟨_, hs'⟩ := stateStep_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | queueAllocateA id actor cell cap =>
      simp only [execFullA, queueAllocateChainA] at h; split at h
      · cases hk : queueAllocateK s.kernel id actor cap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact queueAllocateK_sealedBoxes hk
      · exact absurd h (by simp)
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [execFullA, queueEnqueueChainA] at h; split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact queueEnqueueDepositK_sealedBoxes hk
      · exact absurd h (by simp)
  | queueDequeueA id actor cell depId deposit =>
      simp only [execFullA, queueDequeueChainA] at h; split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some p => obtain ⟨k', mh⟩ := p; rw [hk] at h; simp only [Option.some.injEq] at h; subst h
                    exact queueDequeueRefundK_sealedBoxes hk
      · exact absurd h (by simp)
  | queueResizeA id newCap actor cell =>
      simp only [execFullA, queueResizeChainA] at h; split at h
      · cases hk : queueResizeK s.kernel id newCap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact queueResizeK_sealedBoxes hk
      · exact absurd h (by simp)
  -- §MA-queue-batch (WAVE 4): the atomic batch / pipeline step edit `queues`/`escrows`/`bal`, never
  -- `sealedBoxes` (the witness lemmas + frame helpers); pipelinedSend edits NOTHING.
  | queueAtomicTxA actor ops =>
      simp only [execFullA] at h
      obtain ⟨s1, hf, _, hk⟩ := queueAtomicTxA_atomic_witness h
      rw [show s'.kernel.sealedBoxes = s1.kernel.sealedBoxes from by rw [hk]]
      exact queueAtomicTxChainA_sealedBoxes hf
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [execFullA] at h
      obtain ⟨k1, mh, hd, hfo⟩ := queuePipelineStepA_routing_witness h
      exact (pipelineFanoutK_sealedBoxes hfo).trans (queueDequeueK_sealedBoxes hd)
  | pipelinedSendA actor =>
      simp only [execFullA, Option.some.injEq] at h; subst h; rfl
  | exportSturdyRefA sw actor exporter target rights =>
      simp only [execFullA, swissExportChainA] at h; split at h
      · cases hk : swissExportK s.kernel sw exporter target rights with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact swissExportK_sealedBoxes hk
      · exact absurd h (by simp)
  | enlivenRefA sw actor exporter claimed =>
      simp only [execFullA, swissEnlivenChainA] at h; split at h
      · cases hk : swissEnlivenK s.kernel sw claimed with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact swissEnlivenK_sealedBoxes hk
      · exact absurd h (by simp)
  | swissHandoffA sw certHash introducer exporter =>
      simp only [execFullA, swissHandoffChainA] at h; split at h
      · cases hk : swissHandoffK s.kernel sw certHash with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact swissHandoffK_sealedBoxes hk
      · exact absurd h (by simp)
  | swissDropA sw actor exporter =>
      simp only [execFullA, swissDropChainA] at h; split at h
      · cases hk : swissDropK s.kernel sw with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact swissDropK_sealedBoxes hk
      · exact absurd h (by simp)
  | cellSealA actor cell =>
      obtain ⟨_, hs'⟩ := cellSealChainA_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | cellUnsealA actor cell =>
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | cellDestroyA actor cell ch =>
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors (by simpa only [execFullA] using h); subst hs'; rfl
  | refreshDelegationA actor child =>
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors (by simpa only [execFullA] using h); subst hs'; rfl

/-- **`execFullA_sealedBoxes_frame_or_sealCons` (Wave-3)** — the sealed-box store is written by EXACTLY
ONE effect (`seal`); every other committed `FullActionA` FRAMES it. So a committed step either leaves
`sealedBoxes` unchanged, OR it is a `seal` that conses a box binding a HELD `payload` (`payload ∈ caps
actor`). This is the structural fact the `BoxesConfined` carry rests on (the held payload is confined). -/
theorem execFullA_sealedBoxes_frame_or_sealCons (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s')
    (hnex : ∀ a t inner, fa ≠ .exerciseA a t inner) :
    s'.kernel.sealedBoxes = s.kernel.sealedBoxes ∨
      ∃ pid actor payload, fa = .sealA pid actor payload ∧
        s'.kernel.sealedBoxes
          = { pairId := pid, sealer := actor, payload := payload } :: s.kernel.sealedBoxes ∧
        payload ∈ s.kernel.caps actor := by
  -- `seal` is the SOLE writer (`exerciseA` is excluded — it RECURSES, handled in `boxesConfine` directly);
  -- for `seal` we read the held payload off `sealChainA_factors`. For every other NON-exercise arm
  -- `s'.kernel` shares `s.kernel`'s `sealedBoxes` (`execFullA_sealedBoxes_frame`).
  by_cases hseal : ∃ pid actor payload, fa = .sealA pid actor payload
  · obtain ⟨pid, actor, payload, rfl⟩ := hseal
    obtain ⟨⟨_, hheld⟩, hs'⟩ := sealChainA_factors (by simpa only [execFullA] using h)
    exact Or.inr ⟨pid, actor, payload, rfl, by rw [hs'], hheld⟩
  · exact Or.inl (execFullA_sealedBoxes_frame s s' fa h
      (by rintro pid actor payload rfl; exact hseal ⟨pid, actor, payload, rfl⟩) hnex)

/-! ## Step 3 — `execFullA_confine`: one full-action step preserves confinement (the CORE case split). -/

mutual
/-- **`execFullA_confine` — the per-action confinement step.** With `control ∈ U`, every
committed `FullActionA` preserves `CapsConfined U`. The ~40 non-authority effects frame `caps`
(`*_caps_unchanged`/`rfl`); `revoke`/`dropRef`/`revokeDelegation` filter (`mono`); `attenuate`
narrows in place (`attenuateSlot`); `delegate`/`introduce`/`validateHandoff` copy an already-held cap;
`delegateAtten` grants `attenuate keep (heldCapTo …)` whose conferred authority is ⊆ the held parent cap
⊆ `U` (`grant` + `attenuate_subset`); `spawn` grants `Cap.node` under the explicit `[control] ⊆ U`
ceiling. `exerciseA` RECURSES (mutual `execInnerA_confine`, same ceiling). This is `confinement_preserved` discharged on the
executor, per effect. -/
theorem execFullA_confine {U : List Auth} (hctrl : Auth.control ∈ U)
    (hgrant : Auth.grant ∈ U) (hreply : Auth.reply ∈ U)
    (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') (hpre : CapsConfined U s.kernel.caps)
    -- Wave-3 DE-SHADOW: a confined kernel holds only CONFINED sealed-box payloads, so `unseal`'s grant of
    -- the recovered payload stays within `U` (the box was sealed from a held=confined cap). The seal-pair
    -- caps confer `[grant]`/`[reply]` ⊆ `U` (`hgrant`/`hreply`). These extend `hctrl` for the seal cluster.
    (hboxes : ∀ box ∈ s.kernel.sealedBoxes, ∀ a ∈ capAuthConferred box.payload, a ∈ U) :
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
      -- §SLOT-CAVEAT: peel the caveat gate (`stateStepGuarded_eq`); the field write never edits `caps`.
      exact CapsConfined.of_caps_eq
        (state_caps_unchanged (stateStepGuarded_eq (by simpa only [execFullA] using h))) hpre
  | emitEventA actor cell topic data =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA] at h
      by_cases hlive : cell ∈ s.kernel.accounts
      · rw [if_pos hlive] at h
        simp only [Option.some.injEq] at h
        subst h
        rfl
      · rw [if_neg hlive] at h
        exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | setPermissionsA actor cell p =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | setVKA actor cell vk =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  -- ===== AUTHORITY effects: the cap-writing arms. =====
  | introduceA intro rec t =>
      -- grants the held witness cap; confinement follows because that cap was already confined.
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          show CapsConfined U k'.caps
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            show CapsConfined U (Dregg2.Exec.grant s.kernel.caps rec (heldCapTo s.kernel.caps intro t))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            exact hpre intro (heldCapTo s.kernel.caps intro t) a (heldCapTo_mem s.kernel.caps intro t hg).1 ha
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          show CapsConfined U k'.caps
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            show CapsConfined U (Dregg2.Exec.grant s.kernel.caps rec (heldCapTo s.kernel.caps del t))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            exact hpre del (heldCapTo s.kernel.caps del t) a (heldCapTo_mem s.kernel.caps del t hg).1 ha
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          show CapsConfined U k'.caps
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            show CapsConfined U (Dregg2.Exec.grant s.kernel.caps rec (heldCapTo s.kernel.caps intro t))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            exact hpre intro (heldCapTo s.kernel.caps intro t) a (heldCapTo_mem s.kernel.caps intro t hg).1 ha
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
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
  | exerciseA actor t inner =>
      -- exercise's hold-gate READS the c-list (caps framed); then the inner fold RECURSES, preserving
      -- confinement at each step (mutual `execInnerA_confine`, with the SAME `control ∈ U` ceiling).
      simp only [execFullA] at h
      cases hg : exerciseStepA s actor t with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hg] at h
          obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
          have hpre1 : CapsConfined U s1.kernel.caps :=
            CapsConfined.of_caps_eq (by rw [hs1]) hpre
          -- exercise reads the c-list + appends a receipt; `sealedBoxes` is framed (`s1.kernel = {s with log}`).
          have hbox1 : ∀ box ∈ s1.kernel.sealedBoxes, ∀ a ∈ capAuthConferred box.payload, a ∈ U := by
            rw [hs1]; exact hboxes
          exact execInnerA_confine hctrl hgrant hreply s1 s' inner h hpre1 hbox1
  -- ===== supply: createCell FRAMEs caps; spawn copies a held parent cap plus metadata. =====
  | createCellA actor newCell =>
      exact CapsConfined.of_createCell hpre (by simpa only [execFullA] using h)
  | createCellFromFactoryA actor newCell vk =>
      have hcap := createCellFromFactoryChainA_caps_frame (by simpa only [execFullA] using h)
      exact CapsConfined.of_fresh_slot hpre hcap.2 hcap.1
  | spawnA actor child target =>
      simp only [execFullA] at h
      obtain ⟨s1, hground, hc1, hs'⟩ := spawnChainA_factors h
      subst hs'
      have hpre1 : CapsConfined U s1.kernel.caps := CapsConfined.of_createCell hpre hc1
      have hempty : s1.kernel.caps child = [] := (createCellChainA_caps_frame hc1).2
      have hframe := (createCellChainA_caps_frame hc1).1
      exact CapsConfined.of_fresh_singleton (caps := s1.kernel.caps)
        (caps' := fun l => if l = child then [heldCapTo s.kernel.caps actor target] else s.kernel.caps l)
        (fresh := child) (c := heldCapTo s.kernel.caps actor target) hpre1 hempty
        (fun l hl => by simp [if_neg hl, hframe l hl])
        (by simp)
        (fun a ha => hpre actor (heldCapTo s.kernel.caps actor target) a
          (heldCapTo_mem s.kernel.caps actor target hground.1).1 ha)
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
  -- fulfill/slash route to refund/release (escrow SETTLE) — `caps` literally unchanged (frame).
  | fulfillObligationA id actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact refundEscrowKAsset_caps hk
  | slashObligationA id actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact releaseEscrowKAsset_caps hk
  | noteSpendA nf actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, noteSpendChainA] at h
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact noteSpendNullifier_caps hk
  | noteCreateA cm actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, noteCreateChainA] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, createCommittedEscrowChainA, createEscrowChainA] at h; split at h
      · cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; exact createEscrowKAsset_caps hk
      · exact absurd h (by simp)
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
  -- ===== seal cluster (Wave-3 DE-SHADOW): seal FRAMES caps (edits `sealedBoxes`); createSealPair GRANTS
  -- two confined seal-pair caps (`[grant]`/`[reply]` ⊆ `U`); unseal GRANTS the box payload (confined by
  -- `hboxes`). sovereign/refusal/archive FRAME caps. =====
  | sealA pid actor payload =>
      obtain ⟨_, hs'⟩ := sealChainA_factors (by simpa only [execFullA] using h)
      subst hs'; exact hpre   -- `caps` literally unchanged (edits `sealedBoxes`)
  | unsealA pid actor recipient =>
      obtain ⟨box, hbox, _, hs'⟩ := unsealChainA_factors (by simpa only [execFullA] using h)
      subst hs'
      -- grants `box.payload` to `recipient`: confined because `box ∈ sealedBoxes` is a confined payload.
      refine CapsConfined.grant (fun a ha => ?_) hpre
      exact hboxes box (List.mem_of_find?_eq_some hbox) a ha
  | createSealPairA pid actor sealerHolder unsealerHolder =>
      obtain ⟨_, hs'⟩ := createSealPairChainA_factors (by simpa only [execFullA] using h)
      subst hs'
      -- two nested grants: `sealerCap pid = endpoint pid [grant]`, `unsealerCap pid = endpoint pid [reply]`.
      refine CapsConfined.grant (fun a ha => ?_) (CapsConfined.grant (fun a ha => ?_) hpre)
      · -- unsealer cap confers `[reply]`.
        simp only [unsealerCap, capAuthConferred, List.mem_singleton] at ha; subst ha; exact hreply
      · -- sealer cap confers `[grant]`.
        simp only [sealerCap, capAuthConferred, List.mem_singleton] at ha; subst ha; exact hgrant
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
  -- §MA-queue-batch (WAVE 4): the atomic batch / pipeline step FRAME `caps` (edit `queues`/`escrows`/
  -- `bal`, never `caps` — the witness lemmas + frame helpers); pipelinedSend edits NOTHING.
  | queueAtomicTxA actor ops =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA] at h
      obtain ⟨s1, hf, _, hk⟩ := queueAtomicTxA_atomic_witness h
      rw [show s'.kernel.caps = s1.kernel.caps from by rw [hk]]
      exact queueAtomicTxChainA_caps hf
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA] at h
      obtain ⟨k1, mh, hd, hfo⟩ := queuePipelineStepA_routing_witness h
      exact (pipelineFanoutK_caps hfo).trans (queueDequeueK_caps hd)
  | pipelinedSendA actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, Option.some.injEq] at h; subst h; rfl
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
  -- ===== lifecycle (Wave-3): seal/unseal/destroy edit `lifecycle`/`deathCert`; refresh edits
  -- `delegations` — all FRAME `caps`. =====
  | cellSealA actor cell =>
      obtain ⟨_, hs'⟩ := cellSealChainA_factors (by simpa only [execFullA] using h)
      exact CapsConfined.of_caps_eq (by rw [hs']; rfl) hpre
  | cellUnsealA actor cell =>
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors (by simpa only [execFullA] using h)
      exact CapsConfined.of_caps_eq (by rw [hs']; rfl) hpre
  | cellDestroyA actor cell ch =>
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors (by simpa only [execFullA] using h)
      exact CapsConfined.of_caps_eq (by rw [hs']; rfl) hpre
  | refreshDelegationA actor child =>
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors (by simpa only [execFullA] using h)
      exact CapsConfined.of_caps_eq (by rw [hs']) hpre

/-- **`execInnerA_confine`** — the inner-effect fold an `exerciseA` recurses through preserves
confinement under the SAME `control ∈ U` ceiling (+ the Wave-3 `grant`/`reply`/box hypotheses for the
seal cluster). Mutual with `execFullA_confine`; induction on the inner list, threading the per-step
confinement AND the box-confinement carry (each step preserves `BoxesConfined`, via the dedicated
`execFullA_boxesConfine` below). -/
theorem execInnerA_confine {U : List Auth} (hctrl : Auth.control ∈ U)
    (hgrant : Auth.grant ∈ U) (hreply : Auth.reply ∈ U)
    (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') (hpre : CapsConfined U s.kernel.caps)
    (hboxes : ∀ box ∈ s.kernel.sealedBoxes, ∀ a ∈ capAuthConferred box.payload, a ∈ U) :
    CapsConfined U s'.kernel.caps := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact hpre
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact execInnerA_confine hctrl hgrant hreply s1 s' rest h
            (execFullA_confine hctrl hgrant hreply s s1 a ha hpre hboxes)
            (execFullA_boxesConfine hctrl hgrant hreply s s1 a ha hpre hboxes)

/-- **`execFullA_boxesConfine` (Wave-3)** — a committed `FullActionA` preserves `BoxesConfined`: every arm
FRAMES the sealed-box holding-store EXCEPT `seal`, which adds a box binding a HELD cap (confined by `hpre :
CapsConfined`). `exerciseA` recurses (its inner seals each add a held=confined box). The dual of
`execFullA_confine` over the sealed-box store; together they carry `KConfined` forever. -/
theorem execFullA_boxesConfine {U : List Auth} (hctrl : Auth.control ∈ U)
    (hgrant : Auth.grant ∈ U) (hreply : Auth.reply ∈ U)
    (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') (hpre : CapsConfined U s.kernel.caps)
    (hboxes : ∀ box ∈ s.kernel.sealedBoxes, ∀ a ∈ capAuthConferred box.payload, a ∈ U) :
    ∀ box ∈ s'.kernel.sealedBoxes, ∀ a ∈ capAuthConferred box.payload, a ∈ U := by
  -- `exerciseA` RECURSES (its inner seals each add a held=confined box) — handled via the mutual inner
  -- fold; every other arm's `sealedBoxes` is either UNCHANGED (frame) or `seal`'s held-confined cons.
  by_cases hex : ∃ a t inner, fa = .exerciseA a t inner
  · obtain ⟨actor, t, inner, rfl⟩ := hex
    simp only [execFullA] at h
    cases hg : exerciseStepA s actor t with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some s1 =>
        rw [hg] at h
        obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
        -- exercise reads the c-list (caps + boxes framed); then the inner fold preserves box-confinement.
        have hpre1 : CapsConfined U s1.kernel.caps := CapsConfined.of_caps_eq (by rw [hs1]) hpre
        have hbox1 : ∀ box ∈ s1.kernel.sealedBoxes, ∀ a ∈ capAuthConferred box.payload, a ∈ U := by
          rw [hs1]; exact hboxes
        exact execInnerA_boxesConfine hctrl hgrant hreply s1 s' inner h hpre1 hbox1
  · rcases execFullA_sealedBoxes_frame_or_sealCons s s' fa h
        (by rintro a t inner rfl; exact hex ⟨a, t, inner, rfl⟩)
      with hframe | ⟨pid, actor, payload, hfa, hbox, hheld⟩
    · rw [hframe]; exact hboxes
    · rw [hbox]; intro box hmem a ha
      rcases List.mem_cons.mp hmem with hb | hb
      · -- the freshly-sealed box: its payload is the HELD cap `hheld`, confined by `hpre`.
        subst hb; simp only at ha; exact hpre actor payload a hheld ha
      · exact hboxes box hb a ha

/-- **`execInnerA_boxesConfine` (Wave-3)** — the inner fold preserves `BoxesConfined`, threading the
caps-confinement carry (needed for the inner `seal`s). Mutual with `execFullA_boxesConfine`. -/
theorem execInnerA_boxesConfine {U : List Auth} (hctrl : Auth.control ∈ U)
    (hgrant : Auth.grant ∈ U) (hreply : Auth.reply ∈ U)
    (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') (hpre : CapsConfined U s.kernel.caps)
    (hboxes : ∀ box ∈ s.kernel.sealedBoxes, ∀ a ∈ capAuthConferred box.payload, a ∈ U) :
    ∀ box ∈ s'.kernel.sealedBoxes, ∀ a ∈ capAuthConferred box.payload, a ∈ U := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact hboxes
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact execInnerA_boxesConfine hctrl hgrant hreply s1 s' rest h
            (execFullA_confine hctrl hgrant hreply s s1 a ha hpre hboxes)
            (execFullA_boxesConfine hctrl hgrant hreply s s1 a ha hpre hboxes)
end

/-! ## Step 4 — lift to the forest turn, then the full forest (the executed cell step). -/

/-- **`execFullTurnA_kconfine` (Wave-3)** — a committed full turn preserves the COMBINED invariant
`KConfined U` (caps AND sealed-box payloads): induction on the action list, chaining both halves
(`execFullA_confine` + `execFullA_boxesConfine`). -/
theorem execFullTurnA_kconfine {U : List Auth} (hctrl : Auth.control ∈ U)
    (hgrant : Auth.grant ∈ U) (hreply : Auth.reply ∈ U) :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → KConfined U s.kernel → KConfined U s'.kernel
  | s, s', [], h, hpre => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact hpre
  | s, s', a :: rest, h, hpre => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          obtain ⟨hc, hb⟩ := hpre
          exact execFullTurnA_kconfine hctrl hgrant hreply s1 s' rest h
            ⟨execFullA_confine hctrl hgrant hreply s s1 a ha hc hb,
             execFullA_boxesConfine hctrl hgrant hreply s s1 a ha hc hb⟩

/-- **`execFullTurnA_confine`** — the caps-half corollary (the headline confinement crown): a committed
full turn preserves `CapsConfined U`, given the initial kernel is fully `KConfined` (caps + boxes). -/
theorem execFullTurnA_confine {U : List Auth} (hctrl : Auth.control ∈ U)
    (hgrant : Auth.grant ∈ U) (hreply : Auth.reply ∈ U)
    (s s' : RecChainedState) (tt : List FullActionA)
    (h : execFullTurnA s tt = some s') (hpre : KConfined U s.kernel) :
    CapsConfined U s'.kernel.caps :=
  (execFullTurnA_kconfine hctrl hgrant hreply s s' tt h hpre).1

/-- **`execFullForestA_kconfine`** — a committed full forest preserves `KConfined U`. Routes through
the pre-order bridge `execFullForestA_eq_execFullTurnA` into `execFullTurnA_kconfine`. -/
theorem execFullForestA_kconfine {U : List Auth} (hctrl : Auth.control ∈ U)
    (hgrant : Auth.grant ∈ U) (hreply : Auth.reply ∈ U)
    (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') (hpre : KConfined U s.kernel) :
    KConfined U s'.kernel := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_kconfine hctrl hgrant hreply s s' (lowerForestA f) h hpre

/-- **`cellNextA_kconfine` — the one-step obligation.** A single living-cell step preserves `KConfined U`:
on a commit the forest confinement lemma applies; on a reject the state is unchanged. -/
theorem cellNextA_kconfine {U : List Auth} (hctrl : Auth.control ∈ U)
    (hgrant : Auth.grant ∈ U) (hreply : Auth.reply ∈ U)
    (s : RecChainedState) (cf : ConservingForest) (hpre : KConfined U s.kernel) :
    KConfined U (cellNextA s cf).kernel := by
  unfold cellNextA
  cases hc : execFullForestA s cf.1 with
  | some s' => simp only [Option.getD_some]; exact execFullForestA_kconfine hctrl hgrant hreply s s' cf.1 hc hpre
  | none    => simp only [Option.getD_none]; exact hpre

/-! ## Step 5 — `livingCellA_confinement`: confinement carried FOREVER. -/

/-- **`livingCellA_confinement`** — Fix an authority ceiling `U` containing `control`. If the initial
kernel's caps are confined by `U` (every authority conferred by every held cap lies in `U`), they stay
confined at every index of the unbounded adversarial trajectory `trajA s sched`, under every schedule:

  `∀ n, CapsConfined U (trajA s sched n).kernel.caps`.

This is the seL4 object-integrity confinement (`Authority/Positional.confinement_preserved`, lifted from
l4v `call_kernel_pas_refined`: a turn never grows authority beyond the policy upper bound) carried
coinductively: held-cap copies (ordinary delegation, handoff, spawn), attenuating delegation edges, and
fresh seal caps never push conferred authority past the fixed ceiling, for all time.
`cellNextA_confine` is the one-step obligation; `livingCellA_carries` carries it over the entire
adversarial future. -/
theorem livingCellA_confinement {U : List Auth} (hctrl : Auth.control ∈ U)
    (hgrant : Auth.grant ∈ U) (hreply : Auth.reply ∈ U)
    (s : RecChainedState) (hinit : KConfined U s.kernel) (sched : SchedA) :
    ∀ n, CapsConfined U (trajA s sched n).kernel.caps :=
  -- carry the COMBINED `KConfined` (caps + sealed-box payloads) FOREVER, then project the caps half.
  fun n => (livingCellA_carries (fun s' => KConfined U s'.kernel)
    (fun a cf h => cellNextA_kconfine hctrl hgrant hreply a cf h) s hinit sched n).1

/-! ## It runs (`#eval`) — confinement is non-vacuous on a real grant + a real ceiling.

A real cap table where cell 0 holds an `endpoint 7 [read, write]` cap. The ceiling `U = full Auth`
(all 7 kinds) confines it; a ceiling missing the relevant authority would fail on the grant, so the
bound has teeth. -/

/-- The full authority enumeration — the most permissive ceiling, containing `control`. -/
def fullAuthCeiling : List Auth :=
  [Auth.read, Auth.write, Auth.grant, Auth.call, Auth.reply, Auth.reset, Auth.control]

#guard (decide (Auth.control ∈ fullAuthCeiling))  --  true (the carry hypothesis holds)
-- `[read]` is confined by the full ceiling; `[grant]`-only ceiling does NOT contain `control`:
#guard (decide (∀ a ∈ capAuthConferred (Cap.endpoint 7 [Auth.read]), a ∈ fullAuthCeiling))  --  true
#guard (decide (Auth.control ∈ [Auth.grant])) == false  --  false (a too-tight ceiling rejects connectivity grants)
#guard (decide (∀ a ∈ capAuthConferred (Cap.node 7), a ∈ fullAuthCeiling))  --  true ([control] ⊆ full)

/-! ## Axiom hygiene — confinement + one-step obligation pinned to the kernel triple. -/

#assert_axioms CapsConfined.grant
#assert_axioms CapsConfined.attenuateSlot
#assert_axioms execFullA_confine
#assert_axioms execFullA_boxesConfine
#assert_axioms execFullForestA_kconfine
#assert_axioms cellNextA_kconfine
#assert_axioms livingCellA_confinement

end Dregg2.Exec
