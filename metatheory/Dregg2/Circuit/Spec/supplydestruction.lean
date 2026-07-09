/-
# Dregg2.Circuit.Spec.supplydestruction — INDEPENDENT full-state spec ⟺ executor for the
**supply-destruction** effect family (variant: `burnA` — W1: the RETURN-TO-WELL move).

This is a LEAF module copying the proven reference pattern of `Dregg2/Circuit/Transfer.lean`
(`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`), but applied to the per-asset SUPPLY
BURN — the only `supply-destruction` constructor of `FullActionA`. It does NOT import or extend
Transfer.lean; it stands on its own over the SAME real executor (`Exec.execFullA` →
`Exec.recCBurnAsset` → `Exec.recKBurnAsset`, `TurnExecutorFull.lean`).

## What the executor ACTUALLY does (read from CODE, `TurnExecutorFull.lean` — W1)

The dispatch arm (`execFullA`) is

    | .burnA actor cell a amt   => recCBurnAsset s actor cell a amt

and the chained burn (`recCBurnAsset`) runs the kernel burn and, on success, prepends the TRUTHFUL
return-to-well receipt `{ actor := actor, src := cell, dst := a, amt := amt }` to the log.

The kernel burn (`recKBurnAsset`) is the W1 ISSUER-MOVE with direction swapped — an ordinary
per-asset transfer `cell → a` (holder → issuer well) on the PER-ASSET ledger `bal`:

    def recKBurnAsset (k) (actor cell) (a) (amt) : Option RecordKernelState :=
      if (actor = cell ∨ mintAuthorizedB k.caps actor a = true) ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
          ∧ cell ∈ k.accounts ∧ a ∈ k.accounts ∧ cell ≠ a
      then some { k with bal := recTransferBal k.bal cell a a amt }
      else none

W1 (DREGG3 §2.2): `AssetId := CellId` — the asset IS its issuer cell; burning RETURNS value to the
issuer's negative-capable well (the well's balance rises toward zero — supply shrinks), so
`Σ_c bal c a` is EXACTLY unchanged. STAGE-3 AUTHORITY SPLIT: holder SELF-REDEEM (`actor = cell` —
reducing one's own holding) is permissionless; burning ANOTHER cell's holding stays issuer-gated
(`mintAuthorizedB actor a`, E2). The HOLDER keeps the ordinary availability gate (`amt ≤ bal cell a`
— you can only burn what you hold; only the issuer WELL waives availability).

## The spec ⟺ executor theorem (BOTH directions — the crown-jewel shape)

`BurnSpec s t s'` is the INDEPENDENT declarative full-state post-condition: the guard holds, the
post-ledger is EXACTLY `recTransferBal s.kernel.bal cell a a amt` (the return-to-well write), the
log gets the truthful receipt prepended, and EVERY OTHER kernel field is LITERALLY unchanged (the
FRAME). No frame clause mentions the executor. `recCBurnAsset_iff_spec` proves the executor meets it
EXACTLY, both ways — the `→` VALIDATES the executor against the spec (a silently-mutated field would
make the proof FAIL), the `←` reconstructs the committed state. `recBurn_ledger_correct` validates
the post-ledger helper declaratively (the analog of `recTransfer_correct`).
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.SupplyDestruction

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — The full admissibility guard the executor checks (the `recKBurnAsset` `if`).

Extracted as a `Prop` so the spec ⟺ executor proof is a clean re-assembly. This is the EXACT
conjunction in `recKBurnAsset` (W1): privileged-supply authority over the **ISSUER** `a` (E2 — the
production law's destruction face), non-negativity (no negative-burn value inflation), per-asset
availability at the HOLDER (no over-burn), holder + issuer-well liveness, and holder ≠ well. -/
def BurnGuard (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) : Prop :=
  (actor = cell ∨ mintAuthorizedB k.caps actor a = true) ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
    ∧ cell ∈ k.accounts ∧ a ∈ k.accounts ∧ cell ≠ a ∧ cellLifecycleLive k a = true

/-- The truthful burn receipt the chained executor prepends to the log: the return-to-well row
`holder cell → well a` of the burned `amt` (W1: an ordinary move, no negative-disclosure fiction). -/
def burnReceipt (actor cell : CellId) (a : AssetId) (amt : ℤ) : Turn :=
  { actor := actor, src := cell, dst := a, amt := amt }

/-! ## §2 — `recKBurnAsset` commits IFF its guard holds (the kernel side, both directions). -/

/-- The kernel burn commits IFF its admissibility guard holds; and the committed post-kernel is then
the `recTransferBal … cell a a amt` return-to-well write (other kernel fields preserved by the
record update `{ k with … }`). This pins the kernel arm so the chained spec is a clean lift. -/
theorem recKBurnAsset_iff_guard (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    (∃ k', recKBurnAsset k actor cell a amt = some k') ↔ BurnGuard k actor cell a amt := by
  unfold recKBurnAsset BurnGuard
  constructor
  · rintro ⟨k', h⟩
    by_cases hg : (actor = cell ∨ mintAuthorizedB k.caps actor a = true) ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
        ∧ cell ∈ k.accounts ∧ a ∈ k.accounts ∧ cell ≠ a ∧ cellLifecycleLive k a = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · intro hg; exact ⟨_, by rw [if_pos hg]⟩

/-! ## §3 — DECLARATIVE validation of the post-ledger helper (the `recTransfer_correct` analog).

`recTransferBal bal cell a a amt` (the return-to-well write) is the ONLY component the burn
rewrites. We validate it DECLARATIVELY: the holder's `(cell, a)` entry falls by exactly `amt`, the
issuer's well `(a, a)` rises by exactly `amt` (toward zero — supply shrinks), and EVERY OTHER
`(cell, asset)` ledger entry is literally untouched. Debit ∧ well-credit ∧ ledger-frame. -/
theorem recBurn_ledger_correct (bal : CellId → AssetId → ℤ) (cell : CellId) (a : AssetId) (amt : ℤ)
    (hne : cell ≠ a) :
    recTransferBal bal cell a a amt cell a = bal cell a - amt
    ∧ recTransferBal bal cell a a amt a a = bal a a + amt
    ∧ (∀ c b, ¬ (c = cell ∧ b = a) → ¬ (c = a ∧ b = a)
        → recTransferBal bal cell a a amt c b = bal c b) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold recTransferBal
    rw [if_pos rfl, if_pos rfl]
  · unfold recTransferBal
    rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]
  · intro c b hnc hni
    unfold recTransferBal
    rcases eq_or_ne b a with hb | hb
    · have hcc : c ≠ cell := fun h => hnc ⟨h, hb⟩
      have hci : c ≠ a := fun h => hni ⟨h, hb⟩
      rw [if_pos hb, if_neg hcc, if_neg hci]
    · rw [if_neg hb]

/-! ## §4 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor ⟺ spec.

`BurnSpec` is the COMPLETE declarative state transition of a committed `burnA`, written INDEPENDENTLY
of the executor (no `recKBurnAsset`/`recCBurnAsset` term in any frame clause). It enumerates:
  * the guard `BurnGuard` (admissibility),
  * the post-ledger `bal` (the SOLE rewritten component): exactly the return-to-well write,
  * the log: the truthful receipt prepended (the ONLY other rewritten component),
  * EVERY OTHER non-`bal` kernel field LITERALLY unchanged (the FRAME).

Missing ANY field reintroduces a ghost; all 17 kernel components (16 frozen + `bal` rewritten) plus
the `log` are enumerated. -/
def BurnSpec (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (s' : RecChainedState) : Prop :=
  BurnGuard s.kernel actor cell a amt
  -- the SOLE rewritten kernel component: the per-asset ledger moves holder → well
  ∧ s'.kernel.bal = recTransferBal s.kernel.bal cell a a amt
  -- the SOLE rewritten chained component: the truthful receipt is prepended (newest-first)
  ∧ s'.log = burnReceipt actor cell a amt :: s.log
  -- the FRAME: all 16 OTHER kernel fields LITERALLY unchanged
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt
  ∧ s'.kernel.heaps = s.kernel.heaps
  ∧ s'.kernel.nullifierRoot = s.kernel.nullifierRoot
  ∧ s'.kernel.revokedRoot = s.kernel.revokedRoot

/-- **`recCBurnAsset_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The chained record
executor commits a per-asset burn into `s'` IFF `s'` is EXACTLY the spec'd full post-state. The `→`
direction VALIDATES `recCBurnAsset` against the independent spec — all 17 kernel components + the log
are checked, so had the executor silently mutated `caps`/`nullifiers`/any frozen field the
frame clauses would make this proof FAIL; the `←` reconstructs the committed state from the spec.
This is the executor corner of the spec ⟺ executor ⟺ circuit triangle for `supply-destruction`. -/
theorem recCBurnAsset_iff_spec (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (s' : RecChainedState) :
    recCBurnAsset s actor cell a amt = some s' ↔ BurnSpec s actor cell a amt s' := by
  unfold recCBurnAsset BurnSpec
  -- expose the inner kernel burn `if`
  unfold recKBurnAsset
  by_cases hg : (actor = cell ∨ mintAuthorizedB s.kernel.caps actor a = true) ∧ 0 ≤ amt
      ∧ amt ≤ s.kernel.bal cell a ∧ cell ∈ s.kernel.accounts ∧ a ∈ s.kernel.accounts ∧ cell ≠ a
      ∧ cellLifecycleLive s.kernel a = true
  · rw [if_pos hg]
    simp only [BurnGuard]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    · rintro ⟨_, hbal, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
      -- rebuild `s'` field-by-field from the spec; destruct both records to expose components
      obtain ⟨k', log'⟩ := s'
      obtain ⟨acc, cl, cps, nul, rev, com, bl, sc, fac, lc, dc, dlg, dlgs, dge, dgea, hp, nr, rr⟩ := k'
      simp only at hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      subst hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      rfl
  · rw [if_neg hg]
    simp only [BurnGuard]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §5 — corollaries: the headline projections of the full spec (committed-form). -/

/-- **`recCBurnAsset_commits_iff_guard`** — the chained burn commits IFF the guard holds (the
admissibility-only projection of the full spec). -/
theorem recCBurnAsset_commits_iff_guard (s : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) :
    (∃ s', recCBurnAsset s actor cell a amt = some s') ↔ BurnGuard s.kernel actor cell a amt := by
  constructor
  · rintro ⟨s', h⟩; exact ((recCBurnAsset_iff_spec s actor cell a amt s').mp h).1
  · intro hg
    obtain ⟨k', hk⟩ := (recKBurnAsset_iff_guard s.kernel actor cell a amt).mpr hg
    exact ⟨_, by unfold recCBurnAsset; rw [hk]⟩

/-- **`recCBurnAsset_debits`** — a committed burn debits the holder's `(cell, a)` entry by exactly
`amt` AND credits the issuer's well `(a, a)` by exactly `amt` (W1: the value RETURNS to the well —
supply shrinks, the sum never moves). Read off the full spec + the declarative ledger validation. -/
theorem recCBurnAsset_debits {s s' : RecChainedState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recCBurnAsset s actor cell a amt = some s') :
    s'.kernel.bal cell a = s.kernel.bal cell a - amt
    ∧ s'.kernel.bal a a = s.kernel.bal a a + amt := by
  have hspec := (recCBurnAsset_iff_spec s actor cell a amt s').mp h
  have hne : cell ≠ a := hspec.1.2.2.2.2.2.1
  obtain ⟨hdeb, hwell, _⟩ := recBurn_ledger_correct s.kernel.bal cell a amt hne
  rw [hspec.2.1]
  exact ⟨hdeb, hwell⟩

/-- **`recCBurnAsset_other_ledger_untouched`** — a committed burn leaves EVERY ledger entry other
than the holder's and the well's untouched (the ledger-frame projection). -/
theorem recCBurnAsset_other_ledger_untouched {s s' : RecChainedState} {actor cell : CellId}
    {a : AssetId} {amt : ℤ} (h : recCBurnAsset s actor cell a amt = some s')
    (c : CellId) (b : AssetId) (hcb : ¬ (c = cell ∧ b = a)) (hci : ¬ (c = a ∧ b = a)) :
    s'.kernel.bal c b = s.kernel.bal c b := by
  have hspec := (recCBurnAsset_iff_spec s actor cell a amt s').mp h
  have hne : cell ≠ a := hspec.1.2.2.2.2.2.1
  rw [hspec.2.1]
  exact (recBurn_ledger_correct s.kernel.bal cell a amt hne).2.2 c b hcb hci

/-- **`recCBurnAsset_no_negative_burn`** — fail-closed: a committed burn carries `0 ≤ amt`. So no
"negative burn" can inflate the holder through this arm (it would be a mint in disguise). -/
theorem recCBurnAsset_no_negative_burn {s s' : RecChainedState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recCBurnAsset s actor cell a amt = some s') : 0 ≤ amt :=
  ((recCBurnAsset_iff_spec s actor cell a amt s').mp h).1.2.1

/-- **`recCBurnAsset_no_overburn`** — fail-closed: a committed burn carries `amt ≤ bal cell a`. So the
holder's asset-`a` entry cannot be driven negative by a burn (only the issuer WELL is
negative-capable; ordinary holders keep the availability gate). -/
theorem recCBurnAsset_no_overburn {s s' : RecChainedState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recCBurnAsset s actor cell a amt = some s') : amt ≤ s.kernel.bal cell a :=
  ((recCBurnAsset_iff_spec s actor cell a amt s').mp h).1.2.2.1

/-- **`recCBurnAsset_authorized` (Stage-3 split)** — fail-closed: a committed burn carries EITHER
holder self-redeem (`actor = cell` — reducing one's own holding, permissionless) OR privileged-supply
(`mintAuthorizedB`) authority over the **ISSUER** `a` (W1/E2). An actor that is neither the holder nor
holds the issuer capability cannot destroy another cell's supply. -/
theorem recCBurnAsset_authorized {s s' : RecChainedState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recCBurnAsset s actor cell a amt = some s') :
    actor = cell ∨ mintAuthorizedB s.kernel.caps actor a = true :=
  ((recCBurnAsset_iff_spec s actor cell a amt s').mp h).1.1

/-- **`recCBurnAsset_conserves` (the W1 punchline).** A committed burn leaves EVERY asset's total
supply EXACTLY unchanged — the holder's debit lands in the well (`recKBurnAsset_delta`). -/
theorem recCBurnAsset_conserves {s s' : RecChainedState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recCBurnAsset s actor cell a amt = some s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  unfold recCBurnAsset at h
  cases hk : recKBurnAsset s.kernel actor cell a amt with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h
      have : s'.kernel = k' := by rw [← h]
      rw [this]
      exact recKBurnAsset_delta s.kernel k' actor cell a amt hk b

/-! ## §6 — executor-dispatch form: the SAME truths through `execFullA (.burnA …)`.

`execFullA s (.burnA actor cell a amt) = recCBurnAsset s actor cell a amt` definitionally, so the
full spec ⟺ holds through the top-level dispatch unchanged — this is the `supply-destruction` arm
of `execFullA` validated against its independent spec. -/

/-- **`execFullA_burnA_iff_spec` — the dispatch-level spec ⟺ executor.** Through the top-level
`execFullA` dispatch on `.burnA`, committing the turn into `s'` is EXACTLY `BurnSpec`. -/
theorem execFullA_burnA_iff_spec (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (s' : RecChainedState) :
    execFullA s (.burnA actor cell a amt) = some s' ↔ BurnSpec s actor cell a amt s' := by
  show recCBurnAsset s actor cell a amt = some s' ↔ BurnSpec s actor cell a amt s'
  exact recCBurnAsset_iff_spec s actor cell a amt s'

/-- **`burnA_rejects_destroyed_issuer` — "Destroyed is terminal" (the lifecycle tooth).** A `burnA`
whose ISSUER well is a member account but NOT lifecycle-Live (`cellLifecycleLive caps a ≠ true` — a
Destroyed or Sealed issuer cell) is REJECTED, even with full authority/availability/membership.
Returning supply to a Destroyed well is refused at the executor (and so the spec) layer — the
property codex flagged as missing (the handler wrapper enforced it; `execFullA`/the spec did not). -/
theorem burnA_rejects_destroyed_issuer (s : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (hdead : cellLifecycleLive s.kernel a ≠ true) :
    execFullA s (.burnA actor cell a amt) = none := by
  show recCBurnAsset s actor cell a amt = none
  unfold recCBurnAsset recKBurnAsset
  rw [if_neg (by rintro ⟨_, _, _, _, _, _, h⟩; exact absurd h hdead)]

/-! ## §6b — concrete #guard non-vacuity witnesses (Destroyed-issuer burn refused).

Cell 1 is the burnable holder, cell 0 the issuer well. Actor 9 holds the `node 0` issuer cap; the
holder holds 30 of asset 0. A Live-issuer burn of 10 commits; the SAME burn over a Destroyed issuer
(member, but `lifecycle = 3`) is refused — the lifecycle is the only thing that changed. -/

/-- A pre-state: cells {0,1} members, holder cell 1 holds 30 of asset 0, actor 9 holds `node 0`. -/
def sBurn0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun a => if a = 9 then [Dregg2.Authority.Cap.node 0] else []
        bal := fun c a => if c = 1 ∧ a = 0 then 30 else 0 }
    log := [] }

/-- The same, but the issuer well (cell 0) is Destroyed (`lifecycle 0 = 3`). -/
def sBurnDead : RecChainedState :=
  { sBurn0 with kernel := { sBurn0.kernel with lifecycle := fun c => if c = 0 then 3 else 0 } }

-- A LIVE-issuer burn of 10 of asset 0 (holder 1 → well 0) COMMITS:
#guard (execFullA sBurn0 (.burnA 9 1 0 10)).isSome  --  true
-- The issuer is STILL a member account when Destroyed (membership ≠ liveness):
#guard decide (0 ∈ sBurnDead.kernel.accounts)  --  true
#guard cellLifecycleLive sBurnDead.kernel 0 == false
-- ...but the SAME burn over the Destroyed issuer is REFUSED ("Destroyed is terminal"):
#guard decide ((execFullA sBurnDead (.burnA 9 1 0 10)).isNone)  --  true

/-! ## §7 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms burnA_rejects_destroyed_issuer
#assert_axioms recKBurnAsset_iff_guard
#assert_axioms recBurn_ledger_correct
#assert_axioms recCBurnAsset_iff_spec
#assert_axioms recCBurnAsset_commits_iff_guard
#assert_axioms recCBurnAsset_debits
#assert_axioms recCBurnAsset_other_ledger_untouched
#assert_axioms recCBurnAsset_no_negative_burn
#assert_axioms recCBurnAsset_no_overburn
#assert_axioms recCBurnAsset_authorized
#assert_axioms recCBurnAsset_conserves
#assert_axioms execFullA_burnA_iff_spec

end Dregg2.Circuit.Spec.SupplyDestruction
