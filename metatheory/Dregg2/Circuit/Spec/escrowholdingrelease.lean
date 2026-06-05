/-
# Dregg2.Circuit.Spec.escrowholdingrelease — INDEPENDENT full-state spec + executor⟺spec for the
  ESCROW-HOLDING-RELEASE effect family (`releaseEscrowA` · `slashObligationA`).

This is the holding-store-SETTLE analogue of `Dregg2/Circuit/Transfer.lean`'s `TransferSpec` /
`recKExec_iff_spec` / `recTransfer_correct`, written from scratch as an INDEPENDENT declarative
reference and proved EXACTLY met by the real executor, both ways. It mirrors the sibling
`Dregg2/Circuit/Spec/authorityunattenuated.lean`'s `RecChainedState`-level discipline.

## The family

The full executor `execFullA` (`TurnExecutorFull.lean:3479`) dispatches BOTH constructors to the
SAME chained per-asset escrow-release primitive `releaseEscrowChainA`:

    execFullA s (.releaseEscrowA   id actor) = releaseEscrowChainA s id actor   -- (apply.rs:1812)
    execFullA s (.slashObligationA id actor) = releaseEscrowChainA s id actor   -- (apply.rs:1656)

`slashObligation` is dispatch-ALIASED to escrow-release: a post-deadline slash TRANSFERS the parked
stake to the BENEFICIARY (= the record's `recipient`), exactly the per-asset escrow RELEASE that
credits the recipient. The two are DEFINITIONALLY the same transition; the post-deadline §8/slash gate
is a THEOREM-LAYER carrier (the `frameGaps`/notes below record that the EXECUTED arm does NOT itself
check a deadline — it is the SAME body as `releaseEscrowA`). We give ONE full-state spec
`ReleaseEscrowSpec` (the representative) and derive the other constructor as a COROLLARY via the
executor-arm definitional equality (`execFullA_slashObligation_eq`).

## The executor primitive, unfolded (read off the CODE, `RecordKernel.lean:1505` + `:1993`)

`releaseEscrowChainA s id actor`:

    match releaseEscrowKAsset s.kernel id with
    | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
    | none    => none

and `releaseEscrowKAsset k id`:

    match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
    | some r => if r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true then
                  some (settleEscrowRawAsset k id r.recipient r.asset r.amount)
                else none
    | none   => none

with `settleEscrowRawAsset k id target asset amount`:

    { k with bal     := recBalCreditCell k.bal target asset amount
             escrows := markResolved k.escrows id }

Hence a committed `releaseEscrow`:

  * **GUARD** — there is an unresolved record `r` with `r.id = id` (`find? = some r`), AND the
        SETTLE-LIVENESS gate `r.recipient ∈ accounts ∧ cellLifecycleLive recipient` holds (crediting
        a dead/non-account would silently DESTROY value, breaking combined conservation).
  * **TOUCHED `kernel.bal`** ← `recBalCreditCell s.kernel.bal r.recipient r.asset r.amount`
        (recipient credited `+amount` at the RECORD'S asset; every other cell/asset literally fixed).
  * **TOUCHED `kernel.escrows`** ← `markResolved s.kernel.escrows id` (the first id-matching unresolved
        record flipped `resolved := true`; all others — before, after, other ids — untouched).
  * **TOUCHED `log`** ← `escrowReceiptA actor :: s.log` (one escrow-receipt clock row prepended).
  * **FRAME** every OTHER `RecordKernelState` component (the 15: `accounts cell caps nullifiers
        revoked commitments queues swiss slotCaveats factories lifecycle deathCert delegate delegations
        sealedBoxes`) LITERALLY unchanged. (`bal` and `escrows` are the two touched kernel fields.)

`ReleaseEscrowSpec` states EXACTLY this as a `Prop`, with NO executor term in any frame clause, and
`releaseEscrowChainA_iff_spec` proves the executor meets it iff — the `→` validates the executor
against the independent spec (a silently-mutated field would make the frame clause FAIL).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.EscrowHoldingRelease

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

/-! ## §1 — The admissibility guard (the two `match`/`if` conditions of `releaseEscrowKAsset`, named).

A committed escrow-release needs (1) an unresolved id-matching record present in the holding-store
(`find? = some r`), and (2) the SETTLE-LIVENESS gate on that record's `recipient` (a live account).
We extract this as a `Prop` carrying the found record `r`, so the bridge directions are a clean
re-assembly. -/

/-- The decidable `find?` predicate the kernel walks `escrows` with: an UNRESOLVED record of this id. -/
def matchesId (id : Nat) : EscrowRecord → Bool := fun r => decide (r.id = id ∧ r.resolved = false)

/-- **`releaseGuard s id r`** — the executor's admissibility for a release of escrow `id`, witnessed by
the FOUND record `r`: `r` is the first unresolved id-matching record (`find? = some r`), and its
settlement target (the `recipient`) is a LIVE account (`recipient ∈ accounts ∧ cellLifecycleLive`).
This is the EXACT conjunction of `releaseEscrowKAsset`'s `match`-arm + `if`-condition. -/
def releaseGuard (s : RecChainedState) (id : Nat) (r : EscrowRecord) : Prop :=
  s.kernel.escrows.find? (matchesId id) = some r
    ∧ r.recipient ∈ s.kernel.accounts
    ∧ cellLifecycleLive s.kernel r.recipient = true

/-! ## §2 — The post-state's touched `bal`/`escrows`, validated DECLARATIVELY (the `recTransfer_correct`
analogue).

`settleEscrowRawAsset` is the EXACT post-state body a committed release installs. We validate its two
touched fields declaratively (not blindly trust the helper): the recipient gains `+amount` at the
record's asset (every other cell/asset untouched), and the id's first unresolved record is flipped
resolved (every other record untouched). -/

/-- **`releaseEscrow_settle_correct`** — the settle helper's two touched fields validated
DECLARATIVELY. (1) The settlement target gains exactly `+amount` at `asset` while EVERY other
cell/asset entry is literally unchanged (so the credit is a genuine single-cell, single-asset move,
no cross-asset laundering); (2) marking flips the first unresolved id-matching record `resolved` and
leaves the list otherwise structurally as `markResolved`. So the spec's `bal`/`escrows` clauses
genuinely encode credit ∧ resolve ∧ frame, rather than trusting the helper. -/
theorem releaseEscrow_settle_correct (bal : CellId → AssetId → ℤ) (target : CellId) (asset : AssetId)
    (amount : ℤ) :
    recBalCreditCell bal target asset amount target asset = bal target asset + amount
    ∧ (∀ x b, ¬ (x = target ∧ b = asset) →
        recBalCreditCell bal target asset amount x b = bal x b) := by
  refine ⟨?_, ?_⟩
  · simp only [recBalCreditCell, and_self, if_pos]
  · intro x b hxb
    simp only [recBalCreditCell, if_neg hxb]

/-! ## §3 — THE FULL-STATE DECLARATIVE SPEC (the INDEPENDENT reference).

The whole truth of a committed escrow-release: the guard holds for some found record `r`; the
post-state's `kernel.bal` is the recipient-credit at `r`'s asset; `kernel.escrows` is the
mark-resolved list; the `log` gains exactly one escrow receipt for the actor; and ALL FIFTEEN other
`RecordKernelState` components are LITERALLY unchanged. No frame clause mentions the executor. -/

/-- **`ReleaseEscrowSpec s id actor s'`** — the INDEPENDENT full-state semantics of a committed
escrow-release. Existentially carries the found record `r` (the holding-store entry the release
settles), then enumerates ALL 17 kernel fields + `log`: `bal` is the recipient credit at `r.asset`;
`escrows` is `markResolved … id`; `log` is the prepended escrow receipt; the other 15 kernel fields
(`accounts cell caps nullifiers revoked commitments queues swiss slotCaveats factories lifecycle
deathCert delegate delegations sealedBoxes`) are unchanged. Missing any field would reintroduce a
ghost. -/
def ReleaseEscrowSpec (s : RecChainedState) (id : Nat) (actor : CellId) (s' : RecChainedState) :
    Prop :=
  ∃ r : EscrowRecord,
    releaseGuard s id r
    ∧ s'.kernel.bal = recBalCreditCell s.kernel.bal r.recipient r.asset r.amount
    ∧ s'.kernel.escrows = markResolved s.kernel.escrows id
    ∧ s'.log = escrowReceiptA actor :: s.log
    -- the 15 framed kernel fields (every RecordKernelState component except `bal` and `escrows`):
    ∧ s'.kernel.accounts = s.kernel.accounts
    ∧ s'.kernel.cell = s.kernel.cell
    ∧ s'.kernel.caps = s.kernel.caps
    ∧ s'.kernel.nullifiers = s.kernel.nullifiers
    ∧ s'.kernel.revoked = s.kernel.revoked
    ∧ s'.kernel.commitments = s.kernel.commitments
    ∧ s'.kernel.queues = s.kernel.queues
    ∧ s'.kernel.swiss = s.kernel.swiss
    ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
    ∧ s'.kernel.factories = s.kernel.factories
    ∧ s'.kernel.lifecycle = s.kernel.lifecycle
    ∧ s'.kernel.deathCert = s.kernel.deathCert
    ∧ s'.kernel.delegate = s.kernel.delegate
    ∧ s'.kernel.delegations = s.kernel.delegations
    ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes

/-! ## §4 — EXECUTOR ⟺ SPEC (FULL state, both directions).

`releaseEscrowChainA` commits a release into `s'` IFF `s'` is EXACTLY the spec'd full post-state. The
`→` VALIDATES the executor against the independent spec — all 18 components (17 kernel + log) are
checked, so had it silently mutated `caps`/`nullifiers`/`lifecycle`/… the frame clauses would make
this proof FAIL. The `←` reconstructs the committed state from the spec. -/

/-- **`releaseEscrowChainA_iff_spec` — EXECUTOR ⟺ SPEC.** The chained per-asset escrow-release executor
commits a release into `s'` iff `s'` is exactly the spec'd full post-state. -/
theorem releaseEscrowChainA_iff_spec (s : RecChainedState) (id : Nat) (actor : CellId)
    (s' : RecChainedState) :
    releaseEscrowChainA s id actor = some s' ↔ ReleaseEscrowSpec s id actor s' := by
  unfold releaseEscrowChainA releaseEscrowKAsset ReleaseEscrowSpec releaseGuard matchesId
         settleEscrowRawAsset
  -- split on whether an unresolved id-matching record is found. `cases hf` substitutes the value into
  -- BOTH the executor `match` AND the spec's `find?` clause; the following `simp only` iota-reduces the
  -- now-`some r`/`none` executor `match` arm.
  cases hf : s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none =>
    simp only
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨r, hfind, _⟩; exact absurd hfind (by simp)
  | some r =>
    simp only
    -- now split on the settle-liveness gate.
    by_cases hg : r.recipient ∈ s.kernel.accounts ∧ cellLifecycleLive s.kernel r.recipient = true
    · rw [if_pos hg]
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨r, ⟨rfl, hg.1, hg.2⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
               rfl, rfl, rfl, rfl, rfl⟩
      · rintro ⟨r', ⟨hfind', _, _⟩, hbal, hesc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
               h12, h13, h14, h15⟩
        -- the found record is unique: the spec's `find?` reduced to `some r`, and `hfind' : some r = some r'`.
        simp only [Option.some.injEq] at hfind'
        subst hfind'
        -- reconstruct `s'` from its 18 components.
        obtain ⟨k', log'⟩ := s'
        obtain ⟨acc, cl, cp, esc, nul, rev, com, bl, qs, sw, slc, fac, lc, dc, dg, dgs, sb⟩ := k'
        simp only at hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        subst hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        rfl
    · rw [if_neg hg]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨r', ⟨hfind', hrec, hlive⟩, _⟩
        simp only [Option.some.injEq] at hfind'
        subst hfind'
        exact absurd ⟨hrec, hlive⟩ hg

/-- **`releaseEscrowChainA_iff_guard` — commitment IFF the guard** (the existence form).
`releaseEscrowChainA` commits SOME post-state iff there is a found unresolved record whose recipient
is live. -/
theorem releaseEscrowChainA_iff_guard (s : RecChainedState) (id : Nat) (actor : CellId) :
    (∃ s', releaseEscrowChainA s id actor = some s') ↔ (∃ r, releaseGuard s id r) := by
  unfold releaseEscrowChainA releaseEscrowKAsset releaseGuard matchesId
  cases hf : s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none =>
    simp only
    constructor
    · rintro ⟨s', h⟩; exact absurd h (by simp)
    · rintro ⟨r, hfind, _⟩; exact absurd hfind (by simp)
  | some r =>
    simp only
    by_cases hg : r.recipient ∈ s.kernel.accounts ∧ cellLifecycleLive s.kernel r.recipient = true
    · rw [if_pos hg]
      constructor
      · intro _; exact ⟨r, rfl, hg.1, hg.2⟩
      · intro _; exact ⟨_, rfl⟩
    · rw [if_neg hg]
      constructor
      · rintro ⟨s', h⟩; exact absurd h (by simp)
      · rintro ⟨r', hfind', hrec, hlive⟩
        simp only [Option.some.injEq] at hfind'; subst hfind'
        exact absurd ⟨hrec, hlive⟩ hg

/-! ## §5 — EXECUTOR ⟺ SPEC, lifted to `execFullA` for BOTH family constructors.

The two constructors `releaseEscrowA` / `slashObligationA` are DEFINITIONALLY the same transition
`releaseEscrowChainA` (the executor arms below are `rfl`). So `releaseEscrowChainA_iff_spec` lifts to
each verbatim — the family shares ONE spec. -/

/-- The executor arm for `releaseEscrowA` is `releaseEscrowChainA` (definitional). -/
theorem execFullA_releaseEscrow_eq (s : RecChainedState) (id : Nat) (actor : CellId) :
    execFullA s (.releaseEscrowA id actor) = releaseEscrowChainA s id actor := rfl

/-- The executor arm for `slashObligationA` is `releaseEscrowChainA` (definitional — a post-deadline
slash CREDITS the beneficiary = the record's `recipient`, exactly the escrow-release body; the
post-deadline gate is the §8/theorem-layer carrier, see `frameGaps`/notes). -/
theorem execFullA_slashObligation_eq (s : RecChainedState) (id : Nat) (actor : CellId) :
    execFullA s (.slashObligationA id actor) = releaseEscrowChainA s id actor := rfl

/-- **`execFullA_releaseEscrow_iff_spec` — FULL executor ⟺ SPEC for `.releaseEscrowA`.** -/
theorem execFullA_releaseEscrow_iff_spec (s : RecChainedState) (id : Nat) (actor : CellId)
    (s' : RecChainedState) :
    execFullA s (.releaseEscrowA id actor) = some s' ↔ ReleaseEscrowSpec s id actor s' := by
  rw [execFullA_releaseEscrow_eq]; exact releaseEscrowChainA_iff_spec s id actor s'

/-- **`execFullA_slashObligation_iff_spec` — FULL executor ⟺ SPEC for `.slashObligationA`** (same
spec — slash is dispatch-aliased to release). -/
theorem execFullA_slashObligation_iff_spec (s : RecChainedState) (id : Nat) (actor : CellId)
    (s' : RecChainedState) :
    execFullA s (.slashObligationA id actor) = some s' ↔ ReleaseEscrowSpec s id actor s' := by
  rw [execFullA_slashObligation_eq]; exact releaseEscrowChainA_iff_spec s id actor s'

/-! ## §6 — Soundness teeth (the spec is NOT vacuous).

The `→` direction of the spec already validates the executor on EVERY field. Here we exhibit the
positive content a committed release carries (the recipient genuinely GAINS the parked value at the
record's asset; the record genuinely LEAVES the unresolved set) and the negative content (a
missing/already-resolved record cannot be released; a dead-recipient release is fail-closed). These
are derived from the INDEPENDENT spec / executor body. -/

/-- **`release_credits_recipient` — POSITIVE teeth.** A committed release genuinely credits the found
record's `recipient` by exactly `+amount` at the record's `asset`. Derived from the spec's `bal`
clause + the declaratively-validated settle helper. -/
theorem release_credits_recipient (s : RecChainedState) (id : Nat) (actor : CellId)
    (s' : RecChainedState) (h : ReleaseEscrowSpec s id actor s') :
    ∃ r, releaseGuard s id r ∧
      s'.kernel.bal r.recipient r.asset = s.kernel.bal r.recipient r.asset + r.amount := by
  obtain ⟨r, hg, hbal, _⟩ := h
  refine ⟨r, hg, ?_⟩
  rw [hbal]
  exact (releaseEscrow_settle_correct s.kernel.bal r.recipient r.asset r.amount).1

/-- **`release_balance_only_recipient_asset` — FRAME teeth (no cross-cell/asset laundering).** A
committed release leaves EVERY cell/asset `bal` entry other than `(recipient, record's asset)`
literally unchanged. So the credit is a genuine single-cell, single-asset move. -/
theorem release_balance_only_recipient_asset (s : RecChainedState) (id : Nat) (actor : CellId)
    (s' : RecChainedState) (h : ReleaseEscrowSpec s id actor s') :
    ∃ r, releaseGuard s id r ∧
      ∀ x b, ¬ (x = r.recipient ∧ b = r.asset) → s'.kernel.bal x b = s.kernel.bal x b := by
  obtain ⟨r, hg, hbal, _⟩ := h
  refine ⟨r, hg, ?_⟩
  intro x b hxb
  rw [hbal]
  exact (releaseEscrow_settle_correct s.kernel.bal r.recipient r.asset r.amount).2 x b hxb

/-- **`release_resolves_record` — FRAME teeth (the holding-store moves).** A committed release marks
the holding-store via `markResolved … id` — the record genuinely LEAVES the unresolved set. -/
theorem release_resolves_record (s : RecChainedState) (id : Nat) (actor : CellId)
    (s' : RecChainedState) (h : ReleaseEscrowSpec s id actor s') :
    s'.kernel.escrows = markResolved s.kernel.escrows id := by
  obtain ⟨_, _, _, hesc, _⟩ := h
  exact hesc

/-- **`release_caps_neutral` — FRAME teeth.** A committed release touches NEITHER the capability table
`caps` NOR the per-cell named-`balance` cells `cell`: an escrow settle is an authority-NEUTRAL,
record-field-NEUTRAL move (the value lives in the per-asset `bal` ledger + the off-ledger store). -/
theorem release_caps_neutral (s : RecChainedState) (id : Nat) (actor : CellId) (s' : RecChainedState)
    (h : ReleaseEscrowSpec s id actor s') :
    s'.kernel.caps = s.kernel.caps ∧ s'.kernel.cell = s.kernel.cell := by
  obtain ⟨_, _, _, _, _, _, hcell, hcaps, _⟩ := h
  exact ⟨hcaps, hcell⟩

/-- **`release_rejects_missing` — NEGATIVE teeth.** With NO unresolved id-matching record present
(`find? = none`), the release CANNOT commit: `releaseEscrowChainA` (hence every family constructor)
returns `none`. A missing/already-resolved escrow is FAIL-CLOSED — you cannot release value that the
holding-store does not park. -/
theorem release_rejects_missing (s : RecChainedState) (id : Nat) (actor : CellId)
    (hbad : s.kernel.escrows.find? (matchesId id) = none) :
    releaseEscrowChainA s id actor = none := by
  unfold releaseEscrowChainA releaseEscrowKAsset matchesId at *
  simp only [hbad]

/-- **`release_rejects_dead_recipient` — NEGATIVE teeth (the SETTLE-LIVENESS gate).** Even with a
present unresolved record, if its `recipient` is NOT a live account the release is FAIL-CLOSED:
`releaseEscrowChainA` returns `none`. Crediting a dead/non-account would silently DESTROY value
(breaking combined conservation) — the executor refuses by construction. -/
theorem release_rejects_dead_recipient (s : RecChainedState) (id : Nat) (actor : CellId)
    (r : EscrowRecord) (hfind : s.kernel.escrows.find? (matchesId id) = some r)
    (hbad : ¬ (r.recipient ∈ s.kernel.accounts ∧ cellLifecycleLive s.kernel r.recipient = true)) :
    releaseEscrowChainA s id actor = none := by
  unfold releaseEscrowChainA releaseEscrowKAsset matchesId at *
  simp only [hfind, if_neg hbad]

/-! ## §7 — Concrete #guard witnesses: a live-recipient unresolved escrow releases; a missing or
dead-recipient one is rejected.

State `sR0` parks one unresolved escrow (id 7, recipient cell 1 — a LIVE account, amount 30, asset 0).
A release of 7 commits: recipient 1's `bal` at asset 0 rises by 30 and the record is resolved. A
release of a NON-existent id 99 is rejected (`none`); a release whose recipient is non-account is
rejected. Decidable `#guard`s (genuine `decide`, NOT `native_decide`). -/

/-- A concrete chained state parking ONE unresolved escrow: id 7, creator 0, recipient 1 (live),
amount 30, asset 0. Cells 0 and 1 are live accounts; lifecycle defaults Live (0). -/
def sR0 : RecChainedState :=
  { kernel := { accounts := {0, 1}
                cell := fun _ => .record [("balance", .int 0)]
                caps := fun _ => []
                escrows := [{ id := 7, creator := 0, recipient := 1, amount := 30,
                              resolved := false, asset := 0 }] }
    log := [] }

-- A release of the parked escrow 7 commits (recipient 1 is a live account):
#guard (execFullA sR0 (.releaseEscrowA 7 0)).isSome  --  true
-- ...and recipient 1's per-asset `bal` at asset 0 GENUINELY rises by 30 (the parked value settles):
#guard ((execFullA sR0 (.releaseEscrowA 7 0)).map (fun s' => s'.kernel.bal 1 0)).getD 0 == 30
-- ...and `slashObligationA` produces the SAME credit (dispatch-aliased to release):
#guard ((execFullA sR0 (.slashObligationA 7 0)).map (fun s' => s'.kernel.bal 1 0)).getD 0 == 30
-- ...and the record is now resolved (it left the unresolved holding-store set):
#guard ((execFullA sR0 (.releaseEscrowA 7 0)).map
          (fun s' => (s'.kernel.escrows.head?.map (fun r => r.resolved)).getD false)).getD false
          == true

-- A release of a NON-existent escrow id 99 is REJECTED (fail-closed, no such record):
#guard (execFullA sR0 (.releaseEscrowA 99 0)).isNone  --  true

/-- A state parking an escrow whose recipient (cell 5) is NOT a live account. -/
def sRDead : RecChainedState :=
  { kernel := { accounts := {0, 1}
                cell := fun _ => .record [("balance", .int 0)]
                caps := fun _ => []
                escrows := [{ id := 7, creator := 0, recipient := 5, amount := 30,
                              resolved := false, asset := 0 }] }
    log := [] }

-- A release whose recipient is a non-account is REJECTED (the SETTLE-LIVENESS gate fails closed):
#guard (execFullA sRDead (.releaseEscrowA 7 0)).isNone  --  true

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms releaseEscrow_settle_correct
#assert_axioms releaseEscrowChainA_iff_spec
#assert_axioms releaseEscrowChainA_iff_guard
#assert_axioms execFullA_releaseEscrow_eq
#assert_axioms execFullA_slashObligation_eq
#assert_axioms execFullA_releaseEscrow_iff_spec
#assert_axioms execFullA_slashObligation_iff_spec
#assert_axioms release_credits_recipient
#assert_axioms release_balance_only_recipient_asset
#assert_axioms release_resolves_record
#assert_axioms release_caps_neutral
#assert_axioms release_rejects_missing
#assert_axioms release_rejects_dead_recipient

end Dregg2.Circuit.Spec.EscrowHoldingRelease
