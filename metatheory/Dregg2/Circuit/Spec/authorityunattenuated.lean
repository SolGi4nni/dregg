/-
# Dregg2.Circuit.Spec.authorityunattenuated — INDEPENDENT full-state spec + executor⟺spec for the
  AUTHORITY-UNATTENUATED effect family (`delegate` · `introduceA`).

This is the AUTHORITY-side analogue of `Dregg2/Circuit/Transfer.lean`'s `TransferSpec` /
`recKExec_iff_spec` / `recTransfer_correct`, written from scratch as an INDEPENDENT declarative
reference and proved EXACTLY met by the real executor, both ways.

## The family

The full executor `execFullA` (`TurnExecutorFull.lean`) dispatches BOTH constructors to the
SAME chained authority primitive `recCDelegate`:

    execFullA s (.delegate         del rec t) = recCDelegate s del rec t
    execFullA s (.introduceA      intro rec t) = recCDelegate s intro rec t

So the two are DEFINITIONALLY the same transition (the unattenuated held-cap copy — the Granovetter
`Introduce` skeleton). We give ONE full-state spec `DelegateSpec` (the representative) and derive the
other as a COROLLARY via the executor-arm definitional equality (`execFullA_introduceA_eq`).
(F3: `validateHandoffA` died with the seal/swiss/sturdyref verb family — the handoff is the
caps-in-slots factory pattern, `Apps/CapSlotFactory.lean`.)

## The executor primitive, unfolded (read off the CODE, `AuthTurn.lean:80` + `TurnExecutorFull.lean:229`)

`recCDelegate s del rec t`:

    match recKDelegate s.kernel del rec t with
    | some k' => some { kernel := k', log := authReceipt del :: s.log }
    | none    => none

and `recKDelegate k del rec t`:

    if (k.caps del).any (fun cap => confersEdgeTo t cap) = true then
      some { k with caps := grant k.caps rec (heldCapTo k.caps del t) }
    else none

Hence a committed `delegate`:

  * **GUARD** `(s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true`
        — the Granovetter connectivity premise: the delegator already holds a `t`-conferring cap.
        (NOTE: the live executor's gate is EXACTLY this `.any confersEdgeTo`; it does NOT additionally
        check `stateAuthB` — see `frameGaps`/notes.)
  * **TOUCHED `kernel.caps`** ← `grant s.kernel.caps rec (heldCapTo s.kernel.caps del t)`
        (`rec`'s slot gains the delegator's held `t`-cap, NON-amplifying held-copy; other slots whole).
  * **TOUCHED `log`** ← `authReceipt del :: s.log` (one authority-receipt row prepended).
  * **FRAME** every OTHER `RecordKernelState` component (all 16: `accounts cell escrows nullifiers
        revoked commitments bal queues swiss slotCaveats factories lifecycle deathCert delegate
        delegations sealedBoxes`) LITERALLY unchanged. (`caps` is the ONE touched kernel field.)

`DelegateSpec` states EXACTLY this as a `Prop`, with NO executor term in any frame clause, and
`recCDelegate_iff_spec` proves the executor meets it iff — the `→` validates `recCDelegate` against
the independent spec (a silently-mutated field would make the frame clause FAIL).
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.AuthorityUnattenuated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

/-! ## §1 — The admissibility guard (the `recKDelegate` `if`-condition, named).

The Granovetter connectivity premise the executor checks before committing a `delegate`: the
`delegator` already holds a cap conferring an edge to the target `t`. This is the EXACT condition in
`recKDelegate`'s `if` (`AuthTurn.lean:83`), extracted so the bridge's directions are clean
re-assembly. -/

/-- **`delegateGuard s del t`** — the delegator holds a `t`-conferring cap (the executor's gate). -/
def delegateGuard (s : RecChainedState) (del t : CellId) : Prop :=
  (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true

/-! ## §2 — The post-state's touched `caps` map, validated DECLARATIVELY (the `recTransfer_correct`
analogue).

`recDelegateCaps` is the EXACT post-`caps` map a committed delegate installs. We validate it
declaratively (not blindly trust the helper): the `recipient`'s slot gains the delegator's held
`t`-conferring cap on top of its prior caps, and EVERY OTHER holder's cap-slot is untouched. -/

/-- The post-`caps` map of a committed unattenuated delegate: `grant` the recipient the delegator's
held `t`-conferring cap. (Definitionally `grant s.kernel.caps rec (heldCapTo s.kernel.caps del t)`.) -/
def recDelegateCaps (caps : Caps) (del rec t : CellId) : Caps :=
  grant caps rec (heldCapTo caps del t)

/-- **`recDelegateCaps_correct`** — the post-`caps` helper validated DECLARATIVELY. The recipient's
slot gains exactly the delegator's held `t`-conferring cap (prepended to its prior caps), and every
OTHER holder's cap-slot is literally unchanged. So the spec's `caps`-clause encodes
grant ∧ caps-frame, rather than trusting `grant`. -/
theorem recDelegateCaps_correct (caps : Caps) (del rec t : CellId) :
    recDelegateCaps caps del rec t rec
        = heldCapTo caps del t :: caps rec
    ∧ (∀ h, h ≠ rec → recDelegateCaps caps del rec t h = caps h) := by
  refine ⟨?_, ?_⟩
  · simp only [recDelegateCaps, grant, if_true]
  · intro h hne
    simp only [recDelegateCaps, grant, if_neg hne]

/-! ## §3 — THE FULL-STATE DECLARATIVE SPEC (the INDEPENDENT reference).

The whole truth of a committed unattenuated delegate: the connectivity guard holds; the post-state's
`kernel.caps` is the grant; the `log` gains exactly one authority receipt for the delegator; and ALL
SIXTEEN other `RecordKernelState` components are LITERALLY unchanged. No frame clause mentions
`recCDelegate`/`recKDelegate`/`execFullA`. -/

/-- **`DelegateSpec s del rec t s'`** — the INDEPENDENT full-state semantics of a committed
unattenuated delegate. Enumerates ALL 17 kernel fields + `log`: `caps` is the granted map; `log` is
the prepended authority receipt; the other 16 kernel fields (`accounts cell escrows nullifiers
revoked commitments bal queues swiss slotCaveats factories lifecycle deathCert delegate delegations
sealedBoxes`) are unchanged. Missing any field would reintroduce a ghost. -/
def DelegateSpec (s : RecChainedState) (del rec t : CellId) (s' : RecChainedState) : Prop :=
  delegateGuard s del t
  ∧ s'.kernel.caps = recDelegateCaps s.kernel.caps del rec t
  ∧ s'.log = authReceipt del :: s.log
  -- the 16 framed kernel fields (every RecordKernelState component except `caps`):
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt
  ∧ s'.kernel.heaps = s.kernel.heaps

/-! ## §4 — EXECUTOR ⟺ SPEC (FULL state, both directions).

`recCDelegate` commits a delegate into `s'` IFF `s'` is EXACTLY the spec'd full post-state. The `→`
VALIDATES `recCDelegate` against the independent spec — all 18 components (17 kernel + log) are
checked, so had the executor silently mutated `bal`/`nullifiers`/`accounts`/… the frame clauses would
make this proof FAIL. The `←` reconstructs the committed state from the spec. -/

/-- **`recCDelegate_iff_spec` — EXECUTOR ⟺ SPEC.** The chained authority executor commits an
unattenuated delegate into `s'` iff `s'` is exactly the spec'd full post-state. -/
theorem recCDelegate_iff_spec (s : RecChainedState) (del rec t : CellId) (s' : RecChainedState) :
    recCDelegate s del rec t = some s' ↔ DelegateSpec s del rec t s' := by
  unfold recCDelegate recKDelegate DelegateSpec delegateGuard recDelegateCaps
  by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg]
    simp only [hg, true_and]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨hcaps, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
      -- reconstruct `s'` from its 18 components.
      obtain ⟨k', log'⟩ := s'
      obtain ⟨acc, cl, cp, nul, rev, com, bl, slc, fac, lc, dc, dg, dgs, dge, dgea, hp⟩ := k'
      simp only at hcaps hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      subst hcaps hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`recCDelegate_iff_guard` — commitment IFF the guard** (the existence form). `recCDelegate`
commits SOME post-state iff the Granovetter connectivity premise holds. -/
theorem recCDelegate_iff_guard (s : RecChainedState) (del rec t : CellId) :
    (∃ s', recCDelegate s del rec t = some s') ↔ delegateGuard s del t := by
  unfold recCDelegate recKDelegate delegateGuard
  by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg]
    constructor
    · intro _; exact hg
    · intro _; exact ⟨_, rfl⟩
  · rw [if_neg hg]
    constructor
    · rintro ⟨s', h⟩; exact absurd h (by simp)
    · intro h; exact absurd h hg

/-! ## §5 — EXECUTOR ⟺ SPEC, lifted to `execFullA` for BOTH family constructors.

The constructors `delegate` / `introduceA` are DEFINITIONALLY the same transition `recCDelegate`
(the executor arms below are `rfl`). So `recCDelegate_iff_spec` lifts to each verbatim — the family
shares ONE spec. -/

/-- The executor arm for `delegate` is `recCDelegate` (definitional). -/
theorem execFullA_delegate_eq (s : RecChainedState) (del rec t : CellId) :
    execFullA s (.delegate del rec t) = recCDelegate s del rec t := rfl

/-- The executor arm for `introduceA` is `recCDelegate` (definitional — the unattenuated held-cap
copy is the Granovetter introduce skeleton). -/
theorem execFullA_introduceA_eq (s : RecChainedState) (intro rec t : CellId) :
    execFullA s (.introduceA intro rec t) = recCDelegate s intro rec t := rfl

/-- **`execFullA_delegate_iff_spec` — FULL executor ⟺ SPEC for `.delegate`.** -/
theorem execFullA_delegate_iff_spec (s : RecChainedState) (del rec t : CellId)
    (s' : RecChainedState) :
    execFullA s (.delegate del rec t) = some s' ↔ DelegateSpec s del rec t s' := by
  rw [execFullA_delegate_eq]; exact recCDelegate_iff_spec s del rec t s'

/-- **`execFullA_introduceA_iff_spec` — FULL executor ⟺ SPEC for `.introduceA`** (same spec). -/
theorem execFullA_introduceA_iff_spec (s : RecChainedState) (intro rec t : CellId)
    (s' : RecChainedState) :
    execFullA s (.introduceA intro rec t) = some s' ↔ DelegateSpec s intro rec t s' := by
  rw [execFullA_introduceA_eq]; exact recCDelegate_iff_spec s intro rec t s'

/-! ## §6 — Soundness teeth (the spec is NOT vacuous).

The `→` direction of the spec already validates the executor on EVERY field. Here we exhibit the
positive content a committed delegate carries (the recipient GAINS the held cap, the
balance ledger is UNTOUCHED) and the negative content (an un-connected delegator cannot
delegate). These mirror `recDelegate_grants` / `recKDelegate_frame` but are derived from the
INDEPENDENT spec, not the executor body. -/

/-- **`delegate_grants_recipient` — POSITIVE teeth.** A committed delegate puts the
delegator's held `t`-conferring cap into the recipient's slot. Derived from the spec's `caps` clause
+ the declaratively-validated post-`caps` helper. -/
theorem delegate_grants_recipient (s : RecChainedState) (del rec t : CellId) (s' : RecChainedState)
    (h : DelegateSpec s del rec t s') :
    heldCapTo s.kernel.caps del t ∈ s'.kernel.caps rec := by
  obtain ⟨_, hcaps, _⟩ := h
  rw [hcaps, (recDelegateCaps_correct s.kernel.caps del rec t).1]
  exact List.mem_cons_self

/-- **`delegate_balance_neutral` — FRAME teeth.** A committed delegate touches NEITHER the per-asset
ledger `bal` NOR the named-`balance`-field cells: `bal` and `cell` are unchanged. So the authority
turn is conservation-NEUTRAL by the spec's frame, INDEPENDENT of any executor conservation lemma. -/
theorem delegate_balance_neutral (s : RecChainedState) (del rec t : CellId) (s' : RecChainedState)
    (h : DelegateSpec s del rec t s') :
    s'.kernel.bal = s.kernel.bal ∧ s'.kernel.cell = s.kernel.cell := by
  obtain ⟨_, _, _, _, hcell, _, _, _, hbal, _⟩ := h
  exact ⟨hbal, hcell⟩

/-- **`delegate_rejects_unconnected` — NEGATIVE teeth.** A delegator that holds NO `t`-conferring cap
CANNOT delegate: `recCDelegate` (hence every family constructor) returns `none`. The Granovetter
"only connectivity begets connectivity" premise is FAIL-CLOSED — manufacturing an edge from thin air
is rejected by construction. -/
theorem delegate_rejects_unconnected (s : RecChainedState) (del rec t : CellId)
    (hbad : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = false) :
    recCDelegate s del rec t = none := by
  unfold recCDelegate recKDelegate
  rw [if_neg (by rw [hbad]; simp)]

/-! ## §7 — Concrete #guard witnesses: a connected delegator commits; an unconnected one is rejected.

Cell 0 holds a `node 7` cap (connectivity to target 7); cell 9 holds nothing. A delegate 0→1 of 7
commits (the recipient 1 gains the held cap); an attempt by 9 is rejected (`none`). Decidable
`#guard`s (genuine `decide`, NOT `native_decide`). -/

/-- A concrete chained state: cell 0 holds a `node 7` cap; all other slots empty. -/
def sD0 : RecChainedState :=
  { kernel := { accounts := {0, 1}
                cell := fun _ => .record [("balance", .int 0)]
                caps := fun c => if c = 0 then [Cap.node 7] else [] }
    log := [] }

-- A connected delegator (0 holds the `node 7` cap) commits the delegate of target 7 to recipient 1:
#guard (execFullA sD0 (.delegate 0 1 7)).isSome  --  true
-- ...and the recipient 1's slot GAINS the held `node 7` cap (the genuine grant):
#guard ((execFullA sD0 (.delegate 0 1 7)).map (fun s' => s'.kernel.caps 1)).getD [] == [Cap.node 7]
-- ...and `introduceA` produces the SAME recipient slot (same primitive):
#guard ((execFullA sD0 (.introduceA 0 1 7)).map (fun s' => s'.kernel.caps 1)).getD [] == [Cap.node 7]

-- An UNCONNECTED delegator (9 holds nothing) is REJECTED (fail-closed):
#guard (execFullA sD0 (.delegate 9 1 7)).isNone  --  true
-- ...the guard predicate is decidably false for the unconnected delegator:
#guard ((sD0.kernel.caps 9).any (fun cap => confersEdgeTo 7 cap)) == false  --  true

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms recDelegateCaps_correct
#assert_axioms recCDelegate_iff_spec
#assert_axioms recCDelegate_iff_guard
#assert_axioms execFullA_delegate_eq
#assert_axioms execFullA_introduceA_eq
#assert_axioms execFullA_delegate_iff_spec
#assert_axioms execFullA_introduceA_iff_spec
#assert_axioms delegate_grants_recipient
#assert_axioms delegate_balance_neutral
#assert_axioms delegate_rejects_unconnected

end Dregg2.Circuit.Spec.AuthorityUnattenuated
