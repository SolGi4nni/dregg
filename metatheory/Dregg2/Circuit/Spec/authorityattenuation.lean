/-
# Dregg2.Circuit.Spec.authorityattenuation — INDEPENDENT full-state spec + executor⟺spec for the
  dregg2 authority-attenuation effect family (`delegateAttenA`, `attenuateA`).

This leaf module is the `Transfer.lean` reference pattern (`TransferSpec` + `recKExec_iff_spec` +
`recTransfer_correct`) carried to the TWO authority-attenuation arms of `execFullA`:

  * `delegateAttenA del rec t keep` ⟶ `recCDelegateAtten s del rec t keep`
      — the RIGHTS-CARRYING Granovetter delegation (the faithful `apply_introduce`,
        `is_attenuation(held, granted)`): GATED on `del` already holding a cap that confers a
        connectivity edge to `t`; on commit it grants `rec` the delegator's held cap to `t`
        ATTENUATED to `keep` (real conferred rights `⊆` held — `recKDelegateAtten_non_amplifying`),
        and prepends an authority receipt to the log. Fail-closed (no held edge ⇒ `none`).
  * `attenuateA actor idx keep` ⟶ `some (attenuateStepA s actor idx keep)`
      — the in-place self-narrowing of `actor`'s `idx`-th held cap to `keep` (`apply.rs:4377`).
        TOTAL: it ALWAYS commits (at worst the identity, still narrower-or-equal); it edits only the
        `caps` slot of `actor` and prepends an authority receipt.

For EACH variant we state an INDEPENDENT declarative full-state spec — the admissibility guard
(only `delegateAttenA` has one) ∧ the EXACT post-state on the touched components (`kernel.caps` +
`log`) ∧ EVERY OTHER `RecChainedState` field LITERALLY unchanged (the FRAME). `RecChainedState` has
TWO fields: `kernel : RecordKernelState` and `log : List Turn`. The kernel has SEVENTEEN fields —
`accounts cell caps escrows nullifiers revoked commitments bal queues swiss slotCaveats factories
lifecycle deathCert delegate delegations sealedBoxes` — so the FRAME enumerates the SIXTEEN non-`caps`
kernel fields plus the kernel↔kernel `caps` rewrite, plus the `log` head-cons. NO frame clause names
the executor (`execFullA`/`recCDelegateAtten`/`attenuateStepA`/`recKDelegateAtten`); the post-`caps`
clauses use only the PURE cap helpers (`grant`/`attenuate`/`heldCapTo`/`attenuateSlotF`), so the spec
is genuinely independent of the executor it validates.

The `→` direction of each `…_iff_spec` VALIDATES the executor against the independent spec: all 17
kernel fields + the log are checked, so had the arm silently mutated `bal`/`nullifiers`/`revoked`/…
a frame clause would make the proof FAIL. (None do — see `frameGaps = []` in the run report.)

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.AuthorityAttenuation

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth Label)

/-! ## §1 — `delegateAttenA`: the gated rights-carrying Granovetter delegation.

`execFullA s (.delegateAttenA del rec t keep) = recCDelegateAtten s del rec t keep`, which is

    match recKDelegateAtten s.kernel del rec t keep with
    | some k' => some { kernel := k', log := authReceipt del :: s.log }
    | none    => none

and `recKDelegateAtten k del rec t keep` commits IFF `del` holds a cap conferring an edge to `t`,
rewriting ONLY `k.caps` (to `grant k.caps rec (attenuate keep (heldCapTo k.caps del t))`). -/

/-- **The admissibility guard `delegateAttenA` checks**, as a `Prop`: the delegator `del` already
holds a cap conferring a connectivity edge to `t` (the Granovetter "only connectivity begets
connectivity" premise / `Spec.Endow.holds_source`). Stated INDEPENDENTLY (over the pre-state's
`caps`), NOT by referencing the executor. -/
def DelegateAttenGuard (s : RecChainedState) (del t : CellId) : Prop :=
  (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true

/-- **`delegateAttenCaps_correct`** — the cap-update helper validated DECLARATIVELY (the `recTransfer_correct`
analog). On commit, `delegateAttenA` rewrites the cap table to `grant caps rec (attenuate keep
(heldCapTo caps del t))`. This lemma pins what that pure update DOES:
  (a) the recipient `rec`'s slot GAINS the attenuated held cap (`attenuate keep (heldCapTo …)`);
  (b) the attenuated cap's REAL conferred rights are `⊆` the held cap's (genuine non-amplification,
      `is_attenuation(held, granted)`, NOT a `()≤()` collapse);
  (c) every OTHER holder's slot is LITERALLY untouched.
So the spec's `s'.kernel.caps = grant …` clause genuinely encodes grant ∧ attenuation ∧ slot-frame,
rather than blindly trusting the helper. -/
theorem delegateAttenCaps_correct (caps : Caps) (del rec t : CellId) (keep : List Auth) :
    (attenuate keep (heldCapTo caps del t)
        ∈ grant caps rec (attenuate keep (heldCapTo caps del t)) rec)
    ∧ confRights (attenuate keep (heldCapTo caps del t)) ≤ confRights (heldCapTo caps del t)
    ∧ (∀ h, h ≠ rec →
        grant caps rec (attenuate keep (heldCapTo caps del t)) h = caps h) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the granted cap is prepended onto `rec`'s slot.
    unfold grant; rw [if_pos rfl]; exact List.mem_cons_self
  · -- genuine `granted ⊆ held` over the `ExecAuth` rights lattice.
    exact attenuate_confRights_le keep (heldCapTo caps del t)
  · -- a non-recipient slot is unchanged by `grant`.
    intro h hh; simp only [grant, if_neg hh]

/-- **The full-state declarative spec of a committed `delegateAttenA`** — the INDEPENDENT reference
semantics. The guard holds; the post-state's `kernel.caps` is the attenuated grant (see
`delegateAttenCaps_correct`); the log gains exactly the authority receipt; and every one of the
SIXTEEN non-`caps` kernel fields is unchanged. No frame clause mentions the executor. -/
def DelegateAttenSpec (s : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (s' : RecChainedState) : Prop :=
  DelegateAttenGuard s del t
  ∧ s'.kernel.caps = grant s.kernel.caps rec (attenuate keep (heldCapTo s.kernel.caps del t))
  ∧ s'.log = authReceipt del :: s.log
  -- THE FRAME: the sixteen non-`caps` kernel fields, all LITERALLY unchanged.
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.escrows = s.kernel.escrows
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.queues = s.kernel.queues
  ∧ s'.kernel.swiss = s.kernel.swiss
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes

/-- **`delegateAtten_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The full executor
`execFullA` commits a `delegateAttenA del rec t keep` into `s'` IFF `s'` is EXACTLY the spec'd full
post-state. The `→` direction VALIDATES the arm against the independent spec — all 17 kernel fields +
the log are checked, so had the arm silently mutated any of them the corresponding frame clause would
make this proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem delegateAtten_iff_spec (s : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (s' : RecChainedState) :
    execFullA s (.delegateAttenA del rec t keep) = some s'
      ↔ DelegateAttenSpec s del rec t keep s' := by
  unfold DelegateAttenSpec DelegateAttenGuard
  simp only [execFullA, recCDelegateAtten, recKDelegateAtten]
  by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hcaps, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
      -- reconstruct `s'` from its (kernel field-by-field) + log spec.
      obtain ⟨k', log'⟩ := s'
      obtain ⟨acc, cell, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
      simp only at hcaps hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      subst hcaps hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §2 — `attenuateA`: the TOTAL in-place self-narrowing.

`execFullA s (.attenuateA actor idx keep) = some (attenuateStepA s actor idx keep)`, with

    attenuateStepA s actor idx keep
      = { kernel := { s.kernel with caps := attenuateSlotF s.kernel.caps actor idx keep },
          log := authReceipt actor :: s.log }

There is NO admissibility guard — the arm ALWAYS commits (attenuation cannot fail: `List.modify` is a
no-op when `idx` is out of bounds, and `attenuate` only narrows). So the spec is UNCONDITIONAL. -/

/-- **`attenuateCaps_correct`** — the in-place narrowing helper validated DECLARATIVELY. On commit,
`attenuateA` rewrites the cap table to `attenuateSlotF caps actor idx keep`, which replaces the
`idx`-th cap of `actor` with its `keep`-attenuation and LEAVES EVERY OTHER HOLDER'S slot untouched.
(The per-cap non-amplification — the attenuated `idx`-th cap confers `⊆` rights — is the
already-proven `attenuate_confRights_le`; here we pin the SLOT-FRAME, the spec's load-bearing claim.) -/
theorem attenuateCaps_correct (caps : Caps) (actor : CellId) (idx : Nat) (keep : List Auth) :
    (∀ h, h ≠ actor → attenuateSlotF caps actor idx keep h = caps h)
    ∧ attenuateSlotF caps actor idx keep actor = (caps actor).modify idx (attenuate keep) := by
  refine ⟨?_, ?_⟩
  · intro h hh; simp only [attenuateSlotF, if_neg hh]
  · unfold attenuateSlotF; rw [if_pos rfl]

/-- **The full-state declarative spec of an `attenuateA`** — the INDEPENDENT reference semantics. NO
guard (always commits). The post-state's `kernel.caps` is the in-place slot narrowing (see
`attenuateCaps_correct`); the log gains the authority receipt; and every one of the SIXTEEN non-`caps`
kernel fields is unchanged. No frame clause mentions the executor. -/
def AttenuateSpec (s : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (s' : RecChainedState) : Prop :=
  s'.kernel.caps = attenuateSlotF s.kernel.caps actor idx keep
  ∧ s'.log = authReceipt actor :: s.log
  -- THE FRAME: the sixteen non-`caps` kernel fields, all LITERALLY unchanged.
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.escrows = s.kernel.escrows
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.queues = s.kernel.queues
  ∧ s'.kernel.swiss = s.kernel.swiss
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes

/-- **`attenuate_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** `execFullA` commits an
`attenuateA actor idx keep` (always — it is a TOTAL `some …` arm) into `s'` IFF `s'` is EXACTLY the
spec'd full post-state. The `→` direction VALIDATES the arm against the independent spec — all 17
kernel fields + the log are checked, so any silent mutation of an off-`caps` field would make a frame
clause FAIL; the `←` reconstructs the committed state from the spec. -/
theorem attenuate_iff_spec (s : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (s' : RecChainedState) :
    execFullA s (.attenuateA actor idx keep) = some s'
      ↔ AttenuateSpec s actor idx keep s' := by
  unfold AttenuateSpec
  simp only [execFullA, attenuateStepA, Option.some.injEq]
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨hcaps, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
    obtain ⟨k', log'⟩ := s'
    obtain ⟨acc, cell, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
    simp only at hcaps hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    subst hcaps hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    rfl

/-! ## §3 — corollaries: the headline NON-AMPLIFICATION facts read off the spec.

The whole point of the attenuation family is that authority only SHRINKS-or-stays. These corollaries
extract that from the executor⟺spec equivalence (so they hold of the REAL committed step). -/

/-- **`delegateAtten_spec_non_amplifying`** — from a committed `delegateAttenA`, the recipient gains a
cap that (a) is genuinely IN its post-state slot and (b) whose REAL conferred rights are `⊆` the
delegator's held cap (genuine `is_attenuation`). Read off the spec's `caps` clause (which the
committed step pins via `delegateAtten_iff_spec`) + `delegateAttenCaps_correct`. -/
theorem delegateAtten_spec_non_amplifying (s : RecChainedState) (del rec t : CellId)
    (keep : List Auth) (s' : RecChainedState)
    (h : execFullA s (.delegateAttenA del rec t keep) = some s') :
    attenuate keep (heldCapTo s.kernel.caps del t) ∈ s'.kernel.caps rec
    ∧ confRights (attenuate keep (heldCapTo s.kernel.caps del t))
        ≤ confRights (heldCapTo s.kernel.caps del t) := by
  have hspec := (delegateAtten_iff_spec s del rec t keep s').mp h
  have hcaps : s'.kernel.caps
      = grant s.kernel.caps rec (attenuate keep (heldCapTo s.kernel.caps del t)) := hspec.2.1
  obtain ⟨hmem, hle, _⟩ := delegateAttenCaps_correct s.kernel.caps del rec t keep
  exact ⟨by rw [hcaps]; exact hmem, hle⟩

/-- **`delegateAtten_spec_balance_neutral`** — from a committed `delegateAttenA`, the per-asset ledger
`bal` and the live-account set are UNCHANGED (the family is `caps`-only ⇒ conservation-trivial). Read
directly off the spec's frame clauses. -/
theorem delegateAtten_spec_balance_neutral (s : RecChainedState) (del rec t : CellId)
    (keep : List Auth) (s' : RecChainedState)
    (h : execFullA s (.delegateAttenA del rec t keep) = some s') :
    s'.kernel.bal = s.kernel.bal ∧ s'.kernel.accounts = s.kernel.accounts := by
  have hspec := (delegateAtten_iff_spec s del rec t keep s').mp h
  exact ⟨hspec.2.2.2.2.2.2.2.2.2.1, hspec.2.2.2.1⟩

/-- **`attenuate_spec_balance_neutral`** — the TOTAL `attenuateA` is likewise `caps`-only: `bal` and
`accounts` are UNCHANGED. -/
theorem attenuate_spec_balance_neutral (s : RecChainedState) (actor : CellId) (idx : Nat)
    (keep : List Auth) (s' : RecChainedState)
    (h : execFullA s (.attenuateA actor idx keep) = some s') :
    s'.kernel.bal = s.kernel.bal ∧ s'.kernel.accounts = s.kernel.accounts := by
  have hspec := (attenuate_iff_spec s actor idx keep s').mp h
  exact ⟨hspec.2.2.2.2.2.2.2.2.1, hspec.2.2.1⟩

/-! ## §4 — non-vacuity: the gate is REAL (a forged delegation is REJECTED).

A `delegateAttenA` whose delegator holds NO cap conferring an edge to `t` (`DelegateAttenGuard`
fails) makes `execFullA` return `none` — the forged/unauthorized delegation cannot commit. This is
the soundness content (matching `Transfer.lean`'s `rejects_unauthorized`): the spec is worthless if
it accepted bad inputs. -/

/-- **`delegateAtten_rejects_ungrounded` — PROVED.** A `delegateAttenA` over a pre-state where the
delegator `del` holds NO cap conferring an edge to `t` (`¬ DelegateAttenGuard`) is REJECTED by the
executor (`= none`): no `s'` is produced. An ungrounded ("only connectivity begets connectivity"
premise violated) delegation cannot commit. -/
theorem delegateAtten_rejects_ungrounded (s : RecChainedState) (del rec t : CellId)
    (keep : List Auth) (hbad : ¬ DelegateAttenGuard s del t) :
    execFullA s (.delegateAttenA del rec t keep) = none := by
  unfold DelegateAttenGuard at hbad
  simp only [execFullA, recCDelegateAtten, recKDelegateAtten]
  rw [if_neg hbad]

/-- **`delegateAtten_no_spec_when_ungrounded` — corollary.** When the guard fails, NO post-state
satisfies the spec via the executor (the `↔` collapses to `none = some s'`, impossible). -/
theorem delegateAtten_no_spec_when_ungrounded (s : RecChainedState) (del rec t : CellId)
    (keep : List Auth) (s' : RecChainedState) (hbad : ¬ DelegateAttenGuard s del t) :
    ¬ execFullA s (.delegateAttenA del rec t keep) = some s' := by
  rw [delegateAtten_rejects_ungrounded s del rec t keep hbad]; simp

/-! ## §5 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms delegateAttenCaps_correct
#assert_axioms delegateAtten_iff_spec
#assert_axioms attenuateCaps_correct
#assert_axioms attenuate_iff_spec
#assert_axioms delegateAtten_spec_non_amplifying
#assert_axioms delegateAtten_spec_balance_neutral
#assert_axioms attenuate_spec_balance_neutral
#assert_axioms delegateAtten_rejects_ungrounded
#assert_axioms delegateAtten_no_spec_when_ungrounded

end Dregg2.Circuit.Spec.AuthorityAttenuation
