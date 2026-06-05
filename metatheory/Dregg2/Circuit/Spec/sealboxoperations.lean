/-
# Dregg2.Circuit.Spec.sealboxoperations — INDEPENDENT full-state spec + executor⟺spec for the
  dregg2 effect FAMILY `seal-box-operations` (`sealA` · `unsealA`).

This is a LEAF module copying the REFERENCE pattern in `Dregg2/Circuit/Transfer.lean`
(`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`), specialised to the two seal-box arms
of the FULL op-set executor `execFullA` (`TurnExecutorFull.lean:3479`):

    execFullA s (.sealA   pid actor payload)    = sealChainA   s pid actor payload
    execFullA s (.unsealA pid actor recipient)  = unsealChainA s pid actor recipient

The two chained kernel mutators (`TurnExecutorFull.lean:1845`/`:1860`):

    sealChainA s pid actor payload
      = if (s.kernel.caps actor).any (holdsSealCapFor pid) = true ∧ payload ∈ s.kernel.caps actor
        then some { kernel := { s.kernel with sealedBoxes := ⟨pid, actor, payload⟩ :: s.kernel.sealedBoxes },
                    log    := ⟨actor, actor, actor, 0⟩ :: s.log }
        else none

    unsealChainA s pid actor recipient
      = if (s.kernel.caps actor).any (holdsSealCapFor pid) = true
        then match findSealedBox s.kernel.sealedBoxes pid with
             | some box => some { kernel := { s.kernel with caps := grant s.kernel.caps recipient box.payload },
                                  log    := ⟨actor, recipient, recipient, 0⟩ :: s.log }
             | none     => none
        else none

## The two guards (fail-closed — `CapabilityNotHeld` and absent-box).

Both arms are GUARDED (`if … then some … else none`), unlike `authorityrevocation` (unconditional).

  * `sealA`   admits IFF the actor genuinely HOLDS the sealer cap for `pid` (dregg1's
    `lookup_by_target`, `apply.rs:2756`; fail-closed `CapabilityNotHeld`) AND HOLDS the `payload` cap
    being sealed (you can only seal a cap you hold — the box payload is a confined cap). The guard is
    a TWO-conjunct `if`, modelled exactly (`sealAdmitGuard`).
  * `unsealA` admits IFF the actor HOLDS the unsealer cap for `pid` (`apply.rs:2891`) AND the box
    EXISTS in the holding-store (`findSealedBox … = some box`; fail-closed if absent). The guard is a
    held-cap conjunct PLUS the existential `∃ box, findSealedBox … = some box`, modelled exactly
    (`unsealAdmitGuard`).

## ⚑ FRAME-GAP FLAG (executor behaviour vs the task brief).

The orchestrator brief said `sealA` should REMOVE the payload cap from the actor's c-list and insert
it into the box. The ACTUAL executor (`sealChainA`, `TurnExecutorFull.lean:1845`) does NOT touch
`caps` at all — the doc comment is explicit: *"The sealer's own c-list is unchanged (the cap is
COPIED into the box, dregg1 leaves the sealer's caps intact)."* So the cap is COPIED, not MOVED, on
seal. The spec is written to match the EXECUTOR (the ground truth), and the `caps`-unchanged frame
clause is what PROVES that, both directions. This divergence is reported in `frameGaps` — it is a
spec-vs-brief mismatch (the executor is internally consistent: `unseal` then GRANTS a fresh copy to
the recipient), NOT an executor frame bug, but it IS a sealed-box-payload-vs-c-list double-spend
surface worth ember's eyes (the sealer keeps the cap AND the box holds it AND unseal grants it to a
recipient — three live copies of one capability).

Likewise `unsealChainA` does NOT remove/consume the box from `sealedBoxes` (it leaves the box in the
store), so the box can be unsealed REPEATEDLY, each unseal granting another copy of `payload`. The
`sealedBoxes`-unchanged frame clause of `UnsealSpec` PROVES this; reported in `frameGaps`.

## The FRAME (the whole point — every ghost enumerated).

`RecChainedState` = `{ kernel : RecordKernelState, log : List Turn }`, and `RecordKernelState` has
SEVENTEEN fields (`accounts cell caps escrows nullifiers revoked commitments bal queues swiss
slotCaveats factories lifecycle deathCert delegate delegations sealedBoxes`). So a full-state spec
pins 18 components (17 kernel + `log`).

  * `sealChainA` touches exactly `kernel.sealedBoxes` (prepend) + `log` (prepend). The other 16
    kernel fields (incl. `caps` — the FRAME-GAP above) are LITERALLY unchanged.
  * `unsealChainA` touches exactly `kernel.caps` (`grant` to `recipient`) + `log` (prepend). The other
    16 kernel fields (incl. `sealedBoxes` — the box is NOT consumed) are LITERALLY unchanged.

Missing ANY field reintroduces a ghost, so all are enumerated in each spec, WITHOUT reference to any
executor helper in the frame clauses.

## The deliverables (mirroring Transfer).

  1. `SealSpec` / `UnsealSpec` : `Prop` — the INDEPENDENT declarative full-state specs (admissibility
     guard ∧ the exact touched-component post ∧ the 16-field kernel FRAME + `log`).
  2. `execFullA_seal_iff_spec` / `execFullA_unseal_iff_spec` — `execFullA st (.<variant> …) = some
     st' ↔ <E>Spec …` (BOTH directions). The `→` validates the executor arm against the independent
     spec; a silently-mutated field makes it FAIL.
  3. `sealChainA_post_correct` / `unsealChainA_post_correct` — the post-state helper validated
     DECLARATIVELY (the analogues of `recTransfer_correct`): the box is prepended binding exactly
     `payload`; the recovered cap is granted to exactly `recipient`.
  4. Non-vacuity: the box genuinely binds the sealed cap; unseal genuinely grants it; fail-closed on
     the missing cap / missing box.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.SealBoxOperations

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

/-! ## §1 — The INDEPENDENT declarative post-states (touched components, no executor helper).

`sealedBox payload pid actor` and `grantedCaps caps recipient payload` are the touched-component
post-states written WITHOUT reference to the executor's `sealChainA`/`unsealChainA` bodies. These are
the apex reference for the `sealedBoxes`/`caps` post-states; the executor's bodies are then proved
equal to them (`sealChainA_post_correct`/`unsealChainA_post_correct`). -/

/-- **`sealedBoxPrepend`** — the declarative sealed-box holding-store after `actor` seals `payload`
into a box keyed by `pid`: the box `⟨pid, actor, payload⟩` prepended, all prior boxes verbatim. -/
def sealedBoxPrepend (boxes : List SealedBoxRecord) (pid : Nat) (actor : CellId) (payload : Cap) :
    List SealedBoxRecord :=
  { pairId := pid, sealer := actor, payload := payload } :: boxes

/-- **`grantedCaps`** — the declarative cap-table after the recovered `payload` is granted to
`recipient` (the cap prepended to `recipient`'s slot; every other holder verbatim). Written
independently of the executor; proved equal to `grant` (which is `grant`, here exhibited as the
reference, validated by `unsealChainA_post_correct`). -/
def grantedCaps (caps : Caps) (recipient : CellId) (payload : Cap) : Caps :=
  fun l => if l = recipient then payload :: caps l else caps l

/-- **`grantedCaps_eq_grant`** — the declarative `grantedCaps` IS the executor's `grant` primitive
(`Caps.lean:72`). So pinning the unseal spec's `caps` clause to `grantedCaps` genuinely encodes the
executor's c-list grant, while being written independently of it. -/
theorem grantedCaps_eq_grant (caps : Caps) (recipient : CellId) (payload : Cap) :
    grantedCaps caps recipient payload = grant caps recipient payload := rfl

/-- **`sealReceipt`** / **`unsealReceipt`** — the audit-log rows the two arms append (the chain
advances by exactly one row each). Written declaratively to keep the `log` frame independent. -/
def sealReceipt (actor : CellId) : Turn := { actor := actor, src := actor, dst := actor, amt := 0 }
def unsealReceipt (actor recipient : CellId) : Turn :=
  { actor := actor, src := recipient, dst := recipient, amt := 0 }

/-- **`sealChainA_post_correct`** — the declarative `sealedBoxPrepend` IS the executor's
`sealChainA` post-`sealedBoxes`, and `sealReceipt` IS its log row — validated under the guard (so the
spec's clauses genuinely encode the executor's seal). -/
theorem sealChainA_post_correct (s : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap)
    (s' : RecChainedState) (h : sealChainA s pid actor payload = some s') :
    s'.kernel.sealedBoxes = sealedBoxPrepend s.kernel.sealedBoxes pid actor payload
    ∧ s'.log = sealReceipt actor :: s.log := by
  obtain ⟨_, hs'⟩ := sealChainA_factors h
  subst hs'; exact ⟨rfl, rfl⟩

/-- **`unsealChainA_post_correct`** — the declarative `grantedCaps` IS the executor's `unsealChainA`
post-`caps` (the recovered box payload granted to `recipient`), and `unsealReceipt` IS its log row —
validated against the box the store holds. -/
theorem unsealChainA_post_correct (s : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (box : SealedBoxRecord) (s' : RecChainedState)
    (hbox : findSealedBox s.kernel.sealedBoxes pid = some box)
    (h : unsealChainA s pid actor recipient = some s') :
    s'.kernel.caps = grantedCaps s.kernel.caps recipient box.payload
    ∧ s'.log = unsealReceipt actor recipient :: s.log := by
  obtain ⟨box', hbox', _, hs'⟩ := unsealChainA_factors h
  rw [hbox] at hbox'; cases hbox'
  subst hs'; exact ⟨rfl, rfl⟩

/-! ## §2 — The admissibility guards, as `Prop`s (the fail-closed `if` of each arm). -/

/-- **`sealAdmitGuard`** — the full admissibility guard `sealChainA` checks (the conjunction in its
`if`): the actor HOLDS the sealer cap for `pid` AND HOLDS the `payload` cap it is sealing. -/
def sealAdmitGuard (s : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap) : Prop :=
  (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true ∧ payload ∈ s.kernel.caps actor

/-- **`unsealAdmitGuard`** — the full admissibility guard `unsealChainA` checks: the actor HOLDS the
unsealer cap for `pid`, AND the box EXISTS in the holding-store. (The box's identity feeds the
post-state, so the guard is existential over the found box.) -/
def unsealAdmitGuard (s : RecChainedState) (pid : Nat) (actor : CellId) (box : SealedBoxRecord) :
    Prop :=
  (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true ∧
    findSealedBox s.kernel.sealedBoxes pid = some box

/-! ## §3 — FULL-STATE SEMANTIC SPECS (the INDEPENDENT reference) + executor⟺spec.

`SealSpec` / `UnsealSpec` are the COMPLETE declarative post-states, written INDEPENDENTLY of the
executor (no `sealChainA`/`unsealChainA` term in any frame clause). -/

/-- **The full-state declarative spec of a committed `sealA`** — the INDEPENDENT reference semantics
over `RecChainedState`. The seal guard holds; `sealedBoxes` is the declarative prepend; `log` grows
by `sealReceipt`; and every one of the 16 non-`sealedBoxes` kernel fields (INCLUDING `caps` — the
sealer's c-list is UNCHANGED, the FRAME-GAP flag) is literally unchanged. No frame clause mentions
the executor. -/
def SealSpec (st : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap)
    (st' : RecChainedState) : Prop :=
  sealAdmitGuard st pid actor payload
  ∧ st'.kernel.sealedBoxes = sealedBoxPrepend st.kernel.sealedBoxes pid actor payload
  ∧ st'.log = sealReceipt actor :: st.log
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.escrows = st.kernel.escrows
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.queues = st.kernel.queues
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations

/-- **The full-state declarative spec of a committed `unsealA`** — the INDEPENDENT reference
semantics over `RecChainedState`. The unseal guard holds (against the found `box`); `caps` is the
declarative grant of `box.payload` to `recipient`; `log` grows by `unsealReceipt`; and every one of
the 16 non-`caps` kernel fields (INCLUDING `sealedBoxes` — the box is NOT consumed, the FRAME-GAP
flag) is literally unchanged. No frame clause mentions the executor. -/
def UnsealSpec (st : RecChainedState) (pid : Nat) (actor recipient : CellId) (box : SealedBoxRecord)
    (st' : RecChainedState) : Prop :=
  unsealAdmitGuard st pid actor box
  ∧ st'.kernel.caps = grantedCaps st.kernel.caps recipient box.payload
  ∧ st'.log = unsealReceipt actor recipient :: st.log
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.escrows = st.kernel.escrows
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.queues = st.kernel.queues
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes

/-! ## §4 — The executor ⟺ spec equivalences (FULL state, both directions). -/

/-- **`sealChainA_iff_spec` — `sealChainA` ⟺ `SealSpec` (FULL state, both directions).** The chained
seal mutator commits into `st'` IFF `st'` is EXACTLY the spec'd full post-state. The `→` direction
VALIDATES `sealChainA` against the independent spec — all 18 components (16 framed kernel fields + the
`sealedBoxes` post + the `log` post) are checked, so had the mutator silently touched
`caps`/`bal`/`nullifiers`/… the frame clauses would make this proof FAIL; the `←` reconstructs the
committed state from the spec. -/
theorem sealChainA_iff_spec (st : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap)
    (st' : RecChainedState) :
    sealChainA st pid actor payload = some st' ↔ SealSpec st pid actor payload st' := by
  unfold sealChainA SealSpec sealAdmitGuard sealedBoxPrepend sealReceipt
  by_cases hg : (st.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true
      ∧ payload ∈ st.kernel.caps actor
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h; subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
             rfl⟩
    · rintro ⟨_, hsb, hlog, hacc, hcell, hcaps, hesc, hnull, hrev, hcom, hbal, hq, hsw, hsc, hfac,
             hlif, hdc, hdel, hdels⟩
      obtain ⟨k', log'⟩ := st'
      obtain ⟨acc', cell', caps', esc', null', rev', com', bal', q', sw', sc', fac', lif', dc', del',
              dels', sb'⟩ := k'
      subst hacc hcell hcaps hesc hnull hrev hcom hbal hq hsw hsc hfac hlif hdc hdel hdels hsb hlog
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`unsealChainA_iff_spec` — `unsealChainA` ⟺ `UnsealSpec` (FULL state, both directions).** The
chained unseal mutator commits into `st'` IFF `st'` is EXACTLY the spec'd full post-state (against the
box the store holds). The `→` validates `unsealChainA` against the independent spec — all 18
components are checked, including `sealedBoxes` (the box is NOT consumed). -/
theorem unsealChainA_iff_spec (st : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (box : SealedBoxRecord) (st' : RecChainedState)
    (hbox : findSealedBox st.kernel.sealedBoxes pid = some box) :
    unsealChainA st pid actor recipient = some st' ↔ UnsealSpec st pid actor recipient box st' := by
  unfold unsealChainA UnsealSpec unsealAdmitGuard unsealReceipt
  by_cases hg : (st.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true
  · rw [if_pos hg, hbox]
    constructor
    · intro h
      simp only [Option.some.injEq] at h; subst h
      -- the executor writes `grant st.kernel.caps recipient box.payload`; `grantedCaps` IS `grant`.
      -- `rw […, hbox]` above already rewrote the goal's `findSealedBox … = some box` to `some box =
      -- some box`, so the unsealAdmitGuard's box conjunct is discharged by `rfl`.
      refine ⟨⟨hg, rfl⟩, (grantedCaps_eq_grant _ _ _).symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
             rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨⟨_, _⟩, hcaps, hlog, hacc, hcell, hesc, hnull, hrev, hcom, hbal, hq, hsw, hsc, hfac,
             hlif, hdc, hdel, hdels, hsb⟩
      obtain ⟨k', log'⟩ := st'
      obtain ⟨acc', cell', caps', esc', null', rev', com', bal', q', sw', sc', fac', lif', dc', del',
              dels', sb'⟩ := k'
      -- the spec's `caps` post is `grantedCaps`; rewrite it to the executor's `grant` form.
      rw [grantedCaps_eq_grant] at hcaps
      subst hacc hcell hcaps hesc hnull hrev hcom hbal hq hsw hsc hfac hlif hdc hdel hdels hsb hlog
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hg', _⟩, _⟩; exact absurd hg' hg

/-- **`execFullA_seal_iff_spec` — EXECUTOR ⟺ SPEC for the `sealA` arm (FULL state, both
directions).** `execFullA st (.sealA pid actor payload) = some st'` IFF `st'` is exactly the spec'd
full post-state. The `→` validates the `sealA` executor arm against the independent spec. -/
theorem execFullA_seal_iff_spec (st : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap)
    (st' : RecChainedState) :
    execFullA st (.sealA pid actor payload) = some st' ↔ SealSpec st pid actor payload st' := by
  rw [show execFullA st (.sealA pid actor payload) = sealChainA st pid actor payload from rfl]
  exact sealChainA_iff_spec st pid actor payload st'

/-- **`execFullA_unseal_iff_spec` — EXECUTOR ⟺ SPEC for the `unsealA` arm (FULL state, both
directions).** `execFullA st (.unsealA pid actor recipient) = some st'` IFF `st'` is exactly the
spec'd full post-state (against the box `findSealedBox` returns). -/
theorem execFullA_unseal_iff_spec (st : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (box : SealedBoxRecord) (st' : RecChainedState)
    (hbox : findSealedBox st.kernel.sealedBoxes pid = some box) :
    execFullA st (.unsealA pid actor recipient) = some st' ↔
      UnsealSpec st pid actor recipient box st' := by
  rw [show execFullA st (.unsealA pid actor recipient) = unsealChainA st pid actor recipient from rfl]
  exact unsealChainA_iff_spec st pid actor recipient box st' hbox

/-! ## §5 — Non-vacuity: the specs are GENUINE cap-movement, not rubber stamps.

A spec that left `sealedBoxes`/`caps` untouched would be worthless. Here we EXHIBIT that the box
genuinely BINDS the sealed cap, the unseal genuinely GRANTS it to the recipient, and both arms are
fail-closed on the missing-cap / missing-box conditions. -/

/-- **`seal_box_binds_payload` — PROVED.** After a committed seal, the holding-store's HEAD box binds
EXACTLY the sealed `payload` (keyed by `pid`, sealed by `actor`). The box carries a REAL cap, not a
flag. -/
theorem seal_box_binds_payload (st : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap)
    (st' : RecChainedState) (h : SealSpec st pid actor payload st') :
    st'.kernel.sealedBoxes.head? = some { pairId := pid, sealer := actor, payload := payload } := by
  obtain ⟨_, hsb, _⟩ := h
  rw [hsb]; rfl

/-- **`seal_preserves_caps` — PROVED (the FRAME-GAP, made explicit).** A committed seal does NOT
change `caps` at all — the sealer KEEPS the `payload` cap it sealed (the cap is COPIED into the box,
not moved out of the c-list). This is the brief-vs-executor divergence, here a PROVEN frame fact. -/
theorem seal_preserves_caps (st : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap)
    (st' : RecChainedState) (h : SealSpec st pid actor payload st') :
    st'.kernel.caps = st.kernel.caps := by
  obtain ⟨_, _, _, _, _, hcaps, _⟩ := h
  exact hcaps

/-- **`seal_preserves_balances` — PROVED.** The dual frame: a seal edits only `sealedBoxes`+`log`, so
the conserved `recTotal` (and `accounts`/`cell`) are unchanged. Sealing moves no value. -/
theorem seal_preserves_balances (st : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap)
    (st' : RecChainedState) (h : SealSpec st pid actor payload st') :
    recTotal st'.kernel = recTotal st.kernel
    ∧ st'.kernel.accounts = st.kernel.accounts
    ∧ st'.kernel.cell = st.kernel.cell := by
  obtain ⟨_, _, _, hacc, hcell, _⟩ := h
  refine ⟨?_, hacc, hcell⟩
  unfold recTotal; rw [hacc, hcell]

/-- **`unseal_grants_sealed_cap` — THE CAP-MOVEMENT TEETH (PROVED).** After a committed unseal, the
`recipient` HOLDS the box's `payload` cap (it is the head of their c-list). The capability genuinely
MOVED through the box into the recipient — a flag-flip could NEVER witness this. NON-VACUOUS: the
granted cap is EXACTLY the one the box bound. -/
theorem unseal_grants_sealed_cap (st : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (box : SealedBoxRecord) (st' : RecChainedState)
    (h : UnsealSpec st pid actor recipient box st') :
    box.payload ∈ st'.kernel.caps recipient := by
  obtain ⟨_, hcaps, _⟩ := h
  rw [hcaps]
  show box.payload ∈ grantedCaps st.kernel.caps recipient box.payload recipient
  unfold grantedCaps
  rw [if_pos rfl]
  exact List.mem_cons_self ..

/-- **`unseal_preserves_box_store` — PROVED (the second FRAME-GAP, made explicit).** A committed
unseal does NOT consume the box — `sealedBoxes` is unchanged. So a box may be unsealed REPEATEDLY,
each unseal granting another copy of `payload`. This is a PROVEN frame fact (the box is not
single-use). -/
theorem unseal_preserves_box_store (st : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (box : SealedBoxRecord) (st' : RecChainedState)
    (h : UnsealSpec st pid actor recipient box st') :
    st'.kernel.sealedBoxes = st.kernel.sealedBoxes := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsb⟩ := h
  exact hsb

/-- **`unseal_preserves_other_holders` — PROVED.** Any holder `l ≠ recipient` keeps its cap-list
verbatim across the unseal — only the recipient's slot GROWS (by the recovered cap). -/
theorem unseal_preserves_other_holders (st : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (box : SealedBoxRecord) (st' : RecChainedState)
    (h : UnsealSpec st pid actor recipient box st') :
    ∀ l, l ≠ recipient → st'.kernel.caps l = st.kernel.caps l := by
  obtain ⟨_, hcaps, _⟩ := h
  intro l hl
  rw [hcaps]; simp only [grantedCaps, if_neg hl]

/-- **`seal_fail_closed_no_cap` — PROVED.** Sealing when the actor does NOT hold the sealer cap for
`pid` returns `none` (fail-closed `CapabilityNotHeld`): no box is created. -/
theorem seal_fail_closed_no_cap (st : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap)
    (hno : (st.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = false) :
    sealChainA st pid actor payload = none := by
  unfold sealChainA
  rw [if_neg (by rw [hno]; simp)]

/-- **`unseal_fail_closed_no_box` — PROVED.** Unsealing a `pid` with NO box in the holding-store
returns `none`: no cap is granted (the cap must genuinely have been sealed first). -/
theorem unseal_fail_closed_no_box (st : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (hno : findSealedBox st.kernel.sealedBoxes pid = none) :
    unsealChainA st pid actor recipient = none :=
  unsealChainA_noBox_rejects st pid actor recipient hno

/-! ## §6 — Concrete witnesses (a seal/unseal is decidably the cap movement). -/

/-- A concrete pre-state: cell `0` holds the sealer cap for pair `5`, the unsealer cap for `5`, and a
payload `Cap.node 42`. Nobody else holds anything. Empty box store. -/
def kS0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [sealerCap 5, unsealerCap 5, Cap.node 42] else [] }

-- The seal commits (actor 0 holds the sealer cap AND the payload):
#guard (execFullA { kernel := kS0, log := [] } (.sealA 5 0 (Cap.node 42))).isSome  -- true
-- Fail-closed: actor 9 holds NO sealer cap ⇒ CapabilityNotHeld:
#guard (execFullA { kernel := kS0, log := [] } (.sealA 5 9 (Cap.node 42))).isSome == false  -- false
-- Fail-closed: unseal with an EMPTY box store ⇒ no box ⇒ none:
#guard (execFullA { kernel := kS0, log := [] } (.unsealA 5 0 1)).isSome == false  -- false

/-! ## §7 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms grantedCaps_eq_grant
#assert_axioms sealChainA_post_correct
#assert_axioms unsealChainA_post_correct
#assert_axioms sealChainA_iff_spec
#assert_axioms unsealChainA_iff_spec
#assert_axioms execFullA_seal_iff_spec
#assert_axioms execFullA_unseal_iff_spec
#assert_axioms seal_box_binds_payload
#assert_axioms seal_preserves_caps
#assert_axioms seal_preserves_balances
#assert_axioms unseal_grants_sealed_cap
#assert_axioms unseal_preserves_box_store
#assert_axioms unseal_preserves_other_holders
#assert_axioms seal_fail_closed_no_cap
#assert_axioms unseal_fail_closed_no_box

end Dregg2.Circuit.Spec.SealBoxOperations
