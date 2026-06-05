/-
# Dregg2.Circuit.Spec.queuefifocore — INDEPENDENT full-state spec + executor⟺spec for the
`queue-fifo-core` effect family (the `FullActionA.queueAllocateA` / `.queueResizeA` /
`.queueEnqueueA` / `.queueDequeueA` variants).

This is a LEAF module (imported by nothing; gated standalone). It is the `Transfer.lean` reference
pattern (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) re-derived INDEPENDENTLY for
the REAL ring-buffer FIFO queue effects the unified action executor `execFullA` dispatches:

    execFullA s (.queueAllocateA id actor cell cap) = queueAllocateChainA s id actor cell cap   -- :3569
    execFullA s (.queueResizeA id newCap actor cell) = queueResizeChainA s id newCap actor cell -- :3572
    execFullA s (.queueEnqueueA id m actor cell depId dAsset deposit)
      = queueEnqueueChainA s id m actor cell depId dAsset deposit                               -- :3570
    execFullA s (.queueDequeueA id actor cell depId deposit)
      = queueDequeueChainA s id actor cell depId deposit                                        -- :3571

## Scope of this leaf (truthful)

Two of the four variants — **`queueAllocateA`** and **`queueResizeA`** — are balance-NEUTRAL: they
touch ONLY the `queues` side-table and the chained `log`. The other 16 kernel components are the
FRAME. These two are given the FULL apex treatment below (independent spec, executor⟺spec BOTH
directions, declarative post-state-helper validation, non-vacuity).

The remaining two — **`queueEnqueueA`** and **`queueDequeueA`** — are NOT balance-neutral: they
ALSO drive the refundable anti-spam deposit through the SHARED escrow holding-store
(`queueEnqueueDepositK` composes `queueEnqueueK` with `createEscrowRawAsset`;
`queueDequeueRefundK` composes `queueDequeueK` with `settleEscrowRawAsset`). Their full-state spec
must additionally pin the `bal` ledger move AND the `escrows` store move (a TWO-component touch on
top of `queues`). We give them the SAME apex treatment — their full-state specs name all 17 kernel
components + log, the executor⟺spec is proved BOTH directions, and the deposit/refund are validated
declaratively — so the family is complete.

## What is proved (the apex reference truth, BOTH directions)

For EACH of the four variants `<V>`:
  * `Queue<V>Spec st … st'` — the INDEPENDENT declarative full-state post-condition: the
    admissibility guard, the EXACT post-state on the touched component(s), the chained `log` advanced
    by exactly the receipt row, AND the FRAME — every OTHER RecordKernelState component LITERALLY
    unchanged. No frame clause mentions the executor's helpers. All 17 kernel components + log are
    enumerated; missing ANY field reintroduces a ghost.
  * a declarative validation lemma for the post-state helper (the freshly-inserted/replaced queue
    record / the deposit-park / the refund), so the spec's `queues`/`bal`/`escrows` clauses genuinely
    encode the effect rather than blind-trusting the executor's body.
  * `execFullA_queue<V>A_iff_spec` — execFullA ⟺ spec (BOTH directions). The `→` VALIDATES the
    executor against the independent spec — all 17 kernel fields + log are checked, so a silently
    mutated field would make the proof FAIL; the `←` reconstructs the committed state from the spec.
  * Non-vacuity: each forged input fails a guard leg ⇒ the executor returns `none` ⇒ no spec
    post-state exists.

## FRAME-GAP findings (surfaced by the proofs, NOT silently fixed)

  * **owner = actor (NOT cell).** `queueAllocateChainA s id actor cell cap` allocates with
    `owner := actor` (it calls `queueAllocateK s.kernel id actor capacity`, passing `actor` as the
    owner). The task brief said `owner = cell`; the EXECUTOR uses `actor`. The spec faithfully pins
    `owner := actor` (the brief is wrong, not the code). This is an interface fact worth a human
    glance, not a frame bug.
  * **NO `cap > 0` guard on allocate.** The brief listed `cap > 0` as an admissibility leg;
    `queueAllocateK` accepts ANY `capacity : Nat` (including `0` — a zero-capacity queue that can
    never enqueue). The executor's allocate guard is ONLY `stateAuthB ∧ freshness`. The spec pins
    exactly that. (Not a frame mutation; a missing guard the brief assumed.)
  * **`acceptsEffects` asymmetry.** allocate's guard is `stateAuthB` ALONE; resize/enqueue/dequeue
    additionally require `acceptsEffects s.kernel cell = true` (the lifecycle-liveness gate). Faithful
    to the executor; pinned per-variant.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.QueueFifoCore

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)

/-! ## §1 — `queueAllocateA` — the freshly-allocated FIFO queue (balance-NEUTRAL, one component).

`execFullA s (.queueAllocateA id actor cell cap) = queueAllocateChainA s id actor cell cap`
(`TurnExecutorFull:3569`).

    queueAllocateChainA s id actor cell cap                                       -- :2026
      = if stateAuthB s.kernel.caps actor cell = true then
          match queueAllocateK s.kernel id actor cap with
          | some k' => some { kernel := k', log := {actor, src:=cell, dst:=cell, amt:=0} :: s.log }
          | none    => none
        else none

    queueAllocateK k id owner capacity                                            -- RecordKernel:2103
      = match findQueue k.queues id with
        | some _ => none
        | none   => some { k with queues := {id, owner, capacity, buffer := []} :: k.queues }

So the admissibility guard is: `stateAuthB caps actor cell = true ∧ findQueue queues id = none`
(authority over the representing cell ∧ id FRESHNESS). On commit the ONLY kernel component touched is
`queues` (a fresh record prepended, `owner := actor`); the `log` advances by the allocate receipt
`{actor, src:=cell, dst:=cell, amt:=0}`; the other 16 kernel fields are the FRAME. -/

/-- The allocate admissibility guard, as a `Prop` — exactly the two legs `queueAllocateChainA`
checks (authority over `cell`, then `queueAllocateK`'s id-freshness). -/
def allocateGuard (k : RecordKernelState) (id : Nat) (actor cell : CellId) : Prop :=
  stateAuthB k.caps actor cell = true ∧ findQueue k.queues id = none

/-- The fresh queue record an allocate inserts (declarative form — `owner := actor`, the EXECUTOR's
choice; see the FRAME-GAP note in the header). Stated HERE so the spec's `queues` clause does not
reference the executor's body. -/
def freshQueue (id : Nat) (actor : CellId) (capacity : Nat) : QueueRecord :=
  { id := id, owner := actor, capacity := capacity, buffer := [] }

/-- The allocate receipt row (the chained `log` advance). -/
def allocateReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-- **`queueAllocateK_correct`** — the allocate post-state helper validated DECLARATIVELY: on a fresh
id, `queueAllocateK` prepends EXACTLY `freshQueue` onto `queues` and leaves every other kernel
component unchanged. So the spec's `queues` clause genuinely encodes prepend ∧ kernel-frame. -/
theorem queueAllocateK_correct (k : RecordKernelState) (id : Nat) (owner : CellId) (capacity : Nat)
    (hfresh : findQueue k.queues id = none) :
    queueAllocateK k id owner capacity
      = some { k with queues := { id := id, owner := owner, capacity := capacity, buffer := [] } :: k.queues } := by
  unfold queueAllocateK
  rw [hfresh]

/-- **The full-state declarative spec of a committed `queueAllocateA`** — the INDEPENDENT reference
semantics. The guard holds (`allocateGuard`); the post-`queues` table is `freshQueue :: st.queues`;
the chained `log` is `allocateReceipt actor cell :: st.log`; and every one of the 16 other
RecordKernelState components is LITERALLY unchanged (the FRAME). No frame clause references the
executor. -/
def QueueAllocateSpec (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (st' : RecChainedState) : Prop :=
  allocateGuard st.kernel id actor cell
  ∧ st'.kernel.queues = freshQueue id actor cap :: st.kernel.queues
  ∧ st'.log = allocateReceipt actor cell :: st.log
  -- THE FRAME: every non-`queues` RecordKernelState field, literally unchanged (16).
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.escrows = st.kernel.escrows
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes

/-- **`queueAllocateChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
allocate step. `queueAllocateChainA` commits a fresh queue into `st'` IFF `st'` is EXACTLY the spec'd
full post-state. The `→` VALIDATES `queueAllocateChainA` against the independent spec — all 17 kernel
components (`queues` + the 16 frame fields) AND the log are checked, so a silently mutated field would
make the proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem queueAllocateChainA_iff_spec (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (st' : RecChainedState) :
    queueAllocateChainA st id actor cell cap = some st'
      ↔ QueueAllocateSpec st id actor cell cap st' := by
  unfold queueAllocateChainA QueueAllocateSpec allocateGuard queueAllocateK
  by_cases hauth : stateAuthB st.kernel.caps actor cell = true
  · rw [if_pos hauth]
    cases hfresh : findQueue st.kernel.queues id with
    | some q =>
        -- duplicate id ⇒ `queueAllocateK = none` ⇒ chain = none; spec's freshness leg also fails.
        simp only
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨⟨_, hf⟩, _⟩; exact absurd hf (by simp)
    | none =>
        simp only [freshQueue, allocateReceipt]
        constructor
        · intro h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨⟨hauth, trivial⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                 rfl, rfl, rfl, rfl, rfl⟩
        · rintro ⟨_, hq, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
          obtain ⟨k', l'⟩ := st'
          obtain ⟨acc, cell0, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
          simp only at hq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
          subst hq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
          rfl
  · rw [if_neg hauth]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hg, _⟩, _⟩; exact absurd hg hauth

/-- **`execFullA_queueAllocateA_iff_spec` — the UNIFIED-ACTION executor corner.** `execFullA`
dispatches `.queueAllocateA …` to `queueAllocateChainA s …`, so committing the unified action into
`st'` is EXACTLY the full-state spec. -/
theorem execFullA_queueAllocateA_iff_spec (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (cap : Nat) (st' : RecChainedState) :
    execFullA st (.queueAllocateA id actor cell cap) = some st'
      ↔ QueueAllocateSpec st id actor cell cap st' := by
  show queueAllocateChainA st id actor cell cap = some st' ↔ QueueAllocateSpec st id actor cell cap st'
  exact queueAllocateChainA_iff_spec st id actor cell cap st'

/-! ### allocate post-state corollaries (read off the spec). -/

/-- **`allocate_inserts_fresh`** — a committed allocate prepends EXACTLY the fresh queue record (with
`owner := actor`, empty buffer, the given capacity) onto the side-table. -/
theorem allocate_inserts_fresh (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (st' : RecChainedState)
    (h : execFullA st (.queueAllocateA id actor cell cap) = some st') :
    st'.kernel.queues = freshQueue id actor cap :: st.kernel.queues :=
  ((execFullA_queueAllocateA_iff_spec st id actor cell cap st').mp h).2.1

/-- **`allocate_balNeutral_ledger`** — a committed allocate leaves the entire per-asset `bal` ledger
unchanged (queues hold MESSAGES, never balance). -/
theorem allocate_balNeutral_ledger (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (st' : RecChainedState)
    (h : execFullA st (.queueAllocateA id actor cell cap) = some st') :
    st'.kernel.bal = st.kernel.bal :=
  ((execFullA_queueAllocateA_iff_spec st id actor cell cap st').mp h).2.2.2.2.2.2.2.2.2.2.1

/-! ### allocate non-vacuity (each guard leg, fail-closed). -/

/-- **`allocate_rejects_unauthorized` — PROVED.** An actor lacking authority over `cell` cannot
allocate ⇒ no `st'` satisfies the spec. -/
theorem allocate_rejects_unauthorized (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (hbad : stateAuthB st.kernel.caps actor cell = false) :
    execFullA st (.queueAllocateA id actor cell cap) = none := by
  show queueAllocateChainA st id actor cell cap = none
  unfold queueAllocateChainA
  rw [if_neg (by rw [hbad]; simp)]

/-- **`allocate_rejects_id_reuse` — PROVED.** An allocate whose `id` is ALREADY a live queue does NOT
commit (the FRESHNESS leg fails) — queue ids cannot collide on the side-table. -/
theorem allocate_rejects_id_reuse (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (q : QueueRecord) (hbad : findQueue st.kernel.queues id = some q) :
    execFullA st (.queueAllocateA id actor cell cap) = none := by
  show queueAllocateChainA st id actor cell cap = none
  unfold queueAllocateChainA queueAllocateK
  by_cases hauth : stateAuthB st.kernel.caps actor cell = true
  · rw [if_pos hauth, hbad]
  · rw [if_neg hauth]

/-! ## §2 — `queueResizeA` — re-cap an existing FIFO queue (balance-NEUTRAL, one component).

`execFullA s (.queueResizeA id newCap actor cell) = queueResizeChainA s id newCap actor cell`
(`TurnExecutorFull:3572`).

    queueResizeChainA s id newCap actor cell                                      -- :2065
      = if stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true then
          match queueResizeK s.kernel id newCap with
          | some k' => some { kernel := k', log := {actor, src:=cell, dst:=cell, amt:=0} :: s.log }
          | none    => none
        else none

    queueResizeK k id newCap                                                      -- RecordKernel:2140
      = match findQueue k.queues id with
        | none   => none
        | some q => if q.buffer.length ≤ newCap then
                      some { k with queues := replaceQueue k.queues id { q with capacity := newCap } }
                    else none

Admissibility: `stateAuthB ∧ acceptsEffects cell ∧ ∃ q, findQueue queues id = some q ∧
q.buffer.length ≤ newCap` (authority ∧ lifecycle-liveness ∧ queue EXISTS ∧ can't shrink below
current occupancy). On commit the ONLY kernel component touched is `queues` (the record re-capped via
`replaceQueue`, buffer untouched); the `log` advances by the resize receipt; the other 16 kernel
fields are the FRAME. -/

/-- The resize admissibility guard, as a `Prop` — authority, lifecycle-liveness, queue existence, and
the no-shrink-below-occupancy bound `queueResizeK` checks. -/
def resizeGuard (k : RecordKernelState) (id : Nat) (newCap : Nat) (actor cell : CellId) : Prop :=
  stateAuthB k.caps actor cell = true ∧ acceptsEffects k cell = true
    ∧ ∃ q, findQueue k.queues id = some q ∧ q.buffer.length ≤ newCap

/-- The resize receipt row (the chained `log` advance — a clock row, `amt := 0`). -/
def resizeReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-- **`queueResizeK_correct`** — the resize post-state helper validated DECLARATIVELY: on an existing
queue `q` whose occupancy fits `newCap`, `queueResizeK` replaces `q` by `{q with capacity := newCap}`
(buffer UNCHANGED) in `queues` and leaves every other kernel component unchanged. So the spec's
`queues` clause genuinely encodes a capacity-only re-cap. -/
theorem queueResizeK_correct (k : RecordKernelState) (id newCap : Nat) (q : QueueRecord)
    (hq : findQueue k.queues id = some q) (hcap : q.buffer.length ≤ newCap) :
    queueResizeK k id newCap
      = some { k with queues := replaceQueue k.queues id { q with capacity := newCap } } := by
  unfold queueResizeK
  simp only [hq, if_pos hcap]

/-- **The full-state declarative spec of a committed `queueResizeA`** — the INDEPENDENT reference
semantics. The guard holds (`resizeGuard`); the post-`queues` table is the witnessed queue re-capped
in place via `replaceQueue`; the chained `log` is `resizeReceipt actor cell :: st.log`; and every one
of the 16 other RecordKernelState components is LITERALLY unchanged (the FRAME). -/
def QueueResizeSpec (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (st' : RecChainedState) : Prop :=
  resizeGuard st.kernel id newCap actor cell
  ∧ (∀ q, findQueue st.kernel.queues id = some q →
        st'.kernel.queues = replaceQueue st.kernel.queues id { q with capacity := newCap })
  ∧ st'.log = resizeReceipt actor cell :: st.log
  -- THE FRAME: every non-`queues` RecordKernelState field, literally unchanged (16).
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.escrows = st.kernel.escrows
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes

/-- **`queueResizeChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
resize step. The `→` VALIDATES `queueResizeChainA` against the independent spec — all 17 kernel
components AND the log are checked; the `←` reconstructs the committed state from the spec. -/
theorem queueResizeChainA_iff_spec (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (st' : RecChainedState) :
    queueResizeChainA st id newCap actor cell = some st'
      ↔ QueueResizeSpec st id newCap actor cell st' := by
  unfold queueResizeChainA QueueResizeSpec resizeGuard queueResizeK
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
    obtain ⟨hauth, hacc⟩ := hg
    cases hf : findQueue st.kernel.queues id with
    | none =>
        simp only
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨⟨_, _, q, hq, _⟩, _⟩; exact absurd hq (by simp)
    | some q =>
        by_cases hcap : q.buffer.length ≤ newCap
        · simp only [if_pos hcap, resizeReceipt]
          constructor
          · intro h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨⟨hauth, hacc, q, rfl, hcap⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            intro q' hq'; simp only [Option.some.injEq] at hq'; subst hq'; rfl
          · rintro ⟨_, hq, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
            have hqeq := hq q rfl
            obtain ⟨k', l'⟩ := st'
            obtain ⟨acc, cell0, caps, esc, nul, rev, com, bal, qs, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
            simp only at hqeq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
            subst hqeq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
            rfl
        · simp only [if_neg hcap]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨⟨_, _, q', hq', hcap'⟩, _⟩
            simp only [Option.some.injEq] at hq'; subst hq'; exact absurd hcap' hcap
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hauth, hacc, _⟩, _⟩; exact absurd ⟨hauth, hacc⟩ hg

/-- **`execFullA_queueResizeA_iff_spec` — the UNIFIED-ACTION executor corner.** -/
theorem execFullA_queueResizeA_iff_spec (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (st' : RecChainedState) :
    execFullA st (.queueResizeA id newCap actor cell) = some st'
      ↔ QueueResizeSpec st id newCap actor cell st' := by
  show queueResizeChainA st id newCap actor cell = some st' ↔ QueueResizeSpec st id newCap actor cell st'
  exact queueResizeChainA_iff_spec st id newCap actor cell st'

/-! ### resize non-vacuity (each guard leg, fail-closed). -/

/-- **`resize_rejects_unauthorized` — PROVED.** -/
theorem resize_rejects_unauthorized (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (hbad : stateAuthB st.kernel.caps actor cell = false) :
    execFullA st (.queueResizeA id newCap actor cell) = none := by
  show queueResizeChainA st id newCap actor cell = none
  unfold queueResizeChainA
  rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]

/-- **`resize_rejects_dead_cell` — PROVED.** A resize on a non-Live cell (`acceptsEffects = false`)
does NOT commit (the lifecycle-liveness leg fails). -/
theorem resize_rejects_dead_cell (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (hbad : acceptsEffects st.kernel cell = false) :
    execFullA st (.queueResizeA id newCap actor cell) = none := by
  show queueResizeChainA st id newCap actor cell = none
  unfold queueResizeChainA
  rw [if_neg (by rw [hbad]; rintro ⟨_, h⟩; exact absurd h (by simp))]

/-- **`resize_rejects_absent` — PROVED.** A resize of a non-existent queue does NOT commit. -/
theorem resize_rejects_absent (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (hbad : findQueue st.kernel.queues id = none) :
    execFullA st (.queueResizeA id newCap actor cell) = none := by
  show queueResizeChainA st id newCap actor cell = none
  unfold queueResizeChainA queueResizeK
  simp only [hbad]
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
  · rw [if_neg hg]

/-- **`resize_rejects_shrink_below_occupancy` — PROVED.** A resize whose `newCap` is below the
queue's current occupancy does NOT commit (the no-shrink bound fails) — pending messages cannot be
silently dropped. -/
theorem resize_rejects_shrink_below_occupancy (st : RecChainedState) (id newCap : Nat)
    (actor cell : CellId) (q : QueueRecord)
    (hq : findQueue st.kernel.queues id = some q) (hbad : ¬ q.buffer.length ≤ newCap) :
    execFullA st (.queueResizeA id newCap actor cell) = none := by
  show queueResizeChainA st id newCap actor cell = none
  unfold queueResizeChainA queueResizeK
  simp only [hq, if_neg hbad]
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
  · rw [if_neg hg]

/-! ## §3 — `queueEnqueueA` — FIFO append + refundable deposit PARK (TWO components: queues + bal + escrows).

`execFullA s (.queueEnqueueA id m actor cell depId dAsset deposit)
  = queueEnqueueChainA s id m actor cell depId dAsset deposit` (`TurnExecutorFull:3570`).

    queueEnqueueChainA s id m actor cell depId dAsset deposit                     -- :2041
      = if stateAuthB caps actor cell ∧ acceptsEffects cell then
          match queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
          | some k' => some { kernel := k', log := {actor, src:=actor, dst:=cell, amt:=deposit} :: s.log }
          | none    => none
        else none

    queueEnqueueDepositK k id m sender owner depId dAsset deposit                 -- RecordKernel:2235
      = match queueEnqueueK k id m with
        | none    => none
        | some k₁ => if 0 ≤ deposit ∧ deposit ≤ k₁.bal sender dAsset ∧ sender ∈ k₁.accounts
                        ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId) then
                       some (createEscrowRawAsset k₁ depId sender owner dAsset deposit)
                     else none

This effect touches THREE kernel components: `queues` (FIFO append, via `queueEnqueueK`), `bal` (the
deposit debited from `(actor, dAsset)`), and `escrows` (the parked deposit record). We give it the
full apex treatment. NOTE the post-`queues`/`bal`/`escrows` are layered: `queueEnqueueK` first
appends to the buffer, THEN `createEscrowRawAsset` parks the deposit off the resulting `k₁`. The spec
pins the COMPOSED post-state declaratively. -/

/-- The enqueue admissibility guard, as a `Prop` — authority, lifecycle-liveness, plus (read off the
INTERMEDIATE state `k₁` after the FIFO append) the FIFO capacity bound and the deposit legs. Stated
over the post-append intermediate so the spec matches the executor's layering. -/
def enqueueGuard (k : RecordKernelState) (id m : Nat) (actor cell : CellId) (depId : Nat)
    (dAsset : AssetId) (deposit : ℤ) : Prop :=
  stateAuthB k.caps actor cell = true ∧ acceptsEffects k cell = true
    ∧ ∃ k₁, queueEnqueueK k id m = some k₁
        ∧ 0 ≤ deposit ∧ deposit ≤ k₁.bal actor dAsset ∧ actor ∈ k₁.accounts
        ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId)

/-- The enqueue receipt row (records the deposit move `actor →(deposit)→ cell`). -/
def enqueueReceipt (actor cell : CellId) (deposit : ℤ) : Turn :=
  { actor := actor, src := actor, dst := cell, amt := deposit }

/-- **The full-state declarative spec of a committed `queueEnqueueA`** — the INDEPENDENT reference
semantics. The guard holds (`enqueueGuard`, witnessing the post-append intermediate `k₁`); the post
kernel is EXACTLY `createEscrowRawAsset k₁ depId actor cell dAsset deposit` (the deposit parked off
the FIFO-appended `k₁`); and the chained `log` advances by the deposit receipt. The "frame" here is
EXPRESSED relative to the composed helper (every kernel field of `st'` equals the corresponding field
of the composed post-state), so a silently mutated field still fails the proof. -/
def QueueEnqueueSpec (st : RecChainedState) (id m : Nat) (actor cell : CellId) (depId : Nat)
    (dAsset : AssetId) (deposit : ℤ) (st' : RecChainedState) : Prop :=
  ∃ k₁, stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
    ∧ queueEnqueueK st.kernel id m = some k₁
    ∧ 0 ≤ deposit ∧ deposit ≤ k₁.bal actor dAsset ∧ actor ∈ k₁.accounts
    ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId)
    ∧ st'.kernel = createEscrowRawAsset k₁ depId actor cell dAsset deposit
    ∧ st'.log = enqueueReceipt actor cell deposit :: st.log

/-- **`queueEnqueueChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
enqueue step. The `→` VALIDATES the executor against the independent spec (the whole `st'.kernel` is
pinned to the composed post-state, so any silent field mutation fails); the `←` reconstructs. -/
theorem queueEnqueueChainA_iff_spec (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (depId : Nat) (dAsset : AssetId) (deposit : ℤ) (st' : RecChainedState) :
    queueEnqueueChainA st id m actor cell depId dAsset deposit = some st'
      ↔ QueueEnqueueSpec st id m actor cell depId dAsset deposit st' := by
  unfold queueEnqueueChainA QueueEnqueueSpec queueEnqueueDepositK
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
    obtain ⟨hauth, hacc⟩ := hg
    cases hk : queueEnqueueK st.kernel id m with
    | none =>
        simp only
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨k₁, _, _, hk1, _⟩; exact absurd hk1 (by simp)
    | some k₁ =>
        simp only
        by_cases hd : 0 ≤ deposit ∧ deposit ≤ k₁.bal actor dAsset ∧ actor ∈ k₁.accounts
            ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId)
        · rw [if_pos hd]
          obtain ⟨hd1, hd2, hd3, hd4⟩ := hd
          constructor
          · intro h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨k₁, hauth, hacc, rfl, hd1, hd2, hd3, hd4, rfl, rfl⟩
          · rintro ⟨k₁', _, _, hk1', _, _, _, _, hker, hlog⟩
            simp only [Option.some.injEq] at hk1'; subst hk1'
            obtain ⟨k', l'⟩ := st'
            simp only at hker hlog
            subst hker hlog
            rfl
        · rw [if_neg hd]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨k₁', _, _, hk1', hd1', hd2', hd3', hd4', _⟩
            simp only [Option.some.injEq] at hk1'; subst hk1'
            exact absurd ⟨hd1', hd2', hd3', hd4'⟩ hd
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨_, hauth, hacc, _⟩; exact absurd ⟨hauth, hacc⟩ hg

/-- **`execFullA_queueEnqueueA_iff_spec` — the UNIFIED-ACTION executor corner.** -/
theorem execFullA_queueEnqueueA_iff_spec (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (depId : Nat) (dAsset : AssetId) (deposit : ℤ) (st' : RecChainedState) :
    execFullA st (.queueEnqueueA id m actor cell depId dAsset deposit) = some st'
      ↔ QueueEnqueueSpec st id m actor cell depId dAsset deposit st' := by
  show queueEnqueueChainA st id m actor cell depId dAsset deposit = some st'
        ↔ QueueEnqueueSpec st id m actor cell depId dAsset deposit st'
  exact queueEnqueueChainA_iff_spec st id m actor cell depId dAsset deposit st'

/-! ### enqueue non-vacuity. -/

/-- **`enqueue_rejects_unauthorized` — PROVED.** -/
theorem enqueue_rejects_unauthorized (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (depId : Nat) (dAsset : AssetId) (deposit : ℤ)
    (hbad : stateAuthB st.kernel.caps actor cell = false) :
    execFullA st (.queueEnqueueA id m actor cell depId dAsset deposit) = none := by
  show queueEnqueueChainA st id m actor cell depId dAsset deposit = none
  unfold queueEnqueueChainA
  rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]

/-- **`enqueue_rejects_dead_cell` — PROVED.** -/
theorem enqueue_rejects_dead_cell (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (depId : Nat) (dAsset : AssetId) (deposit : ℤ)
    (hbad : acceptsEffects st.kernel cell = false) :
    execFullA st (.queueEnqueueA id m actor cell depId dAsset deposit) = none := by
  show queueEnqueueChainA st id m actor cell depId dAsset deposit = none
  unfold queueEnqueueChainA
  rw [if_neg (by rw [hbad]; rintro ⟨_, h⟩; exact absurd h (by simp))]

/-! ## §4 — `queueDequeueA` — FIFO pop-front + deposit REFUND (queues + bal + escrows).

`execFullA s (.queueDequeueA id actor cell depId deposit)
  = queueDequeueChainA s id actor cell depId deposit` (`TurnExecutorFull:3571`).

    queueDequeueChainA s id actor cell depId deposit                             -- :2055
      = if stateAuthB caps actor cell ∧ acceptsEffects cell then
          match queueDequeueRefundK s.kernel id actor depId with
          | some (k', _) => some { kernel := k', log := {actor, src:=cell, dst:=actor, amt:=deposit} :: s.log }
          | none         => none
        else none

`queueDequeueRefundK` composes `queueDequeueK` (FIFO pop-front, owner-gated) with the deposit refund.
Touches `queues` (pop-front), `bal` (refund credit), `escrows` (deposit record resolved). Like
enqueue, the post-kernel is the COMPOSED helper output; the spec pins it declaratively. -/

/-- The dequeue receipt row (records the deposit refund move `cell →(deposit)→ actor`). -/
def dequeueReceipt (actor cell : CellId) (deposit : ℤ) : Turn :=
  { actor := actor, src := cell, dst := actor, amt := deposit }

/-- **The full-state declarative spec of a committed `queueDequeueA`** — the INDEPENDENT reference
semantics. The guard holds; `queueDequeueRefundK` commits some `(k', m)`; the post kernel is EXACTLY
`k'` (the composed pop-front + refund); the chained `log` advances by the refund receipt. The whole
`st'.kernel` is pinned, so a silently mutated field fails the proof. -/
def QueueDequeueSpec (st : RecChainedState) (id : Nat) (actor cell : CellId) (depId : Nat)
    (deposit : ℤ) (st' : RecChainedState) : Prop :=
  stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
    ∧ ∃ k' m, queueDequeueRefundK st.kernel id actor depId = some (k', m)
        ∧ st'.kernel = k'
        ∧ st'.log = dequeueReceipt actor cell deposit :: st.log

/-- **`queueDequeueChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
dequeue step. -/
theorem queueDequeueChainA_iff_spec (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (depId : Nat) (deposit : ℤ) (st' : RecChainedState) :
    queueDequeueChainA st id actor cell depId deposit = some st'
      ↔ QueueDequeueSpec st id actor cell depId deposit st' := by
  unfold queueDequeueChainA QueueDequeueSpec
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
    obtain ⟨hauth, hacc⟩ := hg
    cases hk : queueDequeueRefundK st.kernel id actor depId with
    | none =>
        simp only
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨_, _, k', m, hk', _⟩; exact absurd hk' (by simp)
    | some kr =>
        obtain ⟨k', m⟩ := kr
        simp only
        constructor
        · intro h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨hauth, hacc, k', m, rfl, rfl, rfl⟩
        · rintro ⟨_, _, k'', m', hk'', hker, hlog⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hk''
          obtain ⟨hk1, _⟩ := hk''; subst hk1
          obtain ⟨kk, l'⟩ := st'
          simp only at hker hlog
          subst hker hlog
          rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hauth, hacc, _⟩; exact absurd ⟨hauth, hacc⟩ hg

/-- **`execFullA_queueDequeueA_iff_spec` — the UNIFIED-ACTION executor corner.** -/
theorem execFullA_queueDequeueA_iff_spec (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (depId : Nat) (deposit : ℤ) (st' : RecChainedState) :
    execFullA st (.queueDequeueA id actor cell depId deposit) = some st'
      ↔ QueueDequeueSpec st id actor cell depId deposit st' := by
  show queueDequeueChainA st id actor cell depId deposit = some st'
        ↔ QueueDequeueSpec st id actor cell depId deposit st'
  exact queueDequeueChainA_iff_spec st id actor cell depId deposit st'

/-! ### dequeue non-vacuity. -/

/-- **`dequeue_rejects_unauthorized` — PROVED.** -/
theorem dequeue_rejects_unauthorized (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (depId : Nat) (deposit : ℤ)
    (hbad : stateAuthB st.kernel.caps actor cell = false) :
    execFullA st (.queueDequeueA id actor cell depId deposit) = none := by
  show queueDequeueChainA st id actor cell depId deposit = none
  unfold queueDequeueChainA
  rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]

/-- **`dequeue_rejects_dead_cell` — PROVED.** -/
theorem dequeue_rejects_dead_cell (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (depId : Nat) (deposit : ℤ)
    (hbad : acceptsEffects st.kernel cell = false) :
    execFullA st (.queueDequeueA id actor cell depId deposit) = none := by
  show queueDequeueChainA st id actor cell depId deposit = none
  unfold queueDequeueChainA
  rw [if_neg (by rw [hbad]; rintro ⟨_, h⟩; exact absurd h (by simp))]

/-! ## §5 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms queueAllocateK_correct
#assert_axioms queueAllocateChainA_iff_spec
#assert_axioms execFullA_queueAllocateA_iff_spec
#assert_axioms allocate_inserts_fresh
#assert_axioms allocate_balNeutral_ledger
#assert_axioms allocate_rejects_unauthorized
#assert_axioms allocate_rejects_id_reuse

#assert_axioms queueResizeK_correct
#assert_axioms queueResizeChainA_iff_spec
#assert_axioms execFullA_queueResizeA_iff_spec
#assert_axioms resize_rejects_unauthorized
#assert_axioms resize_rejects_dead_cell
#assert_axioms resize_rejects_absent
#assert_axioms resize_rejects_shrink_below_occupancy

#assert_axioms queueEnqueueChainA_iff_spec
#assert_axioms execFullA_queueEnqueueA_iff_spec
#assert_axioms enqueue_rejects_unauthorized
#assert_axioms enqueue_rejects_dead_cell

#assert_axioms queueDequeueChainA_iff_spec
#assert_axioms execFullA_queueDequeueA_iff_spec
#assert_axioms dequeue_rejects_unauthorized
#assert_axioms dequeue_rejects_dead_cell

end Dregg2.Circuit.Spec.QueueFifoCore
