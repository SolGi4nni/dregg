/-
# Dregg2.Deos.StandingObligation — a recurring duty is discharged ONCE PER PERIOD, ON SCHEDULE, NEVER
EARLY OR SKIPPED (the standing-obligation house-capacity, grounded BY REUSE of the committed-heap
root + the StrictMonotonic cursor discipline).

`cell/src/obligation_standing.rs` is the Rust house-capacity: a cell that OWES `amount` to a
`beneficiary` every `period` blocks, starting at `start`. Each discharge advances a committed
`next_due` cursor by exactly one period, can only run once the schedule clock reaches the current due
block, and must pay exactly the committed amount. Its soundness is *forge/skip rejection*: no early
discharge, no double-discharge (one-shot per period), no over/under-discharge, and no silent skip (a
cell whose committed cursor lags the schedule is detectable).

This module is the Lean RUNG for that capacity, in the SAME shape the MEMBRANE / DERIVED-CELL /
SEALED-ESCROW rungs set (`docs/deos/HOUSE-CAPACITY-FRAMEWORK.md`): add the invariant leg, prove it
**by reuse** of an already-proven object — here BOTH `Substrate.Heap`'s sorted-Poseidon2 root (the
cursor is committed) AND the **StrictMonotonic** cursor discipline (the SAME monotone-slot law the
version/supply/nonce slots ride, `Dregg2.Exec.Program.evalSimple_strictMono_iff` /
`SimpleStateConstraint::StrictMonotonic`) — exhibit both-polarity `#guard` witnesses,
`#assert_all_clean`, and wire the Rust to it
(`cell/src/obligation_standing.rs::tests::invariant_matches_lean_rung`).

## What is proven — and what it REUSES (no obligation-local commitment, no new monotone law)

The schedule's terms digest, the `next_due` cursor, the discharged count, and the cumulative total
all live in reserved heap slots (the SAME `set_heap`/`compute_heap_root` sorted-Poseidon2 map
`cell/src/obligation_standing.rs` writes, folded into the canonical state commitment with NO VK
bump). A verifier holding the committed heap reads the cursor and gates each discharge. The rung
proves:

  * `opened_cursor` + `opened_discharge_accepts` (HONEST ROUND-TRIP) — an opened obligation commits
    `next_due = start`, against which the period-0 discharge (paid the exact amount, at/after the
    first due block) is accepted by the gate. Read-after-write is `Heap.hget_hset_self`; the cursor
    slot survives the other open-writes by `Heap.hget_hset_frame` (the ONE named `Poseidon2SpongeCR`
    floor).

  * **`cursor_strict_mono` + `advance_strictly_increases` (THE MONOTONE-CURSOR REUSE)** — the cursor
    `cursorAt start period k = start + k·period` is STRICTLY increasing in the period index (the
    `StrictMonotonic{next_due}` discipline: each discharge writes a cursor strictly greater than the
    prior). This is the same monotone-slot law the version/supply/nonce slots ride; here it is what
    makes a period ONE-SHOT.

  * `replay_rejected` (THE ONE-SHOT / NO-DOUBLE TOOTH) — after period 0 is discharged the cursor has
    advanced to `start + period`, so the gate's expected period is 1; a replay naming period 0 is
    REJECTED. `cell/src/obligation_standing.rs`'s `double_discharge_of_one_period_is_rejected`, as a
    consequence of the strict cursor advance.

  * `early_discharge_rejected` (THE NO-EARLY TOOTH) — a discharge whose presented clock is below the
    current period's due block is REJECTED. `early_discharge_is_rejected`.

  * `over_discharge_rejected` (THE NO-OVER/UNDER TOOTH) — a discharge whose amount differs from the
    committed schedule amount is REJECTED. `over_or_under_discharge_is_rejected`.

  * `behind_schedule_rejected` (THE NO-SILENT-SKIP / AUDIT TOOTH) — a cell whose committed
    discharged-count lags the number of periods the schedule says MUST be discharged by the audited
    clock is REJECTED. `behind_schedule_silent_skip_is_rejected`.

  * **`cursor_bound_in_root` / `count_bound_in_root` (THE HEAP REUSE KEYSTONE)** — equal committed
    roots ⟹ equal cursor AND equal discharged-count: a forge cannot present the honest root with a
    rewound cursor or a padded count. DIRECT instances of `Heap.root_binds_get` (the anti-ghost),
    under the one named `Poseidon2SpongeCR` floor. With it, `forged_cursor_moves_root`.

This is NOT new mathematics: the cursor is a committed scalar advancing under the existing
StrictMonotonic discipline, and the BINDING is the proven sorted-Poseidon2 root. The standing
obligation is a NAMING of "a committed-heap binding whose `next_due` slot advances one period per
one-shot discharge" — exactly as the escrow is a naming of a once-only two-leg swap.

## The circuit weld (STAGED, VK-risk-free) — §6b

§3–§6 ground the EXECUTOR-witnessed invariant. §6b binds "due ∧ exact ∧ cursor advanced by one
period" into what a LIGHT CLIENT verifying a *batch* witnesses — via the manifest-in-public-inputs +
off-AIR re-evaluation vehicle the sealed-escrow weld (`SealedEscrow.lean` §6) and the temporal
caveats (`circuit/src/effect_vm/verify.rs` tags 13–16) already ride. The `DischargeGate` over a
(before, after) committed-heap transition is carried as a new slot-caveat tag
(`SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION = 18`) in PUBLIC INPUTS and re-evaluated against the bound
`state_before`/`state_after` views — the AIR constraint polynomials (the VK bytes) are UNCHANGED, so
this is a verifier-code epoch, not a proving-key rotation. The teeth here are BOTH the *executor*
teeth (§3–§6) AND the *light-client* gate (§6b); the Rust arm is the gate's mechanical shadow. Full
staging: `docs/deos/DISCHARGE-OBLIGATION-WELD-DESIGN.md`,
`metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`.

## Axiom hygiene

`#assert_all_clean` at the close. Crypto enters ONLY as the named `Poseidon2SpongeCR` hypothesis (the
cap-root floor the heap carries), never as an axiom. NO core/heap edit — every binding is the REAL
`Substrate.Heap.hset`/`hget` and the root is the REAL `Substrate.Heap.root`.
-/
import Dregg2.Substrate.Heap
import Dregg2.Tactics

namespace Dregg2.Deos.StandingObligation

open Dregg2.Substrate.Heap
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — the schedule (the deterministic clock the binder and verifier BOTH compute). -/

/-- The sealed terms of a standing obligation — the Lean image of
`cell/src/obligation_standing.rs::ObligationTerms` (the parties/asset are off-circuit identity; the
rung carries the scalars the schedule clock reads). `count = 0` means unbounded. -/
structure Terms where
  /-- The amount owed each period. Well-formed terms have `amount > 0`. -/
  amount : ℤ
  /-- The period length in blocks. Well-formed terms have `period > 0`. -/
  period : ℤ
  /-- The block at which period `0` falls due. -/
  start : ℤ
  /-- The bounded number of periods, or `0` for unbounded. -/
  count : ℤ
deriving DecidableEq, Repr

/-- Well-formedness (`ObligationTerms::is_well_formed`): positive amount/period. -/
abbrev Terms.wf (t : Terms) : Prop := 0 < t.amount ∧ 0 < t.period

/-- **`cursorAt t k`** — the `next_due` cursor after `k` periods discharged: `start + k·period`. The
committed cursor takes exactly these values; its strict monotonicity in `k` is the one-shot heart. -/
def cursorAt (t : Terms) (k : ℤ) : ℤ := t.start + k * t.period

/-- **`dueBlock t k`** — the block at which period `k` falls due (`ObligationTerms::due_block`). For
the schedule clock this equals `cursorAt t k`. -/
def dueBlock (t : Terms) (k : ℤ) : ℤ := t.start + k * t.period

/-- **`expectedPeriod t nextDue`** — which period the committed cursor expects next, DERIVED from the
cursor (not trusted from the step): `(next_due − start) / period`. The Rust `expected_period`. -/
def expectedPeriod (t : Terms) (nextDue : ℤ) : ℤ := (nextDue - t.start) / t.period

/-- **`periodsDueBy t clock`** — how many periods MUST be discharged by `clock`
(`ObligationTerms::periods_due_by`): the schedule's ground truth the audit compares against. -/
def periodsDueBy (t : Terms) (clock : ℤ) : ℤ :=
  if clock < t.start then 0
  else
    let due := (clock - t.start) / t.period + 1
    if 0 < t.count ∧ t.count < due then t.count else due

/-- A discharge step presented to the verifier (`cell/src/obligation_standing.rs::Discharge`). -/
structure Step where
  /-- The period the obligor asserts it is discharging. -/
  periodIndex : ℤ
  /-- The amount the obligor asserts it is paying. -/
  amount : ℤ
  /-- The schedule clock at the moment of discharge. -/
  clock : ℤ
deriving DecidableEq, Repr

/-! ## §2 — the obligation as committed heap slots (REUSE of `Substrate.Heap`). -/

/-- The reserved obligation collection (`OBLIGATION_COLL = 0x0_B11_6A`). -/
def obligColl : ℤ := 725354
/-- Heap key holding the terms digest (`KEY_TERMS_DIGEST`). -/
def keyDigest : ℤ := 0
/-- Heap key holding the `next_due` cursor (`KEY_NEXT_DUE`). -/
def keyNextDue : ℤ := 1
/-- Heap key holding the discharged count (`KEY_DISCHARGED_COUNT`). -/
def keyCount : ℤ := 2
/-- Heap key holding the cumulative discharged total (`KEY_DISCHARGED_TOTAL`). -/
def keyTotal : ℤ := 3

/-- The committed `next_due` cursor bound in a cell's heap. -/
def boundCursor (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h obligColl keyNextDue

/-- The committed discharged count bound in a cell's heap. -/
def boundCount (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h obligColl keyCount

/-- The committed cumulative discharged total bound in a cell's heap. -/
def boundTotal (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h obligColl keyTotal

/-- **`openObl hash h digest t`** — seal the terms and initialize the cursor to the first due block,
zero discharged. The Lean image of `cell/src/obligation_standing.rs::open_obligation`. -/
def openObl (hash : List ℤ → ℤ) (h : FeltHeap) (digest : ℤ) (t : Terms) : FeltHeap :=
  hset hash (hset hash (hset hash (hset hash h obligColl keyDigest digest)
    obligColl keyNextDue t.start) obligColl keyCount 0) obligColl keyTotal 0

/-- **`advance hash h t cursor count total`** — the discharge write: advance the cursor by one
period, bump the count, add the amount. The Lean image of `cell/src/obligation_standing.rs::discharge`'s
mutation (given the prior committed `cursor`/`count`/`total`). -/
def advance (hash : List ℤ → ℤ) (h : FeltHeap) (t : Terms) (cursor count total : ℤ) : FeltHeap :=
  hset hash (hset hash (hset hash h obligColl keyNextDue (cursor + t.period))
    obligColl keyCount (count + 1)) obligColl keyTotal (total + t.amount)

/-! ## §3 — the verification core (the forge-detector, as a predicate).

`DischargeOk` is the Lean image of `ObligationState::check_discharge`: the honest-accept path and
every early/double/over-discharge reject consult THIS. `AuditOk` is `ObligationState::audit`. -/

/-- **The discharge gate.** Given the committed `nextDue` cursor, the step accepts iff: the
obligation is not completed (bounded count not yet reached), the step names exactly the cursor's
expected period (one-shot / no-skip), the clock has reached that period's due block (not early), and
the amount equals the committed schedule (no over/under). -/
abbrev DischargeOk (t : Terms) (nextDue : ℤ) (s : Step) : Prop :=
  (t.count = 0 ∨ expectedPeriod t nextDue < t.count) ∧
  s.periodIndex = expectedPeriod t nextDue ∧
  dueBlock t (expectedPeriod t nextDue) ≤ s.clock ∧
  s.amount = t.amount

/-- **The audit gate.** The committed discharged-count is not behind the number of periods the
schedule demands by `clock`. -/
abbrev AuditOk (t : Terms) (committedCount clock : ℤ) : Prop := periodsDueBy t clock ≤ committedCount

/-! ## §4 — THE MONOTONE-CURSOR REUSE: the cursor strictly increases per discharge.

The `next_due` cursor advances under the SAME StrictMonotonic-slot law the version/supply/nonce
slots ride (`Dregg2.Exec.Program.evalSimple_strictMono_iff`): each discharge writes a value strictly
greater than the prior. Over the schedule this is `cursorAt t k = start + k·period` STRICTLY
increasing in `k` — and THAT is what makes a period one-shot. -/

/-- **THE STRICT-MONOTONE CURSOR.** On well-formed terms (`period > 0`), the cursor `cursorAt t k`
is strictly increasing in the period index `k`. The version/supply StrictMonotonic discipline,
instantiated on the obligation's `next_due` slot. -/
theorem cursor_strict_mono (t : Terms) (hwf : t.wf) {j k : ℤ} (hjk : j < k) :
    cursorAt t j < cursorAt t k := by
  unfold cursorAt
  have hp : (0 : ℤ) < t.period := hwf.2
  have : j * t.period < k * t.period := mul_lt_mul_of_pos_right hjk hp
  omega

/-- **THE STRICT ADVANCE.** One discharge advances the cursor strictly: `nextDue < nextDue + period`
(`period > 0`). The per-step face of `cursor_strict_mono` — the StrictMonotonic write. -/
theorem advance_strictly_increases (t : Terms) (hwf : t.wf) (nextDue : ℤ) :
    nextDue < nextDue + t.period := by
  have hp : (0 : ℤ) < t.period := hwf.2
  omega

/-- After one discharge from the opening cursor `start`, the cursor is `start + period`, whose
expected period is `1` — so the freshly-discharged period `0` is no longer the cursor's expectation.
The arithmetic heart of the one-shot tooth (the strict advance, read through `expectedPeriod`). -/
theorem expectedPeriod_after_one (t : Terms) (hwf : t.wf) :
    expectedPeriod t (t.start + t.period) = 1 := by
  unfold expectedPeriod
  have hp : t.period ≠ 0 := ne_of_gt hwf.2
  have : t.start + t.period - t.start = t.period := by ring
  rw [this, Int.ediv_self hp]

theorem expectedPeriod_open (t : Terms) : expectedPeriod t t.start = 0 := by
  unfold expectedPeriod
  simp

/-! ## §5 — THE HONEST ROUND-TRIP + THE TEETH. -/

/-- **HONEST ROUND-TRIP (cursor).** An opened obligation commits `next_due = start`. The cursor slot
survives the later open-writes (count, total) by `Heap.hget_hset_frame` (the named
`Poseidon2SpongeCR` floor), then reads back by `Heap.hget_hset_self`. -/
theorem opened_cursor (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (digest : ℤ) (t : Terms) :
    boundCursor hash (openObl hash h digest t) = some t.start := by
  show hget hash (openObl hash h digest t) obligColl keyNextDue = some t.start
  unfold openObl
  rw [hget_hset_frame hash hCR _ obligColl keyTotal obligColl keyNextDue 0 (by decide),
    hget_hset_frame hash hCR _ obligColl keyCount obligColl keyNextDue 0 (by decide)]
  exact hget_hset_self hash _ obligColl keyNextDue t.start

/-- **HONEST ROUND-TRIP (count).** An opened obligation commits a discharged-count of `0`. -/
theorem opened_count (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (digest : ℤ) (t : Terms) :
    boundCount hash (openObl hash h digest t) = some 0 := by
  show hget hash (openObl hash h digest t) obligColl keyCount = some 0
  unfold openObl
  rw [hget_hset_frame hash hCR _ obligColl keyTotal obligColl keyCount 0 (by decide)]
  exact hget_hset_self hash _ obligColl keyCount 0

/-- **HONEST DISCHARGE ACCEPTS** (non-vacuity). At the opening cursor (`start`), a period-0 discharge
paying the exact amount at/after the first due block is accepted by the gate. The live path the teeth
close. -/
theorem opened_discharge_accepts (t : Terms) (s : Step)
    (hidx : s.periodIndex = 0) (hclk : t.start ≤ s.clock) (hamt : s.amount = t.amount)
    (hopen : t.count = 0 ∨ 0 < t.count) :
    DischargeOk t t.start s := by
  refine ⟨?_, ?_, ?_, hamt⟩
  · rw [expectedPeriod_open]; rcases hopen with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rw [expectedPeriod_open]; exact hidx
  · rw [expectedPeriod_open]; show dueBlock t 0 ≤ s.clock
    unfold dueBlock; simpa using hclk

/-- **THE ONE-SHOT / NO-DOUBLE TOOTH.** After period 0 is discharged the cursor is `start + period`,
whose expected period is `1`; a replay naming period `0` is REJECTED (`0 ≠ 1`). The Rust
`double_discharge_of_one_period_is_rejected`, as a consequence of the strict cursor advance. -/
theorem replay_rejected (t : Terms) (hwf : t.wf) (s : Step) (hidx : s.periodIndex = 0) :
    ¬ DischargeOk t (t.start + t.period) s := by
  intro hok
  have hexp := hok.2.1
  rw [expectedPeriod_after_one t hwf, hidx] at hexp
  exact absurd hexp (by decide)

/-- **THE NO-EARLY TOOTH.** A discharge whose presented clock is below the current period's due block
is REJECTED. The Rust `early_discharge_is_rejected`, as a theorem. -/
theorem early_discharge_rejected (t : Terms) (nextDue : ℤ) (s : Step)
    (hearly : s.clock < dueBlock t (expectedPeriod t nextDue)) :
    ¬ DischargeOk t nextDue s := by
  intro hok
  exact absurd hok.2.2.1 (not_le.mpr hearly)

/-- **THE NO-OVER/UNDER TOOTH.** A discharge whose amount differs from the committed schedule amount
is REJECTED. The Rust `over_or_under_discharge_is_rejected`, as a theorem. -/
theorem over_discharge_rejected (t : Terms) (nextDue : ℤ) (s : Step) (hne : s.amount ≠ t.amount) :
    ¬ DischargeOk t nextDue s := by
  intro hok
  exact hne hok.2.2.2

/-- **THE NO-SILENT-SKIP / AUDIT TOOTH.** A cell whose committed discharged-count lags the number of
periods the schedule demands by the audited clock is REJECTED. The Rust
`behind_schedule_silent_skip_is_rejected`, as a theorem. -/
theorem behind_schedule_rejected (t : Terms) (committedCount clock : ℤ)
    (hbehind : committedCount < periodsDueBy t clock) :
    ¬ AuditOk t committedCount clock := by
  intro hok
  exact absurd hok (not_le.mpr hbehind)

/-! ## §6 — THE HEAP REUSE KEYSTONE: the cursor is bound into the committed root.

The `next_due` cursor and discharged-count ride the SAME sorted-Poseidon2 `Heap.root` the cap crown
proves binds. So equal committed roots open to the SAME cursor and count — a forge cannot present the
honest root with a rewound cursor (re-opening a discharged period) or a padded count. DIRECT
instances of `Heap.root_binds_get` (the anti-ghost), under the one named `Poseidon2SpongeCR` floor. -/

/-- **THE REUSE KEYSTONE (cursor).** Equal roots ⟹ equal committed cursor. Proven by REUSE of
`Heap.root_binds_get` — no obligation-local commitment. -/
theorem cursor_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) :
    boundCursor hash h₁ = boundCursor hash h₂ :=
  root_binds_get hash hCR hroot obligColl keyNextDue

/-- **THE REUSE KEYSTONE (count).** Equal roots ⟹ equal discharged-count — a forge cannot pad the
count while keeping the honest root. -/
theorem count_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) :
    boundCount hash h₁ = boundCount hash h₂ :=
  root_binds_get hash hCR hroot obligColl keyCount

/-- **THE ANTI-GHOST.** A forged cell whose committed cursor differs from the honest one CANNOT keep
the honest root — it must publish a different root (where the one-shot tooth then bites). The
contrapositive of `cursor_bound_in_root`. -/
theorem forged_cursor_moves_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hne : boundCursor hash h₁ ≠ boundCursor hash h₂) :
    root hash h₁ ≠ root hash h₂ :=
  fun hroot => hne (cursor_bound_in_root hash hCR hroot)

/-- **THE REUSE KEYSTONE (total).** Equal roots ⟹ equal committed cumulative total — a forge
cannot under-report (or pad) the discharged total while keeping the honest root. DIRECT instance of
`Heap.root_binds_get`, the same anti-ghost the cursor/count keystones ride. -/
theorem total_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) :
    boundTotal hash h₁ = boundTotal hash h₂ :=
  root_binds_get hash hCR hroot obligColl keyTotal

/-! ## §6b — THE CIRCUIT-WELD RUNG (STAGED): per-period discharge a LIGHT CLIENT witnesses.

§3–§6 are the EXECUTOR-witnessed teeth: a verifier holding the committed heap rejects an early,
double, over/under, or skipped discharge out of band. THIS section is the LIGHT-CLIENT rung — the
soundness an off-AIR `DischargeObligation` manifest entry (a new slot/heap caveat tag carried in
PUBLIC INPUTS, re-evaluated against the bound `state_before`/`state_after` committed-heap views, with
the AIR constraint polynomials — the VK bytes — UNCHANGED) inherits, exactly as the temporal-caveat
verifier arms (`circuit/src/effect_vm/verify.rs` tags 13–16) inherit `temporalStateStepGuarded` and
the sealed-escrow weld (tag 17) inherits `SettleGate`. The full staging is
`docs/deos/DISCHARGE-OBLIGATION-WELD-DESIGN.md`.

The gate is over a (before, after) PAIR of committed heaps — the genuine kernel TRANSITION a batch
proves — not a single state. A satisfying witness FORCES the schedule shape: the discharge is DUE
(the schedule clock has reached the committed cursor's due block), the cursor ADVANCES by exactly one
period, and the discharged total advances by EXACTLY the schedule amount. A forged EARLY discharge
(clock below the due block), a WRONG-AMOUNT discharge, or a NON-ADVANCED cursor (a replay that does
not move the one-shot cursor) is INEXPRESSIBLE — it fails the gate — so the per-period discipline is
light-client-witnessed, not re-run out of band. The verdict is fixed by the committed roots (the
light-client tooth), so a forger must move a root where §6 bites.

The witnessed before-values `cb` (cursor) and `tb` (total) are the slot views the manifest reads
from the cell's committed `next_due`/total slots (stage (a) field-mirror of the
`DISCHARGE-OBLIGATION-WELD-DESIGN.md`); `clock` is the batch's block height, against which the due
block is compared. -/

/-- **READ-BACK after one discharge (cursor).** The discharge write advances the committed cursor by
one period; the cursor slot survives the later total/count writes by `Heap.hget_hset_frame`. -/
theorem advance_cursor (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (t : Terms) (cursor count total : ℤ) :
    boundCursor hash (advance hash h t cursor count total) = some (cursor + t.period) := by
  show hget hash (advance hash h t cursor count total) obligColl keyNextDue = some (cursor + t.period)
  unfold advance
  rw [hget_hset_frame hash hCR _ obligColl keyTotal obligColl keyNextDue (total + t.amount) (by decide),
    hget_hset_frame hash hCR _ obligColl keyCount obligColl keyNextDue (count + 1) (by decide)]
  exact hget_hset_self hash _ obligColl keyNextDue (cursor + t.period)

/-- **READ-BACK after one discharge (total).** The discharge write adds exactly the schedule amount
to the committed total — the outermost write, read back directly by `Heap.hget_hset_self`. -/
theorem advance_total (hash : List ℤ → ℤ)
    (h : FeltHeap) (t : Terms) (cursor count total : ℤ) :
    boundTotal hash (advance hash h t cursor count total) = some (total + t.amount) := by
  show hget hash (advance hash h t cursor count total) obligColl keyTotal = some (total + t.amount)
  unfold advance
  exact hget_hset_self hash _ obligColl keyTotal (total + t.amount)

/-- **The discharge gate over a TRANSITION.** The Lean image of the off-AIR `DischargeObligation`
manifest re-evaluation: read the committed cursor (`cb`) and total (`tb`) from the bound `before`
view and require the discharge is DUE (clock reached the cursor's due block), the `after` cursor
ADVANCES by exactly one period, and the `after` total advances by EXACTLY the schedule amount. The
conjunction in ONE entry is what binds per-period discipline; a per-slot-independent caveat could not
force the joint due ∧ advanced ∧ exact shape. -/
abbrev DischargeGate (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap) (clock cb tb : ℤ) :
    Prop :=
  boundCursor hash before = some cb ∧
  boundTotal  hash before = some tb ∧
  dueBlock t (expectedPeriod t cb) ≤ clock ∧
  boundCursor hash after  = some (cb + t.period) ∧
  boundTotal  hash after  = some (tb + t.amount)

/-- **HONEST DISCHARGE PASSES THE GATE** (non-vacuity, accept polarity). The genuine kernel
transition — a committed cursor/total, then `advance` — satisfies the gate whenever the clock has
reached the due block. Without this the rung would be vacuous (true by no-witness). -/
theorem discharge_passes_gate (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (h : FeltHeap)
    (t : Terms) (cursor count total clock : ℤ)
    (hcur : boundCursor hash h = some cursor) (htot : boundTotal hash h = some total)
    (hdue : dueBlock t (expectedPeriod t cursor) ≤ clock) :
    DischargeGate hash t h (advance hash h t cursor count total) clock cursor total :=
  ⟨hcur, htot, hdue, advance_cursor hash hCR h t cursor count total,
    advance_total hash h t cursor count total⟩

/-- **THE DUE ∧ EXACT ∧ ADVANCED TOOTH.** A satisfying gate witness FORCES the schedule shape: the
discharge was due, the cursor advanced exactly one period, and the total advanced by exactly the
schedule amount. There is no accepting witness that skips the due block, under/over-pays, or leaves
the one-shot cursor un-advanced. -/
theorem discharge_gate_forces_due_exact (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap)
    (clock cb tb : ℤ) (hgate : DischargeGate hash t before after clock cb tb) :
    boundCursor hash before = some cb ∧
      dueBlock t (expectedPeriod t cb) ≤ clock ∧
      boundCursor hash after = some (cb + t.period) ∧
      boundTotal hash after = some (tb + t.amount) :=
  ⟨hgate.1, hgate.2.2.1, hgate.2.2.2.1, hgate.2.2.2.2⟩

/-- **THE NO-EARLY TOOTH.** A discharge whose schedule clock is BELOW the current period's due block
is REFUSED by the gate. Paying before due is INEXPRESSIBLE in-circuit — the light-client face of
§5's `early_discharge_rejected`. -/
theorem discharge_gate_early_rejected (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap)
    (clock cb tb : ℤ) (hearly : clock < dueBlock t (expectedPeriod t cb)) :
    ¬ DischargeGate hash t before after clock cb tb := by
  intro hgate
  exact absurd hgate.2.2.1 (not_le.mpr hearly)

/-- **THE NO-WRONG-AMOUNT TOOTH.** A discharge whose committed `after` total does NOT advance by
exactly the schedule amount (over- or under-pay) is REFUSED: the gate requires
`after total = before total + amount`. The light-client face of §5's `over_discharge_rejected`. -/
theorem wrong_amount_rejected (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap)
    (clock cb tb wrong : ℤ) (hafter : boundTotal hash after = some wrong)
    (hne : wrong ≠ tb + t.amount) :
    ¬ DischargeGate hash t before after clock cb tb := by
  intro hgate
  have h := hgate.2.2.2.2
  rw [hafter] at h
  exact hne (Option.some.inj h)

/-- **THE NO-NON-ADVANCED TOOTH.** A discharge whose committed `after` cursor does NOT advance by one
period (a replay that leaves the one-shot cursor where it was) is REFUSED: the gate requires
`after cursor = before cursor + period`. The light-client face of §5's `replay_rejected` (the strict
cursor advance). -/
theorem cursor_not_advanced_rejected (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap)
    (clock cb tb stuck : ℤ) (hafter : boundCursor hash after = some stuck)
    (hne : stuck ≠ cb + t.period) :
    ¬ DischargeGate hash t before after clock cb tb := by
  intro hgate
  have h := hgate.2.2.2.1
  rw [hafter] at h
  exact hne (Option.some.inj h)

/-- **THE LIGHT-CLIENT TOOTH (root-transport).** The gate verdict is FIXED by the committed ROOTS of
the before/after views — so a light client that checks the gate against the public-input-bound
before/after roots reads the GENUINE verdict; a forger presenting fake cursor/total slots must MOVE a
root (where §6's binding bites). Equal-root before/after views give the same gate verdict. Proven by
REUSE of `cursor_bound_in_root` / `total_bound_in_root` — no obligation-local commitment, the one
named `Poseidon2SpongeCR` floor. -/
theorem discharge_gate_root_bound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {before before' after after' : FeltHeap} (t : Terms) (clock cb tb : ℤ)
    (hb : root hash before = root hash before') (ha : root hash after = root hash after')
    (hgate : DischargeGate hash t before after clock cb tb) :
    DischargeGate hash t before' after' clock cb tb := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hgate
  refine ⟨?_, ?_, h3, ?_, ?_⟩
  · rw [← cursor_bound_in_root hash hCR hb]; exact h1
  · rw [← total_bound_in_root hash hCR hb]; exact h2
  · rw [← cursor_bound_in_root hash hCR ha]; exact h4
  · rw [← total_bound_in_root hash hCR ha]; exact h5

/-! ## §7 — NON-VACUITY TEETH (`#guard`): the schedule invariant BITES, both polarities.

Computed on the reference sponge (`Substrate.Heap.refSponge`). The sample schedule (the Rust
`sample_terms`): owe 50 every 100 blocks from block 1000, unbounded. -/

section Witnesses

/-- The Rust `sample_terms`: amount 50, period 100, start 1000, unbounded. -/
private def t0 : Terms := ⟨50, 100, 1000, 0⟩

theorem t0_wf : t0.wf := by decide

-- THE SCHEDULE CLOCK: period 0 due at 1000, period 1 at 1100, period 2 at 1200; the cursor advances
-- by exactly one period, strictly. (`cursorAt` / `expectedPeriod` compute the Rust ground truth.)
#guard cursorAt t0 0 == 1000
#guard cursorAt t0 1 == 1100
#guard cursorAt t0 2 == 1200
#guard expectedPeriod t0 1000 == 0
#guard expectedPeriod t0 1100 == 1
#guard periodsDueBy t0 999 == 0      -- nothing due before start
#guard periodsDueBy t0 1000 == 1     -- period 0 due exactly at start
#guard periodsDueBy t0 1250 == 3     -- periods 0,1,2 due by 1250

-- HONEST: at the opening cursor 1000, a period-0 discharge of exactly 50 at clock 1000 accepts.
#guard decide (DischargeOk t0 1000 ⟨0, 50, 1000⟩)
-- THE ONE-SHOT: after the cursor advances to 1100, a replay naming period 0 is refused (cursor
-- expects period 1 now).
#guard !decide (DischargeOk t0 1100 ⟨0, 50, 1000⟩)
-- THE NO-EARLY: a discharge one block early (clock 999, due 1000) is refused.
#guard !decide (DischargeOk t0 1000 ⟨0, 50, 999⟩)
-- THE NO-OVER/UNDER: over-discharge (9999) and under-discharge (1) are both refused.
#guard !decide (DischargeOk t0 1000 ⟨0, 9999, 1000⟩)
#guard !decide (DischargeOk t0 1000 ⟨0, 1, 1000⟩)
-- THE NO-SILENT-SKIP: by clock 1250 the schedule demands 3 periods; a cell that committed only 1 is
-- behind (audit refuses); an on-schedule cell (3 committed) passes the SAME audit.
#guard !decide (AuditOk t0 1 1250)
#guard decide (AuditOk t0 3 1250)

-- THE HEAP BINDING (anti-ghost shadow): opening commits cursor=start; advancing one period MOVES
-- the committed root (a light client sees the cursor advance, so a rewind cannot hide).
private def opened : FeltHeap := openObl refSponge [] 777 t0
private def stepped : FeltHeap := advance refSponge opened t0 1000 0 0
#guard boundCursor refSponge opened == some 1000
#guard boundCount refSponge opened == some 0
#guard boundCursor refSponge stepped == some 1100
#guard boundCount refSponge stepped == some 1
#guard (root refSponge stepped != root refSponge opened)

-- §6b THE CIRCUIT-WELD GATE (the `DischargeObligation` manifest re-evaluation), both polarities.
-- The honest transition opened (cursor 1000, total 0) → stepped (cursor 1100, total 50): the period
-- the schedule says is due at block 1000, advancing the cursor one period and the total by 50.
-- HONEST: at clock 1000 (period 0 due at 1000) the due ∧ advanced ∧ exact discharge passes.
#guard decide (DischargeGate refSponge t0 opened stepped 1000 1000 0)
-- NO-EARLY: one block early (clock 999 < due block 1000) fails the gate.
#guard !decide (DischargeGate refSponge t0 opened stepped 999 1000 0)
-- NO-WRONG-AMOUNT: an `after` total that did not advance by exactly 50 (forged to 9999) fails.
private def wrongAmt : FeltHeap := hset refSponge stepped obligColl keyTotal 9999
#guard boundTotal refSponge wrongAmt == some 9999
#guard !decide (DischargeGate refSponge t0 opened wrongAmt 1000 1000 0)
-- NO-NON-ADVANCED: an `after` cursor reverted to 1000 (the one-shot cursor not advanced) fails.
private def notAdvanced : FeltHeap := hset refSponge stepped obligColl keyNextDue 1000
#guard boundCursor refSponge notAdvanced == some 1000
#guard !decide (DischargeGate refSponge t0 opened notAdvanced 1000 1000 0)

end Witnesses

/-! ## §8 — Axiom hygiene. -/

#assert_all_clean [
  cursor_strict_mono,
  advance_strictly_increases,
  expectedPeriod_after_one,
  expectedPeriod_open,
  opened_cursor,
  opened_count,
  opened_discharge_accepts,
  replay_rejected,
  early_discharge_rejected,
  over_discharge_rejected,
  behind_schedule_rejected,
  cursor_bound_in_root,
  count_bound_in_root,
  forged_cursor_moves_root,
  total_bound_in_root,
  advance_cursor,
  advance_total,
  discharge_passes_gate,
  discharge_gate_forces_due_exact,
  discharge_gate_early_rejected,
  wrong_amount_rejected,
  cursor_not_advanced_rejected,
  discharge_gate_root_bound
]

end Dregg2.Deos.StandingObligation
