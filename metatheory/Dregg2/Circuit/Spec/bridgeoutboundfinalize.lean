/-
# Dregg2.Circuit.Spec.bridgeoutboundfinalize — INDEPENDENT full-state spec + executor⟺spec for the
  BRIDGE-OUTBOUND-FINALIZE effect family (`bridgeFinalizeA`).

This is the cross-chain OUTFLOW analogue of `Dregg2/Circuit/Transfer.lean`'s `TransferSpec` /
`recKExec_iff_spec` / `recTransfer_correct`, written from scratch as an INDEPENDENT declarative
reference and proved EXACTLY met by the real executor, both ways. It mirrors the sibling
`Dregg2/Circuit/Spec/escrowholdingrelease.lean`'s `RecChainedState`-level discipline.

## The family

The full executor `execFullA` (`TurnExecutorFull.lean:3551`) dispatches the single constructor to the
chained per-asset bridge-finalize primitive `bridgeFinalizeChainA`:

    execFullA s (.bridgeFinalizeA id actor asset amount)
      = bridgeFinalizeChainA s id actor asset amount

A bridge FINALIZE models the §8 confirmation arriving from the OTHER chain: the parked bridge value
genuinely LEFT for the other chain — a disclosed OUTFLOW (a burn). It is the honest contrast with an
escrow RELEASE (which credits a recipient, conserving): finalize is a NO-credit resolve, so the
COMBINED per-asset measure DROPS by the bridged `amount`.

## The executor primitive, unfolded (read off the CODE)

`bridgeFinalizeChainA s id actor asset amount` (`TurnExecutorFull.lean:2810`):

    if bridgeAuthOK s.kernel id actor then
      match bridgeFinalizeKAsset s.kernel id asset amount with
      | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
      | none    => none
    else none

`bridgeAuthOK k id actor` (`TurnExecutorFull.lean:2801`) — the AUTHORITY gate (re-audit hole #4):

    match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
    | some r => r.bridge == true && r.creator == actor
    | none   => false

`bridgeFinalizeKAsset k id asset amount` (`RecordKernel.lean:1737`) — the RECEIPT-MATCH gate:

    match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
    | some r => if r.bridge = true ∧ r.asset = asset ∧ r.amount = amount then
                  some (bridgeFinalizeRawAsset k id)
                else none
    | none   => none

with `bridgeFinalizeRawAsset k id` (`RecordKernel.lean:1712`) the NO-CREDIT resolve:

    { k with escrows := markResolved k.escrows id }

The two `find?` walk the SAME predicate over the SAME `s.kernel.escrows`, so they return the SAME
record `r` — the guard binds ONE found record.

Hence a committed `bridgeFinalizeA`:

  * **GUARD** — there is an unresolved record `r` with `r.id = id` (`find? = some r`), AND
        (authority) `r.bridge = true ∧ r.creator = actor` — only the RECORDED bridge creator may
        finalize, read off committed state — AND (receipt-match) `r.bridge = true ∧ r.asset = asset
        ∧ r.amount = amount` — the disclosed `(asset, amount)` MATCH the parked record's, fail-closed
        on a mismatch.
  * **TOUCHED `kernel.escrows`** ← `markResolved s.kernel.escrows id` (the first id-matching unresolved
        record flipped `resolved := true`; all others — before, after, other ids — untouched).
  * **TOUCHED `log`** ← `escrowReceiptA actor :: s.log` (one escrow-receipt clock row prepended).
  * **FRAME** every OTHER `RecordKernelState` component (the 16: `accounts cell caps bal nullifiers
        revoked commitments queues swiss slotCaveats factories lifecycle deathCert delegate delegations
        sealedBoxes`) LITERALLY unchanged. NOTE: `escrows` is the ONLY touched kernel field — in
        particular `bal` is FRAMED-UNCHANGED. The bridged value already left the per-cell `bal` ledger
        at LOCK time (`bridgeLockKAsset` debited `bal` and parked the record); finalize merely marks
        the record resolved, so it leaves the COMBINED `recTotalAssetWithEscrow` holding-store measure
        (the value departs the unresolved set) WITHOUT a second `bal` debit. (See `frameGaps`/notes —
        this is an honest difference from a naive "bal LEAVES at finalize" reading of the task.)

`BridgeFinalizeSpec` states EXACTLY this as a `Prop`, with NO executor term in any frame clause, and
`bridgeFinalizeChainA_iff_spec` proves the executor meets it iff — the `→` validates the executor
against the independent spec (a silently-mutated field would make the frame clause FAIL).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.BridgeOutboundFinalize

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

/-! ## §1 — The admissibility guard (the OUTER `bridgeAuthOK` gate ∧ the `bridgeFinalizeKAsset`
`find?`/receipt-match `if`, named).

A committed bridge-finalize needs (1) an unresolved id-matching record present (`find? = some r`),
(2) the AUTHORITY gate `r.bridge = true ∧ r.creator = actor` (only the recorded bridge creator may
finalize — `bridgeAuthOK`), and (3) the RECEIPT-MATCH gate `r.bridge = true ∧ r.asset = asset ∧
r.amount = amount` (the disclosed `(asset, amount)` MATCH the parked record's). We extract this as a
`Prop` carrying the found record `r`, so the bridge directions are a clean re-assembly. -/

/-- The decidable `find?` predicate BOTH kernel walks use: an UNRESOLVED record of this id. -/
def matchesId (id : Nat) : EscrowRecord → Bool := fun r => decide (r.id = id ∧ r.resolved = false)

/-- **`finalizeGuard s id actor asset amount r`** — the executor's admissibility for an outbound
finalize of bridge `id`, witnessed by the FOUND record `r`: `r` is the first unresolved id-matching
record (`find? = some r`); the AUTHORITY gate (`r.bridge = true ∧ r.creator = actor`); and the
RECEIPT-MATCH gate (`r.bridge = true ∧ r.asset = asset ∧ r.amount = amount`). This is the EXACT
conjunction of `bridgeAuthOK`'s record check + `bridgeFinalizeKAsset`'s `match`-arm + `if`-condition,
over the ONE record both `find?`s return. -/
def finalizeGuard (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId) (amount : ℤ)
    (r : EscrowRecord) : Prop :=
  s.kernel.escrows.find? (matchesId id) = some r
    ∧ r.bridge = true ∧ r.creator = actor
    ∧ r.asset = asset ∧ r.amount = amount

/-! ## §2 — The post-state's touched `escrows`, validated DECLARATIVELY (the `recTransfer_correct`
analogue).

`bridgeFinalizeRawAsset` is the EXACT post-state body a committed finalize installs. Its ONLY touched
field is `escrows := markResolved k.escrows id` — and crucially `bal` is LEFT UNTOUCHED (a no-credit
resolve, the OUTFLOW: the value already left `bal` at lock, and now departs the holding store). We
validate this declaratively (not blindly trust the helper). -/

/-- **`bridgeFinalize_resolve_correct`** — the finalize helper's behaviour validated DECLARATIVELY:
(1) the ONLY touched kernel field is `escrows`, set to `markResolved k.escrows id`; (2) the `bal`
ledger is LITERALLY unchanged (the no-credit OUTFLOW — no second debit at finalize). So the spec's
`escrows`/`bal` clauses genuinely encode resolve ∧ no-credit, rather than trusting the helper. -/
theorem bridgeFinalize_resolve_correct (k : RecordKernelState) (id : Nat) :
    (bridgeFinalizeRawAsset k id).escrows = markResolved k.escrows id
    ∧ (bridgeFinalizeRawAsset k id).bal = k.bal := by
  refine ⟨rfl, rfl⟩

/-! ## §3 — THE FULL-STATE DECLARATIVE SPEC (the INDEPENDENT reference).

The whole truth of a committed bridge-finalize: the guard holds for some found record `r`; the
post-state's `kernel.escrows` is the mark-resolved list; the `log` gains exactly one escrow receipt
for the actor; and ALL SIXTEEN other `RecordKernelState` components (including `bal` — the no-credit
OUTFLOW) are LITERALLY unchanged. No frame clause mentions the executor. -/

/-- **`BridgeFinalizeSpec s id actor asset amount s'`** — the INDEPENDENT full-state semantics of a
committed bridge-outbound-finalize. Existentially carries the found record `r` (the parked bridge
entry the finalize resolves), then enumerates ALL 17 kernel fields + `log`: `escrows` is
`markResolved … id`; `log` is the prepended escrow receipt; the other 16 kernel fields (`accounts
cell caps bal nullifiers revoked commitments queues swiss slotCaveats factories lifecycle deathCert
delegate delegations sealedBoxes`) are unchanged. Missing any field would reintroduce a ghost. -/
def BridgeFinalizeSpec (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId)
    (amount : ℤ) (s' : RecChainedState) : Prop :=
  ∃ r : EscrowRecord,
    finalizeGuard s id actor asset amount r
    ∧ s'.kernel.escrows = markResolved s.kernel.escrows id
    ∧ s'.log = escrowReceiptA actor :: s.log
    -- the 16 framed kernel fields (every RecordKernelState component except `escrows`):
    ∧ s'.kernel.accounts = s.kernel.accounts
    ∧ s'.kernel.cell = s.kernel.cell
    ∧ s'.kernel.caps = s.kernel.caps
    ∧ s'.kernel.bal = s.kernel.bal
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

`bridgeFinalizeChainA` commits a finalize into `s'` IFF `s'` is EXACTLY the spec'd full post-state.
The `→` VALIDATES the executor against the independent spec — all 18 components (17 kernel + log) are
checked, so had it silently mutated `bal`/`caps`/`nullifiers`/… the frame clauses would make this
proof FAIL. The `←` reconstructs the committed state from the spec.

The proof must reconcile the TWO `find?`s (`bridgeAuthOK`'s and `bridgeFinalizeKAsset`'s) — both walk
the identical predicate over the identical `s.kernel.escrows`, so a single `cases hf : find? = …`
collapses both. -/

/-- **`bridgeFinalizeChainA_iff_spec` — EXECUTOR ⟺ SPEC.** The chained per-asset bridge-finalize
executor commits an outbound finalize into `s'` iff `s'` is exactly the spec'd full post-state. -/
theorem bridgeFinalizeChainA_iff_spec (s : RecChainedState) (id : Nat) (actor : CellId)
    (asset : AssetId) (amount : ℤ) (s' : RecChainedState) :
    bridgeFinalizeChainA s id actor asset amount = some s'
      ↔ BridgeFinalizeSpec s id actor asset amount s' := by
  unfold bridgeFinalizeChainA bridgeAuthOK bridgeFinalizeKAsset BridgeFinalizeSpec finalizeGuard
         matchesId bridgeFinalizeRawAsset
  -- BOTH `find?`s walk the SAME predicate over `s.kernel.escrows`; split once.
  cases hf : s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none =>
    dsimp only
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨r, ⟨hfind, _⟩, _⟩; exact absurd hfind (by simp)
  | some r =>
    dsimp only
    -- the AUTHORITY gate `bridgeAuthOK` (outer `if`): `r.bridge == true && r.creator == actor`.
    by_cases hauth : (r.bridge == true && r.creator == actor) = true
    · rw [if_pos hauth]
      -- the RECEIPT-MATCH gate (inner `if`): `r.bridge = true ∧ r.asset = asset ∧ r.amount = amount`.
      by_cases hmatch : r.bridge = true ∧ r.asset = asset ∧ r.amount = amount
      · rw [if_pos hmatch]
        obtain ⟨hbr, hasset, hamt⟩ := hmatch
        -- decode the bool-`&&` authority gate into the propositional creator/bridge facts.
        simp only [Bool.and_eq_true, beq_iff_eq] at hauth
        obtain ⟨_, hcreator⟩ := hauth
        constructor
        · intro h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨r, ⟨rfl, hbr, hcreator, hasset, hamt⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                 rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rintro ⟨r', ⟨hfind', _, _, _, _⟩, hesc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
                 h12, h13, h14, h15, h16⟩
          -- the found record is unique: `find? = some r` and `= some r'`.
          simp only [Option.some.injEq] at hfind'
          subst hfind'
          -- reconstruct `s'` from its 18 components.
          obtain ⟨k', log'⟩ := s'
          obtain ⟨acc, cl, cp, esc, nul, rev, com, bl, qs, sw, slc, fac, lc, dc, dg, dgs, sb⟩ := k'
          simp only at hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
          subst hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
          dsimp only [bridgeFinalizeRawAsset]
      · rw [if_neg hmatch]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨r', ⟨hfind', hbr', _, hasset', hamt'⟩, _⟩
          simp only [Option.some.injEq] at hfind'
          subst hfind'
          exact (hmatch ⟨hbr', hasset', hamt'⟩).elim
    · rw [if_neg hauth]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨r', ⟨hfind', hbr', hcreator', _, _⟩, _⟩
        simp only [Option.some.injEq] at hfind'
        subst hfind'
        -- the spec's authority facts contradict `¬ bridgeAuthOK`.
        exact absurd (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨hbr', hcreator'⟩) hauth

/-- **`bridgeFinalizeChainA_iff_guard` — commitment IFF the guard** (the existence form).
`bridgeFinalizeChainA` commits SOME post-state iff there is a found unresolved record that is
bridge-tagged, creator-owned by `actor`, and receipt-matches the disclosed `(asset, amount)`. -/
theorem bridgeFinalizeChainA_iff_guard (s : RecChainedState) (id : Nat) (actor : CellId)
    (asset : AssetId) (amount : ℤ) :
    (∃ s', bridgeFinalizeChainA s id actor asset amount = some s')
      ↔ (∃ r, finalizeGuard s id actor asset amount r) := by
  constructor
  · rintro ⟨s', h⟩
    rw [bridgeFinalizeChainA_iff_spec] at h
    obtain ⟨r, hg, _⟩ := h
    exact ⟨r, hg⟩
  · rintro ⟨r, hg⟩
    -- rebuild the committed post-state from the guard via the iff.
    refine ⟨{ kernel := bridgeFinalizeRawAsset s.kernel id, log := escrowReceiptA actor :: s.log }, ?_⟩
    rw [bridgeFinalizeChainA_iff_spec]
    exact ⟨r, hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §5 — EXECUTOR ⟺ SPEC, lifted to `execFullA`.

The constructor `bridgeFinalizeA` is DEFINITIONALLY the transition `bridgeFinalizeChainA` (the
executor arm below is `rfl`). So `bridgeFinalizeChainA_iff_spec` lifts to it verbatim. -/

/-- The executor arm for `bridgeFinalizeA` is `bridgeFinalizeChainA` (definitional). -/
theorem execFullA_bridgeFinalize_eq (s : RecChainedState) (id : Nat) (actor : CellId)
    (asset : AssetId) (amount : ℤ) :
    execFullA s (.bridgeFinalizeA id actor asset amount)
      = bridgeFinalizeChainA s id actor asset amount := rfl

/-- **`execFullA_bridgeFinalize_iff_spec` — FULL executor ⟺ SPEC for `.bridgeFinalizeA`.** -/
theorem execFullA_bridgeFinalize_iff_spec (s : RecChainedState) (id : Nat) (actor : CellId)
    (asset : AssetId) (amount : ℤ) (s' : RecChainedState) :
    execFullA s (.bridgeFinalizeA id actor asset amount) = some s'
      ↔ BridgeFinalizeSpec s id actor asset amount s' := by
  rw [execFullA_bridgeFinalize_eq]; exact bridgeFinalizeChainA_iff_spec s id actor asset amount s'

/-! ## §6 — Soundness teeth (the spec is NOT vacuous).

The `→` direction of the spec already validates the executor on EVERY field. Here we exhibit the
positive content a committed finalize carries (the record genuinely LEAVES the unresolved set; `bal`
genuinely stays put — the no-credit OUTFLOW) and the negative content (a missing/already-resolved
record, a non-creator caller, or a receipt mismatch is fail-closed). These are derived from the
INDEPENDENT spec / executor body. -/

/-- **`finalize_resolves_record` — FRAME teeth (the holding-store moves).** A committed finalize marks
the holding-store via `markResolved … id` — the record genuinely LEAVES the unresolved set (the value
departs for the other chain). -/
theorem finalize_resolves_record (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId)
    (amount : ℤ) (s' : RecChainedState) (h : BridgeFinalizeSpec s id actor asset amount s') :
    s'.kernel.escrows = markResolved s.kernel.escrows id := by
  obtain ⟨_, _, hesc, _⟩ := h
  exact hesc

/-- **`finalize_bal_neutral` — FRAME teeth (the NO-CREDIT outflow).** A committed finalize leaves the
per-asset `bal` ledger LITERALLY unchanged: finalize is a no-credit resolve (the value already left
`bal` at lock time; finalize merely drops the parked record from the holding store). This is the
honest contrast with escrow-release, which DOES credit a recipient. -/
theorem finalize_bal_neutral (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId)
    (amount : ℤ) (s' : RecChainedState) (h : BridgeFinalizeSpec s id actor asset amount s') :
    s'.kernel.bal = s.kernel.bal := by
  obtain ⟨_, _, _, _, _, _, _, hbal, _⟩ := h
  exact hbal

/-- **`finalize_authority_creator` — POSITIVE teeth (the authority gate's content).** A committed
finalize witnesses that the found record is bridge-tagged AND its RECORDED creator IS the caller —
only the bridge originator (read off committed state) could have finalized. Closes re-audit hole #4
("anyone can finalize any victim's bridge lock by id"). -/
theorem finalize_authority_creator (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId)
    (amount : ℤ) (s' : RecChainedState) (h : BridgeFinalizeSpec s id actor asset amount s') :
    ∃ r, s.kernel.escrows.find? (matchesId id) = some r
      ∧ r.bridge = true ∧ r.creator = actor := by
  obtain ⟨r, ⟨hfind, hbr, hcreator, _, _⟩, _⟩ := h
  exact ⟨r, hfind, hbr, hcreator⟩

/-- **`finalize_receipt_match` — POSITIVE teeth (the receipt-vs-pending check).** A committed finalize
witnesses that the disclosed `(asset, amount)` EXACTLY MATCH the parked record's `(asset, amount)` —
no cross-asset/amount laundering at the bridge boundary. -/
theorem finalize_receipt_match (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId)
    (amount : ℤ) (s' : RecChainedState) (h : BridgeFinalizeSpec s id actor asset amount s') :
    ∃ r, s.kernel.escrows.find? (matchesId id) = some r
      ∧ r.asset = asset ∧ r.amount = amount := by
  obtain ⟨r, ⟨hfind, _, _, hasset, hamt⟩, _⟩ := h
  exact ⟨r, hfind, hasset, hamt⟩

/-- **`finalize_rejects_missing` — NEGATIVE teeth.** With NO unresolved id-matching record present
(`find? = none`), the finalize CANNOT commit: `bridgeFinalizeChainA` returns `none`. A
missing/already-resolved bridge lock is FAIL-CLOSED. -/
theorem finalize_rejects_missing (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId)
    (amount : ℤ) (hbad : s.kernel.escrows.find? (matchesId id) = none) :
    bridgeFinalizeChainA s id actor asset amount = none := by
  unfold bridgeFinalizeChainA bridgeAuthOK bridgeFinalizeKAsset matchesId at *
  rw [hbad]; simp

/-- **`finalize_rejects_nonCreator` — NEGATIVE teeth (the AUTHORITY gate).** Even with a present
unresolved bridge record, if its RECORDED `creator` is NOT the caller the finalize is FAIL-CLOSED:
`bridgeFinalizeChainA` returns `none`. (Same content as `bridgeFinalizeChainA_nonCreator_rejects`,
re-derived here against this module's `matchesId`.) -/
theorem finalize_rejects_nonCreator (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId)
    (amount : ℤ) (r : EscrowRecord) (hfind : s.kernel.escrows.find? (matchesId id) = some r)
    (hbad : (r.creator == actor) = false) :
    bridgeFinalizeChainA s id actor asset amount = none := by
  have hgate : bridgeAuthOK s.kernel id actor = false := by
    unfold bridgeAuthOK matchesId at *
    simp only [hfind]
    rw [hbad]; simp
  unfold bridgeFinalizeChainA
  rw [if_neg (by simp [hgate])]

/-- **`finalize_rejects_mismatch` — NEGATIVE teeth (the RECEIPT-MATCH gate).** Even with a present
unresolved bridge record whose creator IS the caller, if the disclosed `(asset, amount)` do NOT match
the parked record's, the finalize is FAIL-CLOSED. No laundering of a different asset/amount through a
victim's-or-own lock. -/
theorem finalize_rejects_mismatch (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId)
    (amount : ℤ) (r : EscrowRecord) (hfind : s.kernel.escrows.find? (matchesId id) = some r)
    (hbad : ¬ (r.bridge = true ∧ r.asset = asset ∧ r.amount = amount)) :
    bridgeFinalizeChainA s id actor asset amount = none := by
  unfold matchesId at hfind
  unfold bridgeFinalizeChainA bridgeFinalizeKAsset
  by_cases hauth : bridgeAuthOK s.kernel id actor = true
  · rw [if_pos hauth, hfind]
    simp only [if_neg hbad]
  · rw [if_neg (by simp [hauth])]

/-! ## §7 — Concrete #guard witnesses: a creator-owned matched bridge lock finalizes; a missing,
non-creator, or mismatched one is rejected.

State `sB0` parks one unresolved BRIDGE lock (id 7, creator 0, recipient 1, amount 5, asset 1,
bridge := true). A finalize by the creator (actor 0) disclosing the matching `(asset 1, amount 5)`
commits: the record is resolved, `bal` is unchanged. A finalize by a NON-creator (actor 9), a finalize
of a NON-existent id 99, and a finalize disclosing a MISMATCHED amount 99 are each rejected (`none`).
Decidable `#guard`s (genuine `decide`, NOT `native_decide`). -/

/-- A concrete chained state parking ONE unresolved BRIDGE lock: id 7, creator 0, recipient 1,
amount 5, asset 1, bridge := true. Cells 0 and 1 are live accounts. -/
def sB0 : RecChainedState :=
  { kernel := { accounts := {0, 1}
                cell := fun _ => .record [("balance", .int 0)]
                caps := fun _ => []
                escrows := [{ id := 7, creator := 0, recipient := 1, amount := 5,
                              resolved := false, asset := 1, bridge := true }] }
    log := [] }

-- A finalize by the creator (actor 0) disclosing the matching (asset 1, amount 5) commits:
#guard (execFullA sB0 (.bridgeFinalizeA 7 0 1 5)).isSome  --  true
-- ...and the record is now resolved (it left the unresolved holding-store set — the outflow):
#guard ((execFullA sB0 (.bridgeFinalizeA 7 0 1 5)).map
          (fun s' => (s'.kernel.escrows.head?.map (fun r => r.resolved)).getD false)).getD false
          == true
-- ...and the per-asset `bal` ledger is UNCHANGED (the no-credit OUTFLOW — value already left at lock):
#guard ((execFullA sB0 (.bridgeFinalizeA 7 0 1 5)).map (fun s' => s'.kernel.bal 1 1)).getD 99 == 0

-- A finalize by a NON-creator (actor 9) is REJECTED (the AUTHORITY gate fails closed):
#guard (execFullA sB0 (.bridgeFinalizeA 7 9 1 5)).isNone  --  true
-- A finalize of a NON-existent id 99 is REJECTED (fail-closed, no such record):
#guard (execFullA sB0 (.bridgeFinalizeA 99 0 1 5)).isNone  --  true
-- A finalize disclosing a MISMATCHED amount 99 is REJECTED (the RECEIPT-MATCH gate fails closed):
#guard (execFullA sB0 (.bridgeFinalizeA 7 0 1 99)).isNone  --  true
-- A finalize disclosing a MISMATCHED asset 2 is REJECTED (the RECEIPT-MATCH gate fails closed):
#guard (execFullA sB0 (.bridgeFinalizeA 7 0 2 5)).isNone  --  true

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms bridgeFinalize_resolve_correct
#assert_axioms bridgeFinalizeChainA_iff_spec
#assert_axioms bridgeFinalizeChainA_iff_guard
#assert_axioms execFullA_bridgeFinalize_eq
#assert_axioms execFullA_bridgeFinalize_iff_spec
#assert_axioms finalize_resolves_record
#assert_axioms finalize_bal_neutral
#assert_axioms finalize_authority_creator
#assert_axioms finalize_receipt_match
#assert_axioms finalize_rejects_missing
#assert_axioms finalize_rejects_nonCreator
#assert_axioms finalize_rejects_mismatch

end Dregg2.Circuit.Spec.BridgeOutboundFinalize
