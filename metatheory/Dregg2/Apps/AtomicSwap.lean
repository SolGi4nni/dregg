/-
# Dregg2.Apps.AtomicSwap — a verified MULTI-PARTY ATOMIC ESCROW SWAP over the REAL kernel.

The gallery's first MULTI-PARTY app on the GENUINE `RecordKernelState` (NOT the discrete `DemoRes`
toy of `SealedBidAuction`): `N` parties each ESCROW one asset, and the swap settles ATOMICALLY —
all legs commit, or NONE do (fail-closed rollback). This is `dregg1`'s `apply_create_escrow`/
`apply_release_escrow` lifecycle (`turn/src/executor/apply.rs:1674`/`:1959`) composed into a
multi-leg trade, riding entirely on the per-asset `bal` ledger + off-ledger holding-store of
`Exec/RecordKernel.lean`.

It is **composition, not new kernel theory**: every conservation/authority keystone INSTANTIATES a
proved abstract lemma from the green `RecordKernel` (`escrow_create_conserves_combined_per_asset`,
`releaseEscrowKAsset_conserves_combined_per_asset`, `createEscrowKAsset_authorized`,
`recBalCreditCell_recTotalAsset`). What this module ADDS is the multi-party COMPOSITION and the three
headline guarantees:

  * **CONSERVATION (per-asset, whole swap)** — for EVERY asset `b`, the combined per-asset measure
    `recTotalAssetWithEscrow b` (bal-ledger + holding-store) is preserved across the ENTIRE swap:
    Σ each asset in = Σ each asset out. Proved by folding the single-step kernel conservation over
    BOTH phases (lock-all then settle-all) — `runSwap_conserves` / `settleSwap_conserves`.
  * **ATOMICITY (all-or-nothing, fail-closed)** — the lock phase is a monadic fold (`Option.bind`):
    if ANY party's leg fails (insufficient escrow / missing authority / duplicate id), the WHOLE
    fold returns `none`, the swap ROLLS BACK, and EVERY balance is unchanged (`atomicSwap = k`,
    `runSwap_none_rolls_back`). TEETH: a concrete under-funded swap is REJECTED — its committed
    state EQUALS the pre-state, proved as a real discriminating lemma (`underfunded_rolls_back`) +
    `#eval` contrast against the funded swap that genuinely DOES move the ledger.
  * **AUTHORITY (honest scope)** — every committed leg is SELF-authorized (`actor == src`, trivially
    true for any caps — see the honest-scope note on `swap_all_legs_authorized`); the GENUINE cap-gated
    authority is `unauthorized_lock_rejected` (a non-owner holding no cap is REJECTED, exercising the
    real cap-table branch), and release credits only the named counterparty of an EXISTING parked
    record (`release_only_parked` — no pulling an un-escrowed asset).
  * **LIVENESS ◇** — a funded + authorized + locked swap CAN always settle (`settle_completes`), and
    settlement delivers each counterparty its escrowed asset (`settle_delivers`); teeth: a wrong/absent
    id or an unlocked swap credits nobody (`settle_wrong_id_no_delivery`, `settle_unlocked_no_delivery`).

Built on the REAL `RecordKernelState` primitives (`bal` per-asset ledger + `escrows` holding-store),
NOT `DemoRes`. Pure, computable, `#eval`-able.
-/
import Dregg2.Exec.RecordKernel

namespace Dregg2.Apps.AtomicSwap

open Dregg2.Exec
open Dregg2.Authority (Cap Auth)

/-! ## 1. A swap leg and the multi-party swap.

A `SwapLeg` is one party's contribution to the trade: party `party` escrows `amount` of asset
`asset`, destined for `counterparty`. The escrow is keyed by a unique `id`. A swap is a `List
SwapLeg` — `N` parties, `N` legs. (`actor = party`: each party self-authorizes its own lock, the
`actor == src` arm of `authorizedB`; a delegated/cap-bearing actor is the obvious generalization,
not needed for the headline.) -/

/-- **`SwapLeg`** — one party's leg of the multi-party swap: lock `amount` of asset `asset` from
`party`, escrow id `id`, destined for `counterparty` on settle. The `actor` defaults to `party`
(self-authorized lock). -/
structure SwapLeg where
  /-- the escrow id (unique per leg). -/
  id           : Nat
  /-- the party escrowing the asset (debited at lock, the `creator`/refund target). -/
  party        : CellId
  /-- the counterparty credited on settle (the `recipient`). -/
  counterparty : CellId
  /-- the asset class being escrowed (per-asset: this asset moves, others untouched). -/
  asset        : AssetId
  /-- the amount of `asset` escrowed. -/
  amount       : ℤ
deriving Repr, DecidableEq

/-! ## 2. PHASE 1 — lock all legs (the all-or-nothing monadic fold).

Each leg LOCKS its asset via the real `createEscrowKAsset` (single-cell per-asset debit + park the
record). The fold threads the state with `Option.bind`, so the FIRST failing leg short-circuits the
WHOLE swap to `none` — this is the atomicity mechanism: no partial swap exists. -/

/-- **`lockLeg k leg`** — lock a single leg via the real kernel `createEscrowKAsset`: the party
self-authorizes (`actor := leg.party`), debiting `leg.party`'s asset column and parking the record.
Fail-closed (`none`) if the party is unauthorized, the amount is negative or unavailable in that
asset, the party is not a live account, or the id is already in use. -/
def lockLeg (k : RecordKernelState) (leg : SwapLeg) : Option RecordKernelState :=
  createEscrowKAsset k leg.id leg.party leg.party leg.counterparty leg.asset leg.amount

/-- **`runSwap k legs`** — PHASE 1, the all-or-nothing lock fold: lock every leg in order, threading
the state monadically. If ANY leg fails, the whole fold is `none` (atomicity). `none` ⇒ the swap is
rejected and rolls back (`atomicSwap`). -/
def runSwap (k : RecordKernelState) : List SwapLeg → Option RecordKernelState
  | []          => some k
  | leg :: legs => (lockLeg k leg).bind (fun k' => runSwap k' legs)

/-- **`atomicSwap k legs`** — the lock phase with EXPLICIT ROLLBACK: commit the locked state on
success, otherwise return the UNCHANGED pre-state `k`. This is the all-or-nothing transaction
boundary — a failed swap leaves the world exactly as it found it. -/
def atomicSwap (k : RecordKernelState) (legs : List SwapLeg) : RecordKernelState :=
  (runSwap k legs).getD k

/-! ## 3. KEYSTONE — ATOMICITY: a failed swap ROLLS BACK (every balance unchanged).

The atomicity headline: if the lock fold fails anywhere (`runSwap = none`), the committed state is
the PRE-state — no balance moved. Fail-closed rollback, by definition of `atomicSwap` + `Option.getD`. -/

/-- **`runSwap_none_rolls_back` (ATOMICITY)** — if the lock fold fails, the atomic swap commits the
UNCHANGED pre-state: `atomicSwap k legs = k`. Every balance, every escrow, every cap is exactly as
before — the swap is all-or-nothing. -/
theorem runSwap_none_rolls_back (k : RecordKernelState) (legs : List SwapLeg)
    (h : runSwap k legs = none) : atomicSwap k legs = k := by
  unfold atomicSwap; rw [h]; rfl

/-- **`runSwap_some_commits` (the positive face)** — if the lock fold SUCCEEDS, the atomic swap
commits exactly the locked state. (Non-vacuity for the rollback: a swap that succeeds genuinely
advances, so the rollback is not a no-op masquerade.) -/
theorem runSwap_some_commits (k k' : RecordKernelState) (legs : List SwapLeg)
    (h : runSwap k legs = some k') : atomicSwap k legs = k' := by
  unfold atomicSwap; rw [h]; rfl

/-! ## 4. KEYSTONE — CONSERVATION (per-asset, across the WHOLE lock phase).

Each `lockLeg` preserves the combined per-asset measure `recTotalAssetWithEscrow b` for EVERY asset
`b` (the debit is exactly offset by the holding-store rise — `escrow_create_conserves_combined_per_asset`).
Folding that over the whole list: the combined per-asset total is preserved across the ENTIRE lock
phase. This is `Σ each asset in = Σ each asset out`, composed, not re-derived. -/

/-- A single lock preserves the combined per-asset measure for every asset — a thin wrapper over the
kernel keystone `escrow_create_conserves_combined_per_asset`, specialized to the `lockLeg` shape. -/
theorem lockLeg_conserves {k k' : RecordKernelState} {leg : SwapLeg} (b : AssetId)
    (h : lockLeg k leg = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b :=
  escrow_create_conserves_combined_per_asset b h

/-- **`runSwap_conserves` (CONSERVATION, lock phase)** — the WHOLE lock fold preserves the combined
per-asset measure `recTotalAssetWithEscrow b` for EVERY asset `b`: Σ each asset in = Σ each asset out
across all legs. Proved by list induction, composing `lockLeg_conserves` at each step (the value
moves into the holding-store, never minted or destroyed). -/
theorem runSwap_conserves (b : AssetId) :
    ∀ (legs : List SwapLeg) (k k' : RecordKernelState),
      runSwap k legs = some k' →
      recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  intro legs
  induction legs with
  | nil =>
      intro k k' h
      simp only [runSwap, Option.some.injEq] at h
      subst h; rfl
  | cons leg legs ih =>
      intro k k' h
      simp only [runSwap] at h
      -- `(lockLeg k leg).bind (runSwap · legs) = some k'` ⇒ the lock succeeded at some `k1`.
      cases hlock : lockLeg k leg with
      | none => rw [hlock] at h; simp at h
      | some k1 =>
          rw [hlock] at h
          simp only [Option.bind_some] at h
          -- the tail fold conserves from `k1`, the head lock conserves `k → k1`.
          rw [ih k1 k' h, lockLeg_conserves b hlock]

/-- **`atomicSwap_conserves` (CONSERVATION on the committed state, when the swap COMMITS)** — on a
successful swap, the committed atomic-swap state preserves the combined per-asset measure for every
asset. (When the swap fails, `atomicSwap = k` by `runSwap_none_rolls_back`, so conservation is
trivially the identity — covered there.) -/
theorem atomicSwap_conserves {k k' : RecordKernelState} {legs : List SwapLeg} (b : AssetId)
    (h : runSwap k legs = some k') :
    recTotalAssetWithEscrow (atomicSwap k legs) b = recTotalAssetWithEscrow k b := by
  rw [runSwap_some_commits k k' legs h]; exact runSwap_conserves b legs k k' h

/-! ## 5. PHASE 2 — settle all legs (release each escrow to the counterparty).

Each parked record is RELEASED via the real `releaseEscrowKAsset`: a single-cell per-asset credit to
the counterparty + mark resolved. The settle-liveness gate (`recipient ∈ accounts`) is enforced by
the kernel, so combined per-asset conservation holds UNCONDITIONALLY at each release. We fold the
release over the leg ids (same all-or-nothing monadic threading). -/

/-- **`settleSwap k ids`** — PHASE 2, the release fold: release every escrow id in order
(`releaseEscrowKAsset`), threading the state monadically. A missing/already-resolved record or a
non-live recipient short-circuits to `none` (fail-closed). -/
def settleSwap (k : RecordKernelState) : List Nat → Option RecordKernelState
  | []        => some k
  | id :: ids => (releaseEscrowKAsset k id).bind (fun k' => settleSwap k' ids)

/-- **`settleSwap_conserves` (CONSERVATION, settle phase)** — the WHOLE release fold preserves the
combined per-asset measure for EVERY asset: value moves OUT of the holding-store back onto the
counterparties' ledgers, the combined total fixed. Composes `releaseEscrowKAsset_conserves_combined_per_asset`
over the list. -/
theorem settleSwap_conserves (b : AssetId) :
    ∀ (ids : List Nat) (k k' : RecordKernelState),
      settleSwap k ids = some k' →
      recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  intro ids
  induction ids with
  | nil =>
      intro k k' h
      simp only [settleSwap, Option.some.injEq] at h
      subst h; rfl
  | cons id ids ih =>
      intro k k' h
      simp only [settleSwap] at h
      cases hrel : releaseEscrowKAsset k id with
      | none => rw [hrel] at h; simp at h
      | some k1 =>
          rw [hrel] at h
          simp only [Option.bind_some] at h
          rw [ih k1 k' h, releaseEscrowKAsset_conserves_combined_per_asset b hrel]

/-- **`swap_conserves_end_to_end` (THE HEADLINE — CONSERVATION across LOCK + SETTLE)** — the FULL
two-phase swap (lock all legs, then settle all escrows) preserves the combined per-asset measure
`recTotalAssetWithEscrow b` for EVERY asset `b`. Σ each asset in = Σ each asset out, end-to-end: the
locks park value into the holding-store (conserved), the settles move it back onto the
counterparties' ledgers (conserved), so the whole trade neither mints nor burns any asset. -/
theorem swap_conserves_end_to_end (b : AssetId) (legs : List SwapLeg) (ids : List Nat)
    {k klocked ksettled : RecordKernelState}
    (hlock : runSwap k legs = some klocked)
    (hsettle : settleSwap klocked ids = some ksettled) :
    recTotalAssetWithEscrow ksettled b = recTotalAssetWithEscrow k b := by
  rw [settleSwap_conserves b ids klocked ksettled hsettle,
      runSwap_conserves b legs k klocked hlock]

/-! ## 6. KEYSTONE — AUTHORITY (only escrowed assets move).

Each committed lock is SELF-authorized: `actor = party = src`, so `authorizedB` holds via its reflexive
`actor == src` arm — UNCONDITIONALLY, for any cap table (self-escrow needs no capability). That is the
correct semantics (you may always escrow your OWN asset), but it does NOT consult the cap-table; so
`lockLeg_authorized`/`swap_all_legs_authorized` are honest-but-TRIVIAL self-authorization facts, NOT a
cap-bearing "only authorized actors" guarantee. The GENUINE authority content is two-fold:
`release_only_parked` (a release credits only an EXISTING parked record — no un-escrowed pull) and
`unauthorized_lock_rejected` (an actor that is NOT the owner and holds NO cap is REJECTED — the real
cap-table gate that the `actor == src` arm never touches). -/

/-- **`lockLeg_authorized` (self-authorization — HONEST SCOPE)** — a committed lock satisfies
`authorizedB` on `{actor := party, src := party, ..}`. NOTE this is TRIVIALLY true: `actor == src`
(party == party) is `authorizedB`'s reflexive arm, satisfied for ANY cap table — it does NOT consult
the caps. It records that self-escrow is authorized, not a cap-bearing guarantee; the genuine cap-gated
authority is `unauthorized_lock_rejected`. Reads off the kernel keystone `createEscrowKAsset_authorized`. -/
theorem lockLeg_authorized {k k' : RecordKernelState} {leg : SwapLeg} (h : lockLeg k leg = some k') :
    authorizedB k.caps
      { actor := leg.party, src := leg.party, dst := leg.counterparty, amt := leg.amount } = true :=
  createEscrowKAsset_authorized h

/-- **`swap_all_legs_authorized` (self-authorization, folded — HONEST SCOPE)** — in a committed lock
fold, every leg's party self-authorizes (`actor == src`). Like `lockLeg_authorized`, each witness is
the TRIVIAL `actor == src` arm of `authorizedB` (true for any caps), so this is a self-authorization
fact, NOT a cap-bearing "only authorized actors" theorem. The cap-table gate is exercised genuinely by
`unauthorized_lock_rejected`. -/
theorem swap_all_legs_authorized :
    ∀ (legs : List SwapLeg) (k k' : RecordKernelState),
      runSwap k legs = some k' →
      ∀ leg ∈ legs, ∃ kAt : RecordKernelState,
        authorizedB kAt.caps
          { actor := leg.party, src := leg.party, dst := leg.counterparty, amt := leg.amount } = true := by
  intro legs
  induction legs with
  | nil => intro k k' _ leg hmem; simp at hmem
  | cons leg0 legs ih =>
      intro k k' h leg hmem
      simp only [runSwap] at h
      cases hlock : lockLeg k leg0 with
      | none => rw [hlock] at h; simp at h
      | some k1 =>
          rw [hlock] at h
          simp only [Option.bind_some] at h
          rcases List.mem_cons.mp hmem with hhd | htl
          · subst hhd; exact ⟨k, lockLeg_authorized hlock⟩
          · exact ih k1 k' h leg htl

/-- **`release_only_parked` (AUTHORITY — no un-escrowed pull)** — a committed release moved value
ONLY for an EXISTING unresolved parked record: `releaseEscrowKAsset k id = some k'` forces a record
with that `id` to have been found (present-and-unresolved) in `k.escrows`. There is no path by which
a release credits a counterparty without a matching parked escrow — you cannot pull an un-escrowed
asset. -/
theorem release_only_parked {k k' : RecordKernelState} {id : Nat} (h : releaseEscrowKAsset k id = some k') :
    ∃ r, k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r ∧
         r.recipient ∈ k.accounts := by
  unfold releaseEscrowKAsset at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hlive : r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true
      · exact ⟨r, rfl, hlive.1⟩
      · rw [if_neg hlive] at h; exact absurd h (by simp)

/-! ## 7. The TEETH — a concrete underfunded swap is REJECTED (state == pre-state), vs a funded one.

A real discriminating fixture: a 3-party swap. Parties 0, 1, 2 each hold 100 of their own asset and
want to escrow 30. The FUNDED swap LOCKS all three (and the combined per-asset measure is preserved);
the UNDERFUNDED swap (one party tries to escrow 30 of an asset it has 0 of) is REJECTED — the lock
fold fails, `atomicSwap` returns the UNCHANGED pre-state. The `#eval` contrast exhibits both. -/

/-- The swap fixture: three cells `{0, 1, 2}`, each cell `c` holds 100 of asset `c` (cell 0 → asset
0, cell 1 → asset 1, cell 2 → asset 2). Each party owns its own cell (`actor = party = src`
self-authorizes via the `actor == src` arm of `authorizedB`, so no caps are needed). -/
def swap0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = a ∧ c ∈ ({0, 1, 2} : Finset CellId) then 100 else 0 }

/-- **`unauthorized_lock_rejected` (AUTHORITY — the genuine cap-gated teeth)** — an actor that is NOT
the asset owner and holds NO capability over the owner's cell CANNOT escrow that asset: the kernel
fail-closes (`createEscrowKAsset = none`). Party `1` attempts to escrow party `0`'s asset 0 (actor `1`
≠ creator `0`) against `swap0`'s EMPTY cap table — `authorizedB` fails on BOTH arms (`1 ≠ 0`, and
`caps 1 = []`), so the lock is rejected. The lock is funded (cell 0 holds 100 of asset 0) and the id is
fresh, so AUTHORITY is the SOLE reason for rejection — this exercises the cap-table branch of
`authorizedB` that the self-authorized `lockLeg_authorized` (`actor == src`) never touches: the real
"you cannot move an asset you do not control" content. -/
theorem unauthorized_lock_rejected :
    createEscrowKAsset swap0 99 1 0 2 0 30 = none := by
  unfold createEscrowKAsset
  split
  · rename_i hcond
    exact absurd hcond.1 (by simp [authorizedB, swap0])
  · rfl

/-- A 3-leg cyclic swap: party 0 → 1 (asset 0), party 1 → 2 (asset 1), party 2 → 0 (asset 2), each
escrowing 30. Every leg is funded (each party holds 100 of its own asset). -/
def fundedLegs : List SwapLeg :=
  [ { id := 10, party := 0, counterparty := 1, asset := 0, amount := 30 },
    { id := 11, party := 1, counterparty := 2, asset := 1, amount := 30 },
    { id := 12, party := 2, counterparty := 0, asset := 2, amount := 30 } ]

/-- The UNDERFUNDED variant: the third leg tries to escrow 30 of asset 0 from party 2 — but party 2
holds 0 of asset 0 (it only holds asset 2). That leg fails (`amount ≤ bal` violated), so the whole
fold fails and the swap rolls back. -/
def underfundedLegs : List SwapLeg :=
  [ { id := 10, party := 0, counterparty := 1, asset := 0, amount := 30 },
    { id := 11, party := 1, counterparty := 2, asset := 1, amount := 30 },
    { id := 12, party := 2, counterparty := 0, asset := 0, amount := 30 } ]  -- party 2 has 0 of asset 0!

/-- **`funded_swap_commits` — the FUNDED swap genuinely LOCKS (non-vacuity of the teeth).** The
funded 3-leg swap succeeds: `runSwap swap0 fundedLegs` is `some _`. So the rollback teeth below are
discriminating a real success from a real failure, not "everything fails". -/
theorem funded_swap_commits : (runSwap swap0 fundedLegs).isSome = true := by decide

/-- **`underfunded_swap_rejected` — the UNDERFUNDED swap FAILS the lock fold.** Party 2 cannot escrow
asset 0 (holds 0), so its leg's `createEscrowKAsset` returns `none` and the whole fold short-circuits. -/
theorem underfunded_swap_rejected : runSwap swap0 underfundedLegs = none := by decide

/-- **`underfunded_rolls_back` (THE ATOMICITY TEETH — state == pre-state, PROVED)** — the underfunded
swap ROLLS BACK to the EXACT pre-state: `atomicSwap swap0 underfundedLegs = swap0`. Not a single
balance moved, no escrow was parked — the all-or-nothing boundary held. Discharged by
`runSwap_none_rolls_back` fed the rejection. This is a REAL discriminating lemma: the funded swap
genuinely advances (`funded_swap_commits`), this one genuinely does not. -/
theorem underfunded_rolls_back : atomicSwap swap0 underfundedLegs = swap0 :=
  runSwap_none_rolls_back swap0 underfundedLegs underfunded_swap_rejected

/-- **`funded_swap_conserves` — the FUNDED swap conserves EVERY asset (combined measure).** Applied
at the committed state: for every asset `b`, `recTotalAssetWithEscrow (atomicSwap swap0 fundedLegs) b
= recTotalAssetWithEscrow swap0 b`. Reads off `atomicSwap_conserves` with the success witness. -/
theorem funded_swap_conserves (b : AssetId) {k' : RecordKernelState}
    (h : runSwap swap0 fundedLegs = some k') :
    recTotalAssetWithEscrow (atomicSwap swap0 fundedLegs) b = recTotalAssetWithEscrow swap0 b :=
  atomicSwap_conserves b h

/-! ## 7.5 KEYSTONE — LIVENESS ◇ (a funded, locked swap CAN always settle — no deadlock).

The fourth APP-THEOREM-SUITE pillar. ATOMICITY (§3) says a swap is all-or-nothing; CONSERVATION (§4)
that it neither mints nor burns; AUTHORITY (§6) that only escrowed assets move. LIVENESS says the
locked value does not get STUCK: once the lock phase parks the leg escrows, the settle phase ALWAYS
succeeds (`settle_completes`) and DELIVERS each counterparty its escrowed asset (`settle_delivers`).
This is the `◇`/eventually face — the funded+authorized+locked swap genuinely REACHES a fully-settled
state, no party left holding an un-releasable claim.

The completion mechanism is the kernel's settle-liveness gate (`releaseEscrowKAsset`): a release
succeeds iff the id names a parked UNRESOLVED record whose recipient is a LIVE account — and in a swap
the recipient of every parked leg IS its `counterparty`, which the swap fixture makes an account. So
every parked leg can be released; the fold over the leg ids therefore drives the swap to settlement. -/

/-- **`release_completes_of_parked` (LIVENESS primitive — a parked leg CAN be released).** If id `id`
names a parked UNRESOLVED record whose recipient is a LIVE account AND is lifecycle-live (the D3
settle-target gate — a Sealed/Destroyed recipient would block delivery), the kernel release SUCCEEDS
(`isSome`). This is the per-leg liveness step the settle fold composes: no parked leg with a live,
non-frozen counterparty is stuck. Reads off the `releaseEscrowKAsset` semantics + its settle-liveness gate. -/
theorem release_completes_of_parked {k : RecordKernelState} {id : Nat} {r : EscrowRecord}
    (hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hlive : r.recipient ∈ k.accounts) (hlc : cellLifecycleLive k r.recipient = true) :
    (releaseEscrowKAsset k id).isSome = true := by
  unfold releaseEscrowKAsset
  rw [hfind]
  simp only [hlive, hlc, and_self, if_true, Option.isSome_some]

/-- **`release_delivers` (CORRECTNESS — a release CREDITS the named counterparty its escrowed asset).**
A committed release of id `id` credits the found record's `recipient` EXACTLY `r.amount` of `r.asset`
(`k'.bal r.recipient r.asset = k.bal r.recipient r.asset + r.amount`), the recipient being a LIVE
account. Delivery is correct: the counterparty receives the locked asset/amount, at THAT asset only.
This is the per-leg delivery the swap's `settle_delivers` rests on — read off `settleEscrowRawAsset`'s
single-cell `recBalCreditCell` credit. -/
theorem release_delivers {k k' : RecordKernelState} {id : Nat} (h : releaseEscrowKAsset k id = some k') :
    ∃ r, k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r ∧
         r.recipient ∈ k.accounts ∧
         k'.bal r.recipient r.asset = k.bal r.recipient r.asset + r.amount := by
  unfold releaseEscrowKAsset at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hlive : r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true
      · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h; subst h
        refine ⟨r, rfl, hlive.1, ?_⟩
        show recBalCreditCell k.bal r.recipient r.asset r.amount r.recipient r.asset = _
        unfold recBalCreditCell
        rw [if_pos ⟨rfl, rfl⟩]
      · rw [if_neg hlive] at h; exact absurd h (by simp)

/-- The leg ids of the funded fixture, in lock order. The settle fold releases exactly these. -/
def fundedIds : List Nat := [10, 11, 12]

/-- **`settle_completes` (LIVENESS ◇ — the funded, locked swap REACHES settlement, no deadlock).** The
funded 3-leg swap, once locked (`runSwap swap0 fundedLegs` parks all three records), CAN ALWAYS settle:
releasing all three leg ids succeeds (`isSome`). Every parked leg's recipient is its `counterparty`,
which `swap0` makes a LIVE account (`{0,1,2}`), so each `releaseEscrowKAsset` clears its settle-liveness
gate and the whole release fold completes. The locked value is NOT stuck — the swap genuinely reaches a
fully-settled state. This is the `◇`/eventually pillar, decided on the real-kernel fixture. -/
theorem settle_completes :
    ((runSwap swap0 fundedLegs).bind (fun k => settleSwap k fundedIds)).isSome = true := by decide

/-- **`settle_completes_get` (LIVENESS ◇, the `.get` reading).** With the lock-success witness
`funded_swap_commits`, the settle of the locked state is `isSome`: `settleSwap (locked).isSome`. The
funded+authorized+locked swap concretely reaches a fully-settled state — `◇ settled`, made executable. -/
theorem settle_completes_get :
    (settleSwap ((runSwap swap0 fundedLegs).get funded_swap_commits) fundedIds).isSome = true := by
  decide

/-- **`settle_delivers` (CORRECTNESS — settlement DELIVERS each counterparty its escrowed asset).** After
the funded swap locks and then settles all legs, each counterparty holds EXACTLY its escrowed amount of
the escrowed asset on the `bal` ledger: party 0's counterparty `1` gets 30 of asset 0, party 1's
counterparty `2` gets 30 of asset 1, party 2's counterparty `0` gets 30 of asset 2 — the cyclic trade
completes, every leg delivered to the right party at the right asset. Decided on the real-kernel fixture
(the per-leg credit mechanism is `release_delivers`); CONSERVATION (§4) guarantees nothing was minted to
fund these credits — the value came out of the holding-store. -/
theorem settle_delivers :
    ((runSwap swap0 fundedLegs).bind (fun k => settleSwap k fundedIds)).map
      (fun k => (k.bal 1 0, k.bal 2 1, k.bal 0 2)) = some (30, 30, 30) := by decide

/-! ### The LIVENESS TEETH — a settle of a non-locked / wrong id DELIVERS NOTHING (no phantom credit).

The discriminating counter-instances: liveness is not vacuous "everything settles". A release whose id
names NO parked record (or whose target is not parked) fails fail-closed (`none`) — it credits NObody.
Two teeth: settling a WRONG id against the locked swap is `none`, and settling the funded leg ids against
a NON-LOCKED state (the bare `swap0`, whose `escrows` is empty) is `none` — no phantom delivery. -/

/-- **`settle_wrong_id_no_delivery` (TEETH — a wrong id credits nobody).** Settling escrow id `999` —
which no leg parked — against the locked swap FAILS (`none`): there is no parked record to release, so no
counterparty is credited. The settle-liveness gate has teeth: you cannot pull value for an id that names
no parked escrow. -/
theorem settle_wrong_id_no_delivery :
    ((runSwap swap0 fundedLegs).bind (fun k => settleSwap k [999])).isSome = false := by decide

/-- **`settle_unlocked_no_delivery` (TEETH — settling a NON-LOCKED swap delivers nothing).** Settling the
funded leg ids `[10,11,12]` against the BARE `swap0` (which was never locked — `swap0.escrows = []`) FAILS
(`none`): with no parked records, no release can succeed, so NO counterparty is credited. There is no
phantom delivery — settlement requires a prior lock. This discriminates real settlement (`settle_completes`,
which DOES advance) from a no-op masquerade. -/
theorem settle_unlocked_no_delivery : settleSwap swap0 fundedIds = none := by decide

/-! ## 8. `#eval` smoke — the swap's load-bearing bits, decided by the model alone. -/

-- pre-state combined per-asset measure: each of assets 0,1,2 totals 100 (cell c holds 100 of asset c).
#guard (recTotalAssetWithEscrow swap0 0, recTotalAssetWithEscrow swap0 1, recTotalAssetWithEscrow swap0 2) == (100, 100, 100)  -- (100, 100, 100)
-- FUNDED swap LOCKS all 3 legs: succeeds, parks 3 records, combined measure UNCHANGED at every asset.
#guard (runSwap swap0 fundedLegs).isSome                                                                    -- true
#guard (runSwap swap0 fundedLegs).map (fun k => k.escrows.length) == some 3                                 -- some 3 (all parked)
#guard ((runSwap swap0 fundedLegs).map (fun k =>
        (recTotalAssetWithEscrow k 0, recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 2))) == some (100, 100, 100)  -- some (100, 100, 100) — CONSERVED
-- but the BARE ledgers genuinely dropped at each escrowed asset (value moved into the holding-store):
#guard ((runSwap swap0 fundedLegs).map (fun k =>
        (recTotalAsset k 0, recTotalAsset k 1, recTotalAsset k 2))) == some (70, 70, 70)                    -- some (70, 70, 70) — bare DOWN
#guard ((runSwap swap0 fundedLegs).map (fun k =>
        (escrowHeldAsset k 0, escrowHeldAsset k 1, escrowHeldAsset k 2))) == some (30, 30, 30)              -- some (30, 30, 30) — held UP
-- UNDERFUNDED swap is REJECTED (party 2 has 0 of asset 0): fold fails, rollback to pre-state.
#guard (runSwap swap0 underfundedLegs).isSome == false                                                     -- false
-- the rollback leaves EVERY asset's combined measure (and bare ledger) exactly at the pre-state:
#guard (recTotalAssetWithEscrow (atomicSwap swap0 underfundedLegs) 0,
       recTotalAssetWithEscrow (atomicSwap swap0 underfundedLegs) 1,
       recTotalAssetWithEscrow (atomicSwap swap0 underfundedLegs) 2) == (100, 100, 100)                     -- (100, 100, 100) — UNCHANGED
#guard (recTotalAsset (atomicSwap swap0 underfundedLegs) 0,
       recTotalAsset (atomicSwap swap0 underfundedLegs) 1,
       recTotalAsset (atomicSwap swap0 underfundedLegs) 2) == (100, 100, 100)                               -- (100, 100, 100) — no leg moved
#guard (atomicSwap swap0 underfundedLegs).escrows.length == 0                                               -- 0 — nothing parked
-- LIVENESS ◇: the funded+locked swap CAN always settle (no deadlock) and DELIVERS each counterparty.
#guard ((runSwap swap0 fundedLegs).bind (fun k => settleSwap k fundedIds)).isSome                           -- true — reaches settlement
#guard (((runSwap swap0 fundedLegs).bind (fun k => settleSwap k fundedIds)).map (fun k => (k.bal 1 0, k.bal 2 1, k.bal 0 2))) == some (30, 30, 30)  -- some (30, 30, 30) — delivered
#guard (((runSwap swap0 fundedLegs).bind (fun k => settleSwap k fundedIds)).map (fun k =>
        (recTotalAssetWithEscrow k 0, recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 2))) == some (100, 100, 100)  -- some (100, 100, 100) — conserved end-to-end
-- LIVENESS TEETH: a wrong id / a non-locked swap delivers NOTHING (no phantom credit).
#guard ((runSwap swap0 fundedLegs).bind (fun k => settleSwap k [999])).isSome == false                      -- false — wrong id, no delivery
#guard (settleSwap swap0 fundedIds).isSome == false                                                         -- false — never locked, no delivery

/-! ## 9. Axiom hygiene — every keystone pinned to the standard kernel triple.

`#assert_axioms` walks each keystone and errors if any escapes `{propext, Classical.choice,
Quot.sound}`. -/

#assert_axioms runSwap_none_rolls_back
#assert_axioms runSwap_some_commits
#assert_axioms lockLeg_conserves
#assert_axioms runSwap_conserves
#assert_axioms atomicSwap_conserves
#assert_axioms settleSwap_conserves
#assert_axioms swap_conserves_end_to_end
#assert_axioms lockLeg_authorized
#assert_axioms swap_all_legs_authorized
#assert_axioms release_only_parked
#assert_axioms unauthorized_lock_rejected
#assert_axioms funded_swap_commits
#assert_axioms underfunded_swap_rejected
#assert_axioms underfunded_rolls_back
#assert_axioms funded_swap_conserves
#assert_axioms release_completes_of_parked
#assert_axioms release_delivers
#assert_axioms settle_completes
#assert_axioms settle_completes_get
#assert_axioms settle_delivers
#assert_axioms settle_wrong_id_no_delivery
#assert_axioms settle_unlocked_no_delivery

end Dregg2.Apps.AtomicSwap
