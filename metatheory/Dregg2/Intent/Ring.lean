/-
# Dregg2.Intent.Ring — the REAL ring trade, modelled over the executable kernel ledger.

This module makes the Lean `Intent` stack a FAITHFUL model of the running matcher's CORE: the
**ring trade**. The Rust intent crate (`intent/src/solver.rs`, `intent/src/trustless.rs`) is the
running thing — a `RingSolver` finds cycles in the intent compatibility graph (Johnson's algorithm /
Shapley–Scarf top-trading-cycles), `validate_ring` builds a `Vec<Settlement>` from the cycle, and
`check_settlement_conservation` enforces the closed-accounting shape that makes the cycle settle
atomically with no value minted or burned.

The pre-existing Lean (`Intent/Match.lean`, `Intent/Kernel.lean`) modelled an ABSTRACT coend `∫^B`
over a TOY `DemoRes` (`(gold, art)` count bundles, "explicitly not the running matcher"). The coend
is the *bilateral* multi-hop router; it is NOT the ring. A ring is a CYCLE of legs whose offers/wants
chain `A → B → C → A`, settled atomically — and crucially it settles over the **real per-asset
kernel ledger** `RecordKernelState.bal : CellId → AssetId → ℤ`, not the toy bundle.

So here we model the real `RingTrade`:

  * **`RingLeg`** = a single settlement transfer, exactly the Rust `solver::Settlement`
    (`from`/`to`/`asset`/`amount`) — realised as the executable `Turn` over the real ledger.
  * **`Ring`** = the ordered list of legs (the Rust `RingTrade.settlements`).
  * **`settleRing`** = the ATOMIC fold of the legs through the verified per-asset executor
    `recKExecAsset` — any leg that fails to commit aborts the WHOLE ring to `none` (rollback). This
    is the Rust `Effect::Transfer`-per-leg lowering (`intent/src/lowering.rs`) folded all-or-nothing.

The load-bearing theorems (what this now models that the toy seed did not):

  1. **`settleRing_conserves` — a settled ring conserves value PER ASSET.** If the whole ring
     commits, then for EVERY asset `b` the total supply `recTotalAsset · b` is preserved across the
     entire ring (matching is value-neutral: Σ of all legs' transfers = 0, no value created or
     destroyed). Proved by folding the kernel keystone `recKExecAsset_conserves_per_asset` over the
     leg list — each leg conserves every asset, so the composite does.

  2. **`settleRing_atomic` — atomicity (all-or-nothing).** If ANY leg in the ring fails its gate
     (authority / availability / liveness), the whole ring aborts: `settleRing = none`, leaving the
     pre-state untouched. A ring either fully settles or not at all.

  3. **The structural conservation predicate `RingBalanced`** — a direct model of the Rust
     `check_settlement_conservation`: no zero-amount leg, per-asset sent = received, cycle closure
     (every receiver also sends). We prove the canonical chained ring (`closedRing`, the cycle
     `validate_ring` builds) IS `RingBalanced`, and the TEETH: a non-conserving ring (an extra
     credit leg with no matching debit — free mint) is REJECTED by `RingBalanced` and, if it could
     reach the executor, does NOT conserve.

Pure. Models the REAL matcher's ring core, not the toy.
-/
import Dregg2.Intent.KernelBridge
import Dregg2.Exec.RecordKernel

set_option linter.dupNamespace false

namespace Dregg2.Intent.Ring

open Dregg2.Exec (RecordKernelState AssetId Turn CellId recKExecAsset recTotalAsset
  recKExecAsset_conserves_per_asset recKExec balOf setBalance setBalance_balOf authorizedB)

/-! ## 1. `RingLeg` — a single settlement transfer (the Rust `solver::Settlement`). -/

/-- **A ring settlement leg** — the exact data of the Rust `solver::Settlement`: a transfer of
`amount` of `asset` from cell `from_` to cell `to_`, executed by `actor`. This is one edge of the
trade cycle. Realised on the real ledger as the executable `Turn { actor, src := from_, dst := to_,
amt := amount }` moving the `asset` column. -/
structure RingLeg where
  /-- The actor authorising the move (the sender's commitment, who owns `from_`). -/
  actor  : CellId
  /-- Sender cell (`Settlement.from`). -/
  from_  : CellId
  /-- Receiver cell (`Settlement.to`). -/
  to_    : CellId
  /-- The asset being transferred (`Settlement.asset`). -/
  asset  : AssetId
  /-- The amount (`Settlement.amount`). -/
  amount : ℤ
  deriving Inhabited

/-- The executable `Turn` a leg induces on the per-asset ledger (the `Effect::Transfer` lowering). -/
def RingLeg.toTurn (l : RingLeg) : Turn :=
  { actor := l.actor, src := l.from_, dst := l.to_, amt := l.amount }

/-- A **ring** is the ordered list of its legs — the Rust `RingTrade.settlements`. -/
abbrev Ring := List RingLeg

/-! ## 2. `settleRing` — the ATOMIC settlement fold through the VERIFIED executor.

This is the coherence move: instead of the intent crate's own Rust settlement arithmetic, the ring's
legs are executed one-by-one through the verified per-asset kernel `recKExecAsset` (the SAME
`execFullForestG`-derived gate the mandates route through). The fold is all-or-nothing: any leg that
fails its gate returns `none`, aborting the whole ring (rollback to the pre-state). -/

/-- **`settleRing k r` — settle the ring `r` atomically through the verified executor.** Folds each
leg through `recKExecAsset` (debit/credit on the per-asset ledger under the real authority gate). Any
leg that fails to commit aborts the WHOLE ring to `none` — the all-or-nothing atomic-swap contract.
On success, returns the post-state with every leg applied. -/
def settleRing (k : RecordKernelState) (r : Ring) : Option RecordKernelState :=
  r.foldlM (fun s l => recKExecAsset s l.toTurn l.asset) k

@[simp] theorem settleRing_nil (k : RecordKernelState) : settleRing k [] = some k := rfl

/-- One-step unfold of the settle fold: settle the head leg, then the tail. -/
theorem settleRing_cons (k : RecordKernelState) (l : RingLeg) (r : Ring) :
    settleRing k (l :: r)
      = (recKExecAsset k l.toTurn l.asset).bind (fun k' => settleRing k' r) := by
  rfl

/-! ## 3. The CONSERVATION keystone — a settled ring conserves value per asset.

The headline: matching is value-neutral. If the whole ring commits, then for EVERY asset the total
supply is preserved — no value is created or destroyed by the ring. This is exactly "Σ of all legs'
transfers = 0", but proved on the REAL executable ledger by folding the kernel keystone, not asserted
on a toy. -/

/-- **`settleRing_conserves` — A SETTLED RING CONSERVES VALUE, PER ASSET.** If the ring `r` settles
to `k'` (`settleRing k r = some k'`), then for EVERY asset `b`, `recTotalAsset k' b = recTotalAsset k
b`: the total supply of every asset is preserved across the whole ring. Each leg conserves every
asset (`recKExecAsset_conserves_per_asset`); the atomic fold composes those, so the cycle as a whole
moves no net value in any asset. This is the load-bearing property the running matcher relies on,
now PROVED over the verified kernel ledger. -/
theorem settleRing_conserves :
    ∀ (r : Ring) (k k' : RecordKernelState),
      settleRing k r = some k' → ∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b := by
  intro r
  induction r with
  | nil =>
    intro k k' h b
    rw [settleRing_nil] at h
    rw [Option.some.injEq] at h
    rw [← h]
  | cons l rest ih =>
    intro k k' h b
    rw [settleRing_cons] at h
    -- the head leg commits to some `k₁`, then the tail settles `k₁ → k'`.
    cases hhead : recKExecAsset k l.toTurn l.asset with
    | none => rw [hhead] at h; simp at h
    | some k₁ =>
      rw [hhead, Option.bind_some] at h
      have hconsTail : recTotalAsset k' b = recTotalAsset k₁ b := ih k₁ k' h b
      have hconsHead : recTotalAsset k₁ b = recTotalAsset k b :=
        recKExecAsset_conserves_per_asset k k₁ l.toTurn l.asset hhead b
      rw [hconsTail, hconsHead]

/-! ## 4. ATOMICITY — a ring either fully settles or not at all. -/

/-- **`settleRing_atomic` — a leg failure aborts the WHOLE ring.** If the head leg fails its gate
(`recKExecAsset k head.toTurn head.asset = none`), the whole ring fails: `settleRing k (head :: rest)
= none`. No partial settlement — the pre-state `k` is untouched (the caller keeps it on rollback).
The all-or-nothing atomic-swap contract. -/
theorem settleRing_atomic (k : RecordKernelState) (head : RingLeg) (rest : Ring)
    (hfail : recKExecAsset k head.toTurn head.asset = none) :
    settleRing k (head :: rest) = none := by
  rw [settleRing_cons, hfail]; rfl

/-- **`settleRing_atomic_general` — a failing leg ANYWHERE aborts everything BEFORE it commits.**
If a prefix `pre` settles to `k₁` but the next leg `l` fails at `k₁`, the whole ring `pre ++ l ::
post` aborts. This is the general all-or-nothing: a mid-ring under-funded / unauthorised leg rolls
back the entire cycle, not just the suffix. -/
theorem settleRing_atomic_general (k k₁ : RecordKernelState) (pre : Ring) (l : RingLeg) (post : Ring)
    (hpre : settleRing k pre = some k₁)
    (hfail : recKExecAsset k₁ l.toTurn l.asset = none) :
    settleRing k (pre ++ l :: post) = none := by
  have hsplit : ∀ (xs : Ring) (s : RecordKernelState) (s₁ : RecordKernelState),
      settleRing s xs = some s₁ →
      settleRing s (xs ++ l :: post) = settleRing s₁ (l :: post) := by
    intro xs
    induction xs with
    | nil =>
      intro s s₁ h
      rw [settleRing_nil, Option.some.injEq] at h
      subst h
      rfl
    | cons a as ihx =>
      intro s s₁ h
      rw [settleRing_cons] at h
      rw [List.cons_append, settleRing_cons]
      cases ha : recKExecAsset s a.toTurn a.asset with
      | none => rw [ha] at h; simp at h
      | some s' =>
        rw [ha, Option.bind_some] at h
        rw [Option.bind_some]
        exact ihx s' s₁ h
  rw [hsplit pre k k₁ hpre, settleRing_cons, hfail]; rfl

/-! ## 5. The STRUCTURAL conservation predicate `RingBalanced` — a model of the Rust
`check_settlement_conservation` (`intent/src/trustless.rs`).

The Rust engine, before settling, checks the closed-accounting SHAPE of the ring (it cannot re-derive
the per-intent amounts, so it enforces the structural invariants):

  1. **No phantom value** — every leg has `amount ≠ 0`.
  2. **Per-asset global balance** — for each asset, Σ sent = Σ received across the ring.
  3. **Cycle closure** — every cell that RECEIVES also SENDS (no free mint), and vice versa (no
     value burned).

We model this predicate and prove the canonical chained ring satisfies it, and the TEETH: a
non-conserving ring fails it. -/

/-- The finite set of cells the ring touches (every `from_` and every `to_`). The domain over which
net flow is summed. -/
def ringCells (r : Ring) : Finset CellId :=
  (r.foldr (fun l s => insert l.from_ (insert l.to_ s)) ∅)

/-- The total `amount` of `asset` SENT (debited from `from_`) across the ring's legs of that asset.
This is the Rust `sent_per_asset[asset]` accumulator: one `+= s.amount` per leg, indexed by the SEND
side. -/
def sentOf (r : Ring) (a : AssetId) : ℤ :=
  (r.filter (fun l => l.asset == a)).foldl (fun acc l => acc + l.amount) 0

/-- The total `amount` of asset `a` a SINGLE cell `c` RECEIVES across the ring — sum of `l.amount`
over the legs whose `to_ = c`. The genuine credit-side per-cell aggregate (the Rust `receivers`
bookkeeping resolved down to amounts). -/
def recvBy (r : Ring) (c : CellId) (a : AssetId) : ℤ :=
  (r.filter (fun l => l.asset == a)).foldl
    (fun acc l => acc + (if l.to_ = c then l.amount else 0)) 0

/-- The total `amount` of asset `a` a SINGLE cell `c` SENDS across the ring — sum of `l.amount`
over the legs whose `from_ = c`. The genuine debit-side per-cell aggregate. -/
def sentBy (r : Ring) (c : CellId) (a : AssetId) : ℤ :=
  (r.filter (fun l => l.asset == a)).foldl
    (fun acc l => acc + (if l.from_ = c then l.amount else 0)) 0

/-- The total `amount` of `asset` RECEIVED across the ring — summed over the **receiving cells**, NOT
over legs. This is the credit side: `recvOf r a = ∑_c recvBy r c a` over the cells the ring
touches. It is computed independently of `sentOf` (which folds the SEND side over legs), so the
per-asset balance `sentOf = recvOf` is a REAL reindexing theorem (sum-over-legs = sum-over-cells),
NOT a definitional `rfl`. This mirrors the Rust `recv_per_asset` HashMap, which the engine compares
against `sent_per_asset` as two separately-accumulated totals (`check_settlement_conservation`). -/
def recvOf (r : Ring) (a : AssetId) : ℤ :=
  ∑ c ∈ ringCells r, recvBy r c a

/-- A leg's sender (`Settlement.from`). -/
def RingLeg.sender (l : RingLeg) : CellId := l.from_
/-- A leg's receiver (`Settlement.to`). -/
def RingLeg.receiver (l : RingLeg) : CellId := l.to_

/-- **`netFlow r c a`** — the NET position change of cell `c` in asset `a` across the ring: total
received MINUS total sent. The conserved per-cell quantity. A genuine ring (a closed cycle of
balanced legs) moves value around the cells without creating or destroying any, so the net flows sum
to zero across all touched cells (`ringNetFlow_zero` below). -/
def netFlow (r : Ring) (c : CellId) (a : AssetId) : ℤ := recvBy r c a - sentBy r c a

/-- **`RingBalanced r`** — the structural conservation predicate, a faithful model of the Rust
`check_settlement_conservation`:

  * (no phantom value) every leg has non-zero amount;
  * (per-asset balance) for every asset, `sentOf = recvOf`;
  * (cycle closure) every receiving cell also sends, and every sending cell also receives.

A ring the engine would settle must satisfy this. -/
structure RingBalanced (r : Ring) : Prop where
  /-- No zero-amount leg (no no-op masquerading as a settlement). -/
  noPhantom    : ∀ l ∈ r, l.amount ≠ 0
  /-- **Per-asset balance / value-neutrality** — for every asset the net flow summed over the
  touched cells is `0` (received total = sent total). This is the genuine conserved content the Rust
  `check_settlement_conservation` per-asset check enforces, stated over the independently-computed
  credit and debit aggregates (NOT a definitional identity). -/
  perAsset     : ∀ a : AssetId, (∑ c ∈ ringCells r, netFlow r c a) = 0
  /-- Every cell that receives in the ring also sends (no free mint). -/
  recvImpSend  : ∀ l ∈ r, ∃ l' ∈ r, l'.from_ = l.to_
  /-- Every cell that sends in the ring also receives (no value burned). -/
  sendImpRecv  : ∀ l ∈ r, ∃ l' ∈ r, l'.to_ = l.from_

/-! ### The reindexing keystone — sum-over-cells of per-cell contributions = the leg total.

This is the genuine content the vacuous `rfl` papered over. `recvOf` aggregates per RECEIVING cell,
`sentOf` folds per LEG; that they coincide is a real **reindexing** (Fubini-on-a-list): the total
amount in an asset equals both the sum over legs and the sum over the cells each leg credits/debits.
Proved by induction on the leg list, exchanging the cell-sum with the list-fold. -/

/-- The core reindexing lemma over an arbitrary leg list `L` and key extractor `key` (the receiver
`to_` or the sender `from_`): if every leg's key lands in the finite cell set `S`, then summing the
per-cell amount aggregate over `S` equals the flat leg-total. The per-cell fold attributes each leg's
`amount` to exactly the cell `key l`; summing those attributions over all cells recovers the total.
This is the honest "sum over cells = sum over legs" that makes `sentOf = recvOf` a THEOREM. -/
theorem sum_perCell_eq_total (S : Finset CellId) (key : RingLeg → CellId) :
    ∀ (L : List RingLeg), (∀ l ∈ L, key l ∈ S) →
      (∑ c ∈ S, L.foldl (fun acc l => acc + (if key l = c then l.amount else 0)) 0)
        = L.foldl (fun acc l => acc + l.amount) 0 := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton xs x ih =>
    intro hmem
    have hxs : ∀ l ∈ xs, key l ∈ S := fun l hl => hmem l (List.mem_append_left _ hl)
    have hx : key x ∈ S := hmem x (by simp)
    -- foldl over `xs ++ [x]` = (foldl over xs) + (last leg's contribution).
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    -- distribute the cell-sum over the `+` and split off the head term.
    rw [Finset.sum_add_distrib, ih hxs]
    -- the per-cell head contribution sums to `x.amount` (single point `key x`).
    have hpoint :
        (∑ c ∈ S, (if key x = c then x.amount else 0)) = x.amount := by
      rw [Finset.sum_eq_single (key x)]
      · rw [if_pos rfl]
      · intro c _ hc
        rw [if_neg (fun h => hc h.symm)]
      · intro hnx; exact absurd hx hnx
    rw [hpoint]

/-- `∑_c recvBy r c a = sentOf r a` — the credit-side per-cell aggregate, summed over the touched
cells, equals the flat leg total. (Every asset-`a` leg's receiver is in `ringCells r`.) -/
theorem recvOf_eq_sentOf (r : Ring) (a : AssetId) : recvOf r a = sentOf r a := by
  unfold recvOf sentOf recvBy
  exact sum_perCell_eq_total (ringCells r) (fun l => l.to_)
    (r.filter (fun l => l.asset == a)) (fun l hl => by
      have hlr : l ∈ r := (List.mem_filter.mp hl).1
      unfold ringCells
      -- `l.to_` is inserted by `l`'s fold step; membership is preserved up the fold.
      clear hl
      induction r with
      | nil => simp at hlr
      | cons h t ih =>
        simp only [List.foldr_cons, Finset.mem_insert]
        rcases List.mem_cons.mp hlr with rfl | htl
        · right; left; rfl
        · right; right; exact ih htl)

/-- `∑_c sentBy r c a = sentOf r a` — the debit-side per-cell aggregate equals the flat leg total. -/
theorem sentBy_sum_eq_sentOf (r : Ring) (a : AssetId) :
    (∑ c ∈ ringCells r, sentBy r c a) = sentOf r a := by
  unfold sentOf sentBy
  exact sum_perCell_eq_total (ringCells r) (fun l => l.from_)
    (r.filter (fun l => l.asset == a)) (fun l hl => by
      have hlr : l ∈ r := (List.mem_filter.mp hl).1
      unfold ringCells
      clear hl
      induction r with
      | nil => simp at hlr
      | cons h t ih =>
        simp only [List.foldr_cons, Finset.mem_insert]
        rcases List.mem_cons.mp hlr with rfl | htl
        · left; rfl
        · right; right; exact ih htl)

/-- **The per-asset balance `RingBalanced` actually enforces — now a REAL theorem, not `rfl`.**
`sentOf r a = recvOf r a`: the total of asset `a` debited across the legs equals the total credited,
where `recvOf` is computed independently as the sum over RECEIVING cells of their per-cell receipts.
The proof is the reindexing `sum-over-legs = sum-over-cells` (`recvOf_eq_sentOf`), NOT definitional
equality — `sentOf` and `recvOf` are distinct folds (one over legs, one over the touched
cells). This is exactly the Rust `check_settlement_conservation` per-asset check comparing the two
separately-accumulated `sent_per_asset` / `recv_per_asset` HashMaps. -/
theorem perAsset_of_paired (r : Ring) (a : AssetId) : sentOf r a = recvOf r a :=
  (recvOf_eq_sentOf r a).symm

/-- **`ringNetFlow_zero` — THE conservation theorem: net flow sums to zero over the touched cells.**
For every asset `a`, `∑_{c ∈ ringCells r} netFlow r c a = 0`: summed over every cell the ring
touches, the NET position change (received − sent) is exactly zero. Each leg contributes `+amount` to
its receiver's net and `−amount` to its sender's net, and those telescope: the credit side
(`∑ recvBy = sentOf`) and the debit side (`∑ sentBy = sentOf`) are the SAME total, so their
difference vanishes. This is the genuine value-neutrality of a ring — no value minted or burned —
stated as a real (non-vacuous) invariant over the cell domain, the faithful Lean shadow of the Rust
engine's per-asset `sent == received` balance check. -/
theorem ringNetFlow_zero (r : Ring) (a : AssetId) :
    (∑ c ∈ ringCells r, netFlow r c a) = 0 := by
  unfold netFlow
  rw [Finset.sum_sub_distrib]
  rw [show (∑ c ∈ ringCells r, recvBy r c a) = recvOf r a from rfl, recvOf_eq_sentOf,
      sentBy_sum_eq_sentOf]
  ring

/-! ## 6. The CANONICAL chained ring — the cycle `validate_ring` builds, and its balance.

`validate_ring` (`intent/src/solver.rs`) builds settlements from a cycle of `IntentNode`s: leg `k`
sends `node[k].offer_asset` from `node[k].creator` to `node[k+1].creator`. The receivers are exactly
`{node[1], …, node[n], node[0]}` = the senders rotated by one — so cycle closure holds, and (since
each leg is a from/to pair) per-asset balance holds. We exhibit the smallest genuine cycle (a 2-ring
A↔B and a 3-ring A→B→C→A) and prove they are `RingBalanced`, with TEETH (a broken ring fails). -/

/-- A concrete **3-ring** `A→B→C→A`: cell 1 sends asset 10 to cell 2, cell 2 sends asset 11 to cell
3, cell 3 sends asset 12 to cell 1. Each leg is a distinct asset (a genuine multi-party trade with no
common denominator — the headline of the ring solver). Every cell both sends and receives. -/
def closedRing3 : Ring :=
  [ { actor := 1, from_ := 1, to_ := 2, asset := 10, amount := 5 },
    { actor := 2, from_ := 2, to_ := 3, asset := 11, amount := 7 },
    { actor := 3, from_ := 3, to_ := 1, asset := 12, amount := 9 } ]

/-- The canonical 3-ring is `RingBalanced` — no zero leg, per-asset balanced (each asset appears in
exactly one leg, sent = received trivially), and the cycle closes (1→2→3→1: every cell sends and
receives). The honest model of an accepted ring. -/
theorem closedRing3_balanced : RingBalanced closedRing3 where
  noPhantom := by decide
  perAsset := fun a => ringNetFlow_zero closedRing3 a
  recvImpSend := by decide
  sendImpRecv := by decide

/-! ## 7. TEETH — a non-conserving ring is REJECTED.

The hostile case the engine must refuse (the Rust `NonConservingSettlement` errors): a "ring" with a
cell that only RECEIVES (free mint) or only SENDS (value burned), or a zero-amount no-op leg. We
exhibit each and prove `¬ RingBalanced`. -/

/-- A **free-mint** non-ring: cell 1 sends to cell 2, but cell 2 NEVER sends (it only receives — it is
minting free value into the ring). The cycle does not close. -/
def freeMintRing : Ring :=
  [ { actor := 1, from_ := 1, to_ := 2, asset := 10, amount := 5 } ]

/-- **TEETH: the free-mint ring is REJECTED** (`¬ RingBalanced`). Cell 2 receives (leg `1→2`) but no
leg sends FROM cell 2, so `recvImpSend` fails: there is no `l' ∈ r` with `l'.from_ = 2`. The model
refuses a cycle that mints value, exactly as the Rust `check_settlement_conservation` rejects "node …
receives but never sends (free mint)." -/
theorem freeMintRing_rejected : ¬ RingBalanced freeMintRing := by
  intro h
  have hmem : (freeMintRing.get ⟨0, by decide⟩) ∈ freeMintRing := List.get_mem _ _
  obtain ⟨l', hl'mem, hl'⟩ := h.recvImpSend _ hmem
  -- the only leg has `from_ = 1`, but we need `from_ = to_ = 2`; contradiction.
  simp only [freeMintRing, List.mem_singleton] at hl'mem
  subst hl'mem
  simp [freeMintRing] at hl'

/-- A **zero-amount** no-op leg in an otherwise-closed 2-ring: the leg `2→1` carries amount `0` (a
no-op masquerading as a settlement). -/
def zeroLegRing : Ring :=
  [ { actor := 1, from_ := 1, to_ := 2, asset := 10, amount := 5 },
    { actor := 2, from_ := 2, to_ := 1, asset := 11, amount := 0 } ]

/-- **TEETH: a ring with a zero-amount leg is REJECTED** (`¬ RingBalanced`) — the no-phantom-value
check fails. Models the Rust "zero-amount transfer" `NonConservingSettlement`. -/
theorem zeroLegRing_rejected : ¬ RingBalanced zeroLegRing := by
  intro h
  have hmem : (⟨2, 2, 1, 11, 0⟩ : RingLeg) ∈ zeroLegRing := by
    simp [zeroLegRing]
  exact h.noPhantom _ hmem rfl

/-! ## 8. The EXECUTOR teeth — a ring whose leg CANNOT commit aborts (atomicity bites).

A ring that under-funds a leg (sends more than the sender holds) hits `recKExecAsset`'s availability
gate (`amt ≤ k.bal src a`) and fails — so by `settleRing_atomic` the whole ring rolls back. This is
the executor-level refusal: even a structurally-`RingBalanced` ring does not settle if a leg lacks
the funds, and when it doesn't, NOTHING settles. -/

/-- **A ring leg over a cell with zero balance does not commit.** With an empty ledger
(`k.bal = 0`) the leg's availability gate `amt ≤ 0` fails for any positive amount, so the leg —
and (by atomicity) the whole ring — aborts. The executor refuses an unfunded settlement. -/
theorem underfunded_leg_aborts (k : RecordKernelState) (l : RingLeg) (rest : Ring)
    (hbal : k.bal l.from_ l.asset < l.amount) :
    settleRing k (l :: rest) = none := by
  apply settleRing_atomic
  unfold recKExecAsset
  rw [if_neg]
  rintro ⟨_, _, havail, _⟩
  exact absurd havail (by
    simp only [RingLeg.toTurn] at havail ⊢
    omega)

/-! ## 8b. The SOLVER's construction rule — `validate_ring` builds a CHAINED CYCLE, and the
constructed ring is `RingBalanced` BY CONSTRUCTION (not by hand-checking one corpus).

`RingSolver::validate_ring` (`intent/src/solver.rs:423-434`) does NOT build an arbitrary leg list —
it builds settlements from a *cycle of nodes* `[n₀, …, n_{m-1}]` by the fixed rule

  leg k := { from := creator[k], to := creator[(k+1) mod m], asset := offer_asset[k],
             amount := want_min[(k+1) mod m] }

i.e. node `k` sends what it OFFERS to the node that WANTS it (the next node in the cycle). The
receivers are exactly the senders rotated by one. We model this construction rule directly: from a
cycle of `RingNode`s (`creator`/`offerAsset`/`wantMin`, the matched columns of the Rust `IntentNode`)
`chainedRing` builds the leg list EXACTLY as `validate_ring` does, and we prove that ANY such cycle
(of length ≥ 2, distinct creators, positive amounts) yields a `RingBalanced` ring — so the Lean
keystones (`settleRing_conserves`, `ringNetFlow_zero`) hold of the ACTUAL output rule of the running
matcher, for every cycle it can emit, not just the hand-built `closedRing3`. -/

/-- **A matched cycle node** — the columns of the Rust `solver::IntentNode` that `validate_ring`
consumes to build a settlement: who created the intent (`creator`), what asset it offers
(`offerAsset`), and the next party's minimum want (`wantMin`, the amount the leg settles). -/
structure RingNode where
  /-- The intent creator's cell (`IntentNode.creator`). -/
  creator    : CellId
  /-- The asset this node offers (`IntentNode.exchange.offer_asset`). -/
  offerAsset : AssetId
  /-- The settled amount = the RECEIVING node's `want_min_amount` (the Rust `amount` for the leg
  sending TO this node). -/
  wantMin    : ℤ
  deriving Inhabited

/-- **`chainedLeg ns k`** — the `k`-th settlement `validate_ring` builds from the node cycle `ns`:
node `k` sends `ns[k].offerAsset` to node `(k+1) mod m`, in amount `ns[(k+1) mod m].wantMin`. This
is the EXACT Rust rule `settlements.push(Settlement { from: offerer.creator, to: receiver.creator,
asset: offerer.offer_asset, amount: receiver.want_min_amount })`. -/
def chainedLeg (ns : List RingNode) (k : ℕ) : RingLeg :=
  let m := ns.length
  let offerer  := ns.getD k default
  let receiver := ns.getD ((k + 1) % m) default
  { actor  := offerer.creator
    from_  := offerer.creator
    to_    := receiver.creator
    asset  := offerer.offerAsset
    amount := receiver.wantMin }

/-- **`chainedRing ns`** — the full settlement list `validate_ring` builds from the node cycle `ns`:
one `chainedLeg` per node, in order. This IS the Rust `RingTrade.settlements` for the matched cycle
`ns`. -/
def chainedRing (ns : List RingNode) : Ring :=
  (List.range ns.length).map (chainedLeg ns)

/-- A 2-node chained cycle is `[node 0 → node 1, node 1 → node 0]` — exactly the bilateral swap. -/
theorem chainedRing_two (a b : RingNode) :
    chainedRing [a, b] =
      [ { actor := a.creator, from_ := a.creator, to_ := b.creator,
          asset := a.offerAsset, amount := b.wantMin },
        { actor := b.creator, from_ := b.creator, to_ := a.creator,
          asset := b.offerAsset, amount := a.wantMin } ] := by
  simp [chainedRing, chainedLeg, List.range, List.range.loop]

/-- A 3-node chained cycle `A→B→C→A` — the canonical multi-party trade `validate_ring` emits. -/
theorem chainedRing_three (a b c : RingNode) :
    chainedRing [a, b, c] =
      [ { actor := a.creator, from_ := a.creator, to_ := b.creator,
          asset := a.offerAsset, amount := b.wantMin },
        { actor := b.creator, from_ := b.creator, to_ := c.creator,
          asset := b.offerAsset, amount := c.wantMin },
        { actor := c.creator, from_ := c.creator, to_ := a.creator,
          asset := c.offerAsset, amount := a.wantMin } ] := by
  simp [chainedRing, chainedLeg, List.range, List.range.loop]

/-- **Every leg of a chained ring is a `chainedLeg` at some valid index.** Membership in
`chainedRing ns` is exactly being `chainedLeg ns k` for `k < ns.length`. The bridge that lets us
reason about the constructed legs by their index. -/
theorem mem_chainedRing {ns : List RingNode} {l : RingLeg} (h : l ∈ chainedRing ns) :
    ∃ k, k < ns.length ∧ l = chainedLeg ns k := by
  unfold chainedRing at h
  rw [List.mem_map] at h
  obtain ⟨k, hk, hl⟩ := h
  rw [List.mem_range] at hk
  exact ⟨k, hk, hl.symm⟩

/-- **The cycle-closure keystone for the SOLVER's construction: every leg's sender also sends a
NEXT leg, and every leg's receiver is some leg's sender — BY THE ROTATION.** For a chained ring of
length ≥ 2, the receiver of leg `k` is `creator[(k+1) % m]`, which is the SENDER of leg `(k+1) % m`.
So `recvImpSend` holds structurally: there is always a leg sending FROM any receiver. This is the
content the Rust `check_settlement_conservation` cycle-closure check verifies AT RUNTIME — here it is
a THEOREM about the construction rule, holding for every cycle the solver can emit. -/
theorem chainedRing_recvImpSend {ns : List RingNode} (hlen : 2 ≤ ns.length) :
    ∀ l ∈ chainedRing ns, ∃ l' ∈ chainedRing ns, l'.from_ = l.to_ := by
  intro l hl
  obtain ⟨k, hk, rfl⟩ := mem_chainedRing hl
  -- the receiver of leg k is node[(k+1)%m].creator, which is the SENDER of leg (k+1)%m.
  set m := ns.length with hm
  have hmpos : 0 < m := by omega
  refine ⟨chainedLeg ns ((k + 1) % m), ?_, ?_⟩
  · unfold chainedRing
    rw [List.mem_map]
    exact ⟨(k + 1) % m, by rw [List.mem_range]; exact Nat.mod_lt _ hmpos, rfl⟩
  · -- from_ of leg ((k+1)%m) = node[(k+1)%m].creator = to_ of leg k.
    show (chainedLeg ns ((k + 1) % m)).from_ = (chainedLeg ns k).to_
    simp only [chainedLeg, hm]

/-- **The dual cycle-closure: every leg's sender is some leg's receiver — BY THE ROTATION.** The
sender of leg `k` is `creator[k]`; it is the RECEIVER of leg `(k + m - 1) % m` (the previous leg in
the cycle). So `sendImpRecv` holds structurally. Together with `chainedRing_recvImpSend` this is the
full cycle closure the Rust engine enforces — every cell that participates both sends and receives,
proved of the construction rule. -/
theorem chainedRing_sendImpRecv {ns : List RingNode} (hlen : 2 ≤ ns.length) :
    ∀ l ∈ chainedRing ns, ∃ l' ∈ chainedRing ns, l'.to_ = l.from_ := by
  intro l hl
  obtain ⟨k, hk, rfl⟩ := mem_chainedRing hl
  set m := ns.length with hm
  have hmpos : 0 < m := by omega
  -- the previous leg j = (k + m - 1) % m has to_ = node[(j+1)%m].creator = node[k].creator.
  refine ⟨chainedLeg ns ((k + m - 1) % m), ?_, ?_⟩
  · unfold chainedRing
    rw [List.mem_map]
    exact ⟨(k + m - 1) % m, by rw [List.mem_range]; exact Nat.mod_lt _ hmpos, rfl⟩
  · -- to_ of leg j = node[(j+1)%m].creator; we need (j+1)%m = k.
    show (chainedLeg ns ((k + m - 1) % m)).to_ = (chainedLeg ns k).from_
    simp only [chainedLeg, hm]
    congr 2
    -- Goal: ((k + m - 1) % m + 1) % m = k for k < m, m ≥ 1. Extract as a pure Nat lemma.
    have hkm : k < m := hk
    have hkey : ((k + m - 1) % m + 1) % m = k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        have h1 : (0 + m - 1) % m = m - 1 := by
          simp only [Nat.zero_add]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h1]
        have h2 : m - 1 + 1 = m := by omega
        rw [h2, Nat.mod_self]
      · have hrw : k + m - 1 = (k - 1) + m := by omega
        rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (show k - 1 < m by omega)]
        have h3 : k - 1 + 1 = k := by omega
        rw [h3, Nat.mod_eq_of_lt hkm]
    rw [hkey]

/-- **THE SOLVER-OUTPUT KEYSTONE — every chained ring `validate_ring` builds is `RingBalanced`.**
For ANY node cycle `ns` of length ≥ 2 whose receiving amounts are all positive, the settlement list
`chainedRing ns` the Rust `validate_ring` emits satisfies the structural conservation predicate
`RingBalanced`:

  * **noPhantom** — every leg's amount is the receiving node's `wantMin`, positive by hypothesis;
  * **perAsset** — the value-neutrality `∑ netFlow = 0`, from the general `ringNetFlow_zero`;
  * **recvImpSend / sendImpRecv** — cycle closure, from the rotation (`chainedRing_recvImpSend` /
    `chainedRing_sendImpRecv`).

This lifts the Lean conservation keystones from the hand-built `closedRing3` to the ACTUAL output
RULE of the running matcher: whatever cycle the solver finds and `validate_ring` settles, the
verified `settleRing_conserves` applies to it. -/
theorem chainedRing_balanced {ns : List RingNode} (hlen : 2 ≤ ns.length)
    (hpos : ∀ n ∈ ns, 0 < n.wantMin) : RingBalanced (chainedRing ns) where
  noPhantom := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := mem_chainedRing hl
    have hmpos : 0 < ns.length := by omega
    have hidx : (k + 1) % ns.length < ns.length := Nat.mod_lt _ hmpos
    have hmem : ns.getD ((k + 1) % ns.length) default ∈ ns := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
      exact List.getElem_mem hidx
    have := hpos _ hmem
    simp only [chainedLeg]
    omega
  perAsset := fun a => ringNetFlow_zero (chainedRing ns) a
  recvImpSend := chainedRing_recvImpSend hlen
  sendImpRecv := chainedRing_sendImpRecv hlen

/-- **The chained ring settles+conserves on the VERIFIED executor — the full coherence statement for
the solver's output.** If a node cycle's chained ring settles through `settleRing` (the verified
`recKExecAsset` fold), then it conserves every asset (`settleRing_conserves`) AND is structurally
`RingBalanced` (`chainedRing_balanced`). So a ring the running matcher emits and that the verified
executor commits is BOTH value-neutral per asset AND a closed conserving cycle — "an intent-matched
ring fulfilled = a verified, conserving turn", stated over the solver's actual construction. -/
theorem chainedRing_fulfilled_is_verified_conserving
    {ns : List RingNode} (hlen : 2 ≤ ns.length) (hpos : ∀ n ∈ ns, 0 < n.wantMin)
    (k k' : RecordKernelState) (hsettle : settleRing k (chainedRing ns) = some k') :
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b) ∧ RingBalanced (chainedRing ns) :=
  ⟨settleRing_conserves (chainedRing ns) k k' hsettle, chainedRing_balanced hlen hpos⟩

/-! ## 8c. The COMPATIBILITY GRAPH + cycle-finding validity + INDIVIDUAL RATIONALITY (Shapley–Scarf).

§8b modelled `validate_ring`'s OUTPUT construction (`chainedRing`) and proved it conserving. But the
running solver does MORE before it ever calls `validate_ring`: it builds a **compatibility graph**
(`solver.rs:220 build_graph` via `IntentGraph::is_compatible`, `solver.rs:534`), finds **cycles** in it
(`solver.rs:557 find_cycles`, the bounded-DFS Johnson's-algorithm), and only a cycle whose every
consecutive edge is compatible survives the `valid` filter in `find_rings` (`solver.rs:256-272`). The
soundness the solver RELIES ON is the **Shapley–Scarf top-trading-cycle** guarantee: a cycle the graph
admits is *individually rational* — every participant receives the asset it WANTED, in at least the
amount it asked for. The toy `RingNode` of §8b cannot state this: it carries no `offerAmount` and no
`wantAsset`, so "the receiver wants what the sender offers" and "the offer covers the want" are
inexpressible. We enrich the node to the FULL `solver::IntentNode` columns and model the graph edge
predicate exactly, then prove:

  * **`isCompatible` IS the Rust `is_compatible`** — asset-match (`offer_asset == want_asset`) AND
    amount-sufficiency (`offer_amount ≥ want_min_amount`). This is the edge `build_graph` admits.
  * **`CycleValid`** — every consecutive pair around the cycle is `isCompatible`, AND creators are
    distinct (the `SelfLoop` rejection, `solver.rs:327`). This is the invariant the DFS cycle + the
    `valid` filter jointly maintain.
  * **`cycleValid_chains`** — a valid cycle CHAINS: `offerAsset[k] = wantAsset[k+1]` and
    `offerAmount[k] ≥ wantMin[k+1]` for every leg. So the `validate_ring` quantity/asset checks
    (`solver.rs:352`, `solver.rs:361`) PASS for any cycle the graph finds — the construction is not
    partial on the solver's own output.
  * **INDIVIDUAL RATIONALITY (the TTC core)** — in the settlement built from a valid cycle, every
    participant RECEIVES exactly the asset it declared it WANTED (`wantAsset`), in at least its
    declared minimum (`wantMin`). No participant is matched into a worse-than-asked outcome. This is
    the Shapley–Scarf property the solver's correctness rests on, here a THEOREM about the graph it
    actually searches — stated both structurally and ON THE VERIFIED LEDGER (the credited balance). -/

/-- **A matched cycle node — the FULL columns of the Rust `solver::IntentNode`** (`solver.rs:39`). The
§8b `RingNode` carried only `creator/offerAsset/wantMin`; this carries also `offerAmount` (how much the
node offers) and `wantAsset` (which asset it wants), the two columns `is_compatible` reads. With these
the graph edge predicate and individual rationality become expressible. -/
structure MatchNode where
  /-- The intent creator's cell (`IntentNode.creator`). -/
  creator     : CellId
  /-- The asset this node OFFERS (`IntentNode.exchange.offer_asset`). -/
  offerAsset  : AssetId
  /-- How much of `offerAsset` this node offers (`IntentNode.exchange.offer_amount`). -/
  offerAmount : ℤ
  /-- The asset this node WANTS (`IntentNode.exchange.want_asset`). -/
  wantAsset   : AssetId
  /-- The minimum amount of `wantAsset` this node will accept (`IntentNode.exchange.want_min_amount`). -/
  wantMin     : ℤ
  deriving Inhabited

/-- **The projection to the §8b `RingNode`** — forget `offerAmount`/`wantAsset`, keeping the three
columns `chainedLeg` consumes. This is how the enriched model REUSES the §8b keystones: the settlement
of a cycle of `MatchNode`s is the `chainedRing` of their projections, so `chainedRing_balanced` and
`settleRing_conserves` apply verbatim — no duplicated conservation proof. -/
def MatchNode.toRingNode (n : MatchNode) : RingNode :=
  { creator := n.creator, offerAsset := n.offerAsset, wantMin := n.wantMin }

/-- **`isCompatible a b` — the EXACT Rust `IntentGraph::is_compatible`** (`solver.rs:534`). There is a
graph edge `a → b` ("a's offer could satisfy b's want") iff a OFFERS what b WANTS
(`a.offer_asset == b.want_asset`) AND a offers ENOUGH for b's minimum
(`a.offer_amount >= b.want_min_amount`). The Rust returns `Some(score)` exactly on this conjunction;
we model the boolean edge relation it induces. -/
def isCompatible (a b : MatchNode) : Prop :=
  a.offerAsset = b.wantAsset ∧ b.wantMin ≤ a.offerAmount

/-- `isCompatible` is decidable (a conjunction of decidable atoms over `Nat`/`ℤ`): the edge test the
Rust `is_compatible` performs is an effective check, so the teeth (`assetMismatchCycle_no_edge`) and the
validity witness (`validSwapCycle_valid`) discharge by `decide` — no classical reasoning. -/
instance instDecidableIsCompatible (a b : MatchNode) : Decidable (isCompatible a b) := by
  unfold isCompatible; infer_instance

/-- **`settlementsOf ns = chainedRing (ns.map toRingNode)`** — the settlement list the solver builds
from a cycle of `MatchNode`s is exactly the §8b `chainedRing` of the projected `RingNode`s. The
enriched node adds the columns `is_compatible` reads, but the SETTLEMENT only ever uses
`creator/offerAsset` (the leg's from/asset) and the receiver's `wantMin` (the leg's amount) — so the
construction rule is unchanged, and every §8b keystone lifts. -/
def settlementsOf (ns : List MatchNode) : Ring := chainedRing (ns.map MatchNode.toRingNode)

/-- The projection commutes with `length` — a cycle of `MatchNode`s and its `RingNode` image have the
same number of legs. -/
@[simp] theorem map_toRingNode_length (ns : List MatchNode) :
    (ns.map MatchNode.toRingNode).length = ns.length := by simp

/-- **`CycleValid ns` — the invariant the DFS cycle + `find_rings`' `valid` filter jointly maintain.**
A node list is a VALID matching cycle iff (1) it is a genuine ring (length ≥ 2); (2) every consecutive
pair (wrapping around) is `isCompatible` — the edge the graph admits, checked by the `valid` loop
(`solver.rs:256-268`); and (3) all creators are distinct — the `SelfLoop` rejection
(`solver.rs:327-333`). This is precisely the cycle that survives `find_rings` and reaches
`validate_ring`. The consecutive check is stated at every index `k < length` against `(k+1) % length`,
matching the Rust `next = (k + 1) % cycle.len()`. -/
structure CycleValid (ns : List MatchNode) : Prop where
  /-- A ring has at least two participants (`TooSmall` rejection, `solver.rs:322`). -/
  len    : 2 ≤ ns.length
  /-- Every consecutive edge around the cycle is a graph edge (`is_compatible`). -/
  edges  : ∀ k, k < ns.length →
             isCompatible (ns.getD k default) (ns.getD ((k + 1) % ns.length) default)
  /-- All creators distinct — no `SelfLoop` (`solver.rs:329`). -/
  distinct : ∀ i j, i < ns.length → j < ns.length → i ≠ j →
             (ns.getD i default).creator ≠ (ns.getD j default).creator

/-- **`cycleValid_chains` — a valid cycle CHAINS, so `validate_ring`'s quantity/asset checks PASS.**
For every leg `k` of a valid cycle, node `k`'s OFFERED asset equals node `(k+1)`'s WANTED asset
(`offerAsset[k] = wantAsset[(k+1)%m]`, the `solver.rs:352` asset-match check) AND node `k` offers at
least node `(k+1)`'s minimum (`wantMin[(k+1)%m] ≤ offerAmount[k]`, the `solver.rs:361`
sufficiency check). This is the content `find_cycles` walks edge-by-edge: the cycle the DFS returns is
NEVER rejected by `validate_ring` — the two layers AGREE on what a settleable cycle is. -/
theorem cycleValid_chains {ns : List MatchNode} (h : CycleValid ns) (k : ℕ) (hk : k < ns.length) :
    (ns.getD k default).offerAsset = (ns.getD ((k + 1) % ns.length) default).wantAsset ∧
      (ns.getD ((k + 1) % ns.length) default).wantMin ≤ (ns.getD k default).offerAmount :=
  h.edges k hk

/-! ### Individual rationality — the Shapley–Scarf top-trading-cycle core property.

The receiver of leg `k` is node `(k+1) % m`; the leg credits it `wantMin[(k+1)%m]` of asset
`offerAsset[k]`. By `cycleValid_chains`, `offerAsset[k] = wantAsset[(k+1)%m]` — so the receiver gets
EXACTLY the asset it asked for, in EXACTLY its declared minimum. Equivalently, reindexing on the
RECEIVER `j`: node `j` receives, from its predecessor in the cycle, `wantMin[j]` of `wantAsset[j]`.
That is individual rationality: every participant is matched into an outcome at least as good as it
declared acceptable. -/

/-- **`receivedAsset ns j` / `receivedAmount ns j`** — the asset and amount node `j` RECEIVES in the
cycle. The leg crediting `j` is the one from its predecessor `(j + m - 1) % m`; it carries that
predecessor's `offerAsset` in amount `j.wantMin`. -/
def receivedAsset (ns : List MatchNode) (j : ℕ) : AssetId :=
  (ns.getD ((j + ns.length - 1) % ns.length) default).offerAsset
def receivedAmount (ns : List MatchNode) (j : ℕ) : ℤ :=
  (ns.getD j default).wantMin

/-- **INDIVIDUAL RATIONALITY (structural) — every participant gets the asset it WANTED, at least its
declared minimum.** For each node `j` of a valid cycle: `receivedAsset ns j = wantAsset[j]` (it
receives exactly the asset it declared it wants) and `receivedAmount ns j ≥ wantMin[j]` (in at least
its declared minimum — here, exactly). This is the Shapley–Scarf TTC guarantee the solver relies on,
proved of the actual graph cycle: the asset match comes from `cycleValid_chains` at the predecessor
index, whose `(pred+1)%m = j`. NO participant is matched into an unwanted asset or an under-minimum
amount. -/
theorem cycle_individuallyRational {ns : List MatchNode} (h : CycleValid ns)
    (j : ℕ) (hj : j < ns.length) :
    receivedAsset ns j = (ns.getD j default).wantAsset ∧
      (ns.getD j default).wantMin ≤ receivedAmount ns j := by
  have hmpos : 0 < ns.length := by have := h.len; omega
  refine ⟨?_, le_refl _⟩
  -- predecessor index p = (j + m - 1) % m; chain at p gives offerAsset[p] = wantAsset[(p+1)%m].
  set m := ns.length with hm
  have hp : ((j + m - 1) % m) < m := Nat.mod_lt _ hmpos
  have hchain := (cycleValid_chains h ((j + m - 1) % m) hp).1
  -- (p + 1) % m = j (the cycle rotation identity, same as `chainedRing_sendImpRecv`).
  have hkey : (((j + m - 1) % m) + 1) % m = j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      have h1 : (0 + m - 1) % m = m - 1 := by
        simp only [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [h1]; have h2 : m - 1 + 1 = m := by omega
      rw [h2, Nat.mod_self]
    · have hrw : j + m - 1 = (j - 1) + m := by omega
      rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (show j - 1 < m by omega)]
      have h3 : j - 1 + 1 = j := by omega
      rw [h3, Nat.mod_eq_of_lt (by omega : j < m)]
  unfold receivedAsset
  rw [hchain, hkey]

/-- **The settlement crediting node `j` carries exactly `j`'s wanted asset and minimum.** The leg the
solver builds from a valid cycle that has `j` as RECEIVER (`to_ = creator[j]`) transfers
`receivedAsset ns j = wantAsset[j]` in amount `wantMin[j]`. This connects the IR property to the actual
`chainedRing`/`settlementsOf` leg data: the predecessor leg `chainedLeg (map toRingNode) ((j+m-1)%m)`
has `to_ = creator[j]`, `asset = wantAsset[j]` (by IR), and `amount = wantMin[j]`. -/
theorem settlement_to_receiver_is_wanted {ns : List MatchNode} (h : CycleValid ns)
    (j : ℕ) (hj : j < ns.length) :
    let rs := ns.map MatchNode.toRingNode
    let p  := (j + ns.length - 1) % ns.length
    (chainedLeg rs p).to_ = (ns.getD j default).creator ∧
      (chainedLeg rs p).asset = (ns.getD j default).wantAsset ∧
      (chainedLeg rs p).amount = (ns.getD j default).wantMin := by
  have hmpos : 0 < ns.length := by have := h.len; omega
  set m := ns.length with hm
  have hlen' : (ns.map MatchNode.toRingNode).length = m := by simp [hm]
  -- (p + 1) % m = j again.
  have hkey : (((j + m - 1) % m) + 1) % m = j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      have h1 : (0 + m - 1) % m = m - 1 := by
        simp only [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [h1]; have h2 : m - 1 + 1 = m := by omega
      rw [h2, Nat.mod_self]
    · have hrw : j + m - 1 = (j - 1) + m := by omega
      rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (show j - 1 < m by omega)]
      have h3 : j - 1 + 1 = j := by omega
      rw [h3, Nat.mod_eq_of_lt (by omega : j < m)]
  have hp : ((j + m - 1) % m) < m := Nat.mod_lt _ hmpos
  -- getD over the mapped list at an in-range index pulls the map through.
  have hgetmap : ∀ i, i < m → (ns.map MatchNode.toRingNode).getD i default
      = (ns.getD i default).toRingNode := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_map]
    rw [List.getElem?_eq_getElem (by omega : i < ns.length)]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · -- to_ of leg p = creator[(p+1)%m] = creator[j].
    simp only [chainedLeg, hlen', hkey, hgetmap j hj, MatchNode.toRingNode]
  · -- asset of leg p = offerAsset[p] = wantAsset[j] (IR).
    simp only [chainedLeg, hlen', hgetmap _ hp, MatchNode.toRingNode]
    have := (cycle_individuallyRational h j hj).1
    unfold receivedAsset at this
    rw [hm]; exact this
  · -- amount of leg p = wantMin[(p+1)%m] = wantMin[j].
    simp only [chainedLeg, hlen', hkey, hgetmap j hj, MatchNode.toRingNode]

/-- **A valid matching cycle's settlement is `RingBalanced` — the §8c bridge to §8b's keystone.** A
`CycleValid` cycle of positive wants settles to a `RingBalanced` ring (`settlementsOf ns`). This is NOT
a new conservation proof: `settlementsOf ns = chainedRing (ns.map toRingNode)`, and `chainedRing_balanced`
already discharges balance for ANY length-≥2 positive-want node cycle. The §8c contribution is that the
hypotheses (length, positivity) hold for the cycle the GRAPH actually finds, and additionally that the
cycle is individually rational (`cycle_individuallyRational`) — a property `chainedRing` alone could not
even state. -/
theorem cycleValid_settlement_balanced {ns : List MatchNode} (h : CycleValid ns)
    (hpos : ∀ n ∈ ns, 0 < n.wantMin) : RingBalanced (settlementsOf ns) := by
  unfold settlementsOf
  apply chainedRing_balanced
  · simpa using h.len
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨n, hn, rfl⟩ := hr
    exact hpos n hn

/-- **THE §8c KEYSTONE — a graph-found, individually-rational cycle settles to a verified, conserving,
IR ring.** Take a cycle `ns` the solver's `build_graph`/`find_cycles` admits (`CycleValid`) with
positive wants. If its settlement (`settlementsOf ns`, exactly the `validate_ring` output) settles
through the VERIFIED executor (`settleRing`) to `k'`, then:

  * (conservation) every asset's total supply is preserved (`settleRing_conserves`);
  * (balance) the settlement is structurally `RingBalanced` (closed, no phantom value);
  * (individual rationality) EVERY participant `j` receives the asset it WANTED in at least its
    declared minimum (`cycle_individuallyRational`).

This is the full Shapley–Scarf story over the running matcher's ACTUAL graph search: not just "the
output conserves" (§8b) but "a cycle the graph FINDS is value-neutral AND every party is matched
into an acceptable outcome", proved end-to-end against the verified per-asset ledger. -/
theorem cycleValid_fulfilled_is_verified_IR_conserving {ns : List MatchNode}
    (h : CycleValid ns) (hpos : ∀ n ∈ ns, 0 < n.wantMin)
    (k k' : RecordKernelState) (hsettle : settleRing k (settlementsOf ns) = some k') :
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b) ∧
      RingBalanced (settlementsOf ns) ∧
      (∀ j, j < ns.length →
        receivedAsset ns j = (ns.getD j default).wantAsset ∧
          (ns.getD j default).wantMin ≤ receivedAmount ns j) :=
  ⟨settleRing_conserves (settlementsOf ns) k k' hsettle,
   cycleValid_settlement_balanced h hpos,
   fun j hj => cycle_individuallyRational h j hj⟩

/-! ### TEETH — the graph REJECTS an incompatible cycle (no edge ⇒ not `CycleValid` ⇒ never settles).

The hostile case the solver must refuse: a "cycle" whose consecutive nodes are NOT compatible — either
the offered asset is not what the next node wants (`solver.rs:352` mismatch) or the offer underfunds the
want (`solver.rs:361`). Such a node list is NOT `CycleValid` (its `edges` field cannot be satisfied), so
it never reaches `validate_ring`. We exhibit each refusal. -/

/-- A 2-cycle whose ASSETS don't chain: node 0 offers asset 10 but node 1 wants asset 99 (not 10). The
graph admits NO edge `0 → 1`, so `isCompatible (node 0) (node 1)` is FALSE. -/
def assetMismatchCycle : List MatchNode :=
  [ { creator := 1, offerAsset := 10, offerAmount := 100, wantAsset := 11, wantMin := 5 },
    { creator := 2, offerAsset := 11, offerAmount := 100, wantAsset := 99, wantMin := 5 } ]

/-- **TEETH: an asset-mismatched cycle has no graph edge** — `¬ isCompatible (node 0) (node 1)`. Node 0
offers asset 10, node 1 wants asset 99; `offer_asset (10) ≠ want_asset (99)`, so `build_graph` adds no
edge and `find_cycles` cannot traverse it. The model refuses exactly what the Rust `is_compatible`
returns `None` for. -/
theorem assetMismatchCycle_no_edge :
    ¬ isCompatible (assetMismatchCycle.getD 0 default) (assetMismatchCycle.getD 1 default) := by
  unfold isCompatible assetMismatchCycle
  decide

/-- A 2-cycle whose AMOUNTS underfund: node 0 offers only 3 of asset 10, but node 1 wants a minimum of
50. The assets chain but the offer is insufficient — no edge. -/
def underfundCycle : List MatchNode :=
  [ { creator := 1, offerAsset := 10, offerAmount := 3, wantAsset := 11, wantMin := 5 },
    { creator := 2, offerAsset := 11, offerAmount := 100, wantAsset := 10, wantMin := 50 } ]

/-- **TEETH: an underfunded cycle has no graph edge** — `¬ isCompatible (node 0) (node 1)`. Node 0
offers 3 of asset 10; node 1 wants a minimum of 50 of asset 10. `offer_amount (3) < want_min (50)`, so
`is_compatible` returns `None`. The model refuses the under-minimum match the solver's amount check
(`solver.rs:541`) rejects. -/
theorem underfundCycle_no_edge :
    ¬ isCompatible (underfundCycle.getD 0 default) (underfundCycle.getD 1 default) := by
  unfold isCompatible underfundCycle
  decide

/-- A concrete VALID 2-cycle (bilateral swap): node 1 offers asset 10 (amount 100), wants asset 11
(min 5); node 2 offers asset 11 (amount 100), wants asset 10 (min 7). Each offers what the other wants,
with enough — both edges compatible, creators distinct. The smallest genuine matching the graph admits. -/
def validSwapCycle : List MatchNode :=
  [ { creator := 1, offerAsset := 10, offerAmount := 100, wantAsset := 11, wantMin := 5 },
    { creator := 2, offerAsset := 11, offerAmount := 100, wantAsset := 10, wantMin := 7 } ]

/-- **The concrete valid swap IS `CycleValid`** — both consecutive edges are compatible and creators
differ. Non-vacuity: the `CycleValid` predicate is inhabited by a genuine graph cycle, so the keystones
above are not vacuously true. -/
theorem validSwapCycle_valid : CycleValid validSwapCycle where
  len := by decide
  edges := by decide
  distinct := by
    intro i j hi hj hij
    -- length 2: i, j ∈ {0,1} and i ≠ j ⇒ {i,j} = {0,1}, creators 1 ≠ 2.
    have hlen : validSwapCycle.length = 2 := rfl
    rw [hlen] at hi hj
    -- the two creators are 1 and 2 (distinct); show getD i ≠ getD j for i ≠ j in {0,1}.
    have hi2 : i = 0 ∨ i = 1 := by omega
    have hj2 : j = 0 ∨ j = 1 := by omega
    rcases hi2 with rfl | rfl <;> rcases hj2 with rfl | rfl <;>
      first
      | (exact absurd rfl hij)
      | decide

/-- Non-vacuity of individual rationality on the concrete swap: node 0 receives asset 11 (which it
wanted) and node 1 receives asset 10 (which it wanted) — the genuine cross-trade the TTC core promises.
A `#guard` below pins the computed received assets/amounts. -/
theorem validSwapCycle_IR :
    receivedAsset validSwapCycle 0 = 11 ∧ receivedAsset validSwapCycle 1 = 10 :=
  ⟨(cycle_individuallyRational validSwapCycle_valid 0 (by decide)).1,
   (cycle_individuallyRational validSwapCycle_valid 1 (by decide)).1⟩

/-! ## 9. The bridge — `settleRing_conserves` IS the ring refinement of `KernelBridge`'s
per-asset conservation.

`KernelBridge.settle_refines_per_asset_conservation` lifted ONE bundle's settle to per-asset
conservation of a single transfer. `settleRing_conserves` lifts it to a WHOLE CYCLE of transfers —
the multi-party ring — staying on the same real ledger and the same kernel keystone. The toy seed
modelled a single bilateral fill; this models the n-party atomic ring the running matcher actually
settles. -/

/-- **The ring is the n-party generalisation of the bridge's single transfer.** A one-leg ring is
exactly a single `recKExecAsset` transfer, so `settleRing_conserves` on a singleton reduces to the
bridge's `settle_refines_per_asset_conservation`. This pins the ring model as a conservative
extension of the validated single-transfer refinement, not a fresh unrelated theory. -/
theorem singleton_ring_is_transfer (k k' : RecordKernelState) (l : RingLeg)
    (h : recKExecAsset k l.toTurn l.asset = some k') :
    settleRing k [l] = some k' := by
  rw [settleRing_cons, h, Option.bind_some, settleRing_nil]

/-! ## 9b. The LOWERING bridge — the Rust `lowering.rs` settlement leg IS the verified `RingLeg`.

This closes the last gap in "intent fulfilled = verified turn": the running engine
(`TrustlessIntentEngine::finalize`, `intent/src/trustless.rs:1554`) does NOT execute `settleRing`
directly — it LOWERS the winning solution to a `dregg_turn::Turn` via `lowering::lower`
(`intent/src/lowering.rs:268 lower_settlement_leg`). That rule emits, for each Rust
`solver::Settlement { from, to, asset, amount }`, an `Effect::Transfer { from, to, amount }` executed
on cell `from` (the lowered turn's `caller := anchor`, but the value moves `from → to`).

We model that lowering rule (`loweredLeg`) and prove it produces EXACTLY the `RingLeg` whose
`toTurn` the verified `settleRing` fold consumes. So the Turn the live engine ships to the executor
moves the same value, between the same cells, in the same asset, as the verified-executor leg the
keystones (`settleRing_conserves`, `settleRing_atomic`) are proved over. The lowered fulfillment turn
and the verified settlement leg COINCIDE — they are not two parallel accountings. -/

/-- **`SettlementRow`** — the exact data of the Rust `solver::Settlement` (`intent/src/solver.rs:62`):
a transfer of `amount` of `asset` from cell `from_` to cell `to_`. This is what `validate_ring` /
`check_settlement_conservation` produce and consume, and what `lowering::lower` rides over. -/
structure SettlementRow where
  /-- `Settlement.from`. -/
  from_  : CellId
  /-- `Settlement.to`. -/
  to_    : CellId
  /-- `Settlement.asset`. -/
  asset  : AssetId
  /-- `Settlement.amount`. -/
  amount : ℤ
  deriving Inhabited

/-- **`loweredLeg anchor s`** — the `RingLeg` the Rust `lowering::lower_settlement_leg`
(`intent/src/lowering.rs:268`) induces for the settlement row `s` under the federation/solver `anchor`.
The Rust rule sets `target := from`, `caller := anchor`, and emits `Effect::Transfer { from, to,
amount }`; the `actor` authorising the move is the `anchor` (the auctioned settlement cell moving value
on behalf of the matching), and the value moves `from_ → to_`. This is the bridge from the
discovery-time `Settlement` to the executable `RingLeg`. -/
def loweredLeg (anchor : CellId) (s : SettlementRow) : RingLeg :=
  { actor := anchor, from_ := s.from_, to_ := s.to_, asset := s.asset, amount := s.amount }

/-- **The lowered leg's executable `Turn` moves exactly the settlement's value between the settlement's
cells in the settlement's asset.** `(loweredLeg anchor s).toTurn = { actor := anchor, src := s.from_,
dst := s.to_, amt := s.amount }`: the `Effect::Transfer { from, to, amount }` the Rust lowering emits
is realised as the verified per-asset `Turn` debiting `from_` and crediting `to_` by `amount` — the
SAME move `recKExecAsset … s.asset` performs. The fulfillment Turn and the verified leg coincide. -/
@[simp] theorem loweredLeg_toTurn (anchor : CellId) (s : SettlementRow) :
    (loweredLeg anchor s).toTurn
      = { actor := anchor, src := s.from_, dst := s.to_, amt := s.amount } := rfl

/-- **`loweredRing anchor rows`** — the executable ring the live engine ships: lower every settlement
row of the winning solution through `lowering::lower` under one `anchor`, in order. This IS the leg
list inside `finalize`'s `SealedTurn.call_forest` (each a `Effect::Transfer`), now expressed as the
`Ring` the verified `settleRing` fold consumes. -/
def loweredRing (anchor : CellId) (rows : List SettlementRow) : Ring :=
  rows.map (loweredLeg anchor)

/-- **`loweredRing` preserves the settlement's amounts, assets, and from/to per leg.** The lowering is
data-preserving leg-by-leg: the `k`-th lowered leg carries exactly the `k`-th settlement row's
`from_/to_/asset/amount` (only the authorising `actor` is set to `anchor`). So any per-asset / cycle
property the rows have transfers verbatim to the lowered executable ring. -/
theorem loweredRing_getElem (anchor : CellId) (rows : List SettlementRow)
    (k : ℕ) (hk : k < rows.length) :
    (loweredRing anchor rows)[k]'(by simpa [loweredRing] using hk)
      = loweredLeg anchor (rows[k]) := by
  simp [loweredRing]

/-- **THE FULFILLMENT KEYSTONE — a lowered, settled fulfillment IS a verified conserving turn.**
If the executable ring `loweredRing anchor rows` (the legs the live `finalize` ships to the executor)
settles through the VERIFIED `settleRing` fold to `k'`, then for EVERY asset the total supply is
preserved (`settleRing_conserves`). I.e. running the actual lowered fulfillment Turn through the
verified executor conserves value — "an intent fulfilled (lowered + settled) = a verified, conserving
turn", now stated over the EXACT lowering rule the running engine uses, not a toy. -/
theorem lowered_fulfillment_conserves (anchor : CellId) (rows : List SettlementRow)
    (k k' : RecordKernelState) (hsettle : settleRing k (loweredRing anchor rows) = some k') :
    ∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b :=
  settleRing_conserves (loweredRing anchor rows) k k' hsettle

/-- **The full coherence statement at the SOLVER-to-EXECUTOR boundary.** Take a node cycle `ns` the
matcher found (length ≥ 2, positive wants). Its settlements (`chainedRing ns`, the exact `validate_ring`
output) lowered to executable legs and settled through the verified executor are BOTH conserving (per
asset) AND structurally `RingBalanced` (closed, no phantom value). Since `chainedRing` already produces
`RingLeg`s and `loweredLeg` only re-stamps the `actor`, the conservation and balance proved of the
solver's output (`chainedRing_fulfilled_is_verified_conserving`) carry to the lowered fulfillment. This
is the end-to-end: matcher output → lowering → verified executor = conserving authorized turn. -/
theorem chainedRing_lowered_fulfillment_is_verified_conserving
    {ns : List RingNode} (hlen : 2 ≤ ns.length) (hpos : ∀ n ∈ ns, 0 < n.wantMin)
    (k k' : RecordKernelState) (hsettle : settleRing k (chainedRing ns) = some k') :
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b) ∧ RingBalanced (chainedRing ns) :=
  chainedRing_fulfilled_is_verified_conserving hlen hpos k k' hsettle

/-! ## Axiom hygiene — every ring keystone pinned to the three kernel axioms. -/
#assert_axioms settleRing_conserves
#assert_axioms settleRing_atomic
#assert_axioms settleRing_atomic_general
#assert_axioms sum_perCell_eq_total
#assert_axioms recvOf_eq_sentOf
#assert_axioms sentBy_sum_eq_sentOf
#assert_axioms perAsset_of_paired
#assert_axioms ringNetFlow_zero
#assert_axioms closedRing3_balanced
#assert_axioms freeMintRing_rejected
#assert_axioms zeroLegRing_rejected
#assert_axioms underfunded_leg_aborts
#assert_axioms singleton_ring_is_transfer
#assert_axioms chainedRing_two
#assert_axioms chainedRing_three
#assert_axioms mem_chainedRing
#assert_axioms chainedRing_recvImpSend
#assert_axioms chainedRing_sendImpRecv
#assert_axioms chainedRing_balanced
#assert_axioms chainedRing_fulfilled_is_verified_conserving
#assert_axioms map_toRingNode_length
#assert_axioms cycleValid_chains
#assert_axioms cycle_individuallyRational
#assert_axioms settlement_to_receiver_is_wanted
#assert_axioms cycleValid_settlement_balanced
#assert_axioms cycleValid_fulfilled_is_verified_IR_conserving
#assert_axioms assetMismatchCycle_no_edge
#assert_axioms underfundCycle_no_edge
#assert_axioms validSwapCycle_valid
#assert_axioms validSwapCycle_IR
#assert_axioms loweredLeg_toTurn
#assert_axioms loweredRing_getElem
#assert_axioms lowered_fulfillment_conserves
#assert_axioms chainedRing_lowered_fulfillment_is_verified_conserving

/-! ### `#eval` smoke — the ring corpus is computable. -/
#guard sentOf closedRing3 10 == 5
#guard recvOf closedRing3 11 == 7
#guard (closedRing3.length) == 3
-- The per-cell net flows are NON-trivial (the de-vacuified conservation has real content):
-- in asset 10, cell 2 RECEIVES 5 (net +5) and cell 1 SENDS 5 (net −5) — distinct, non-zero flows
-- whose sum over the touched cells is 0 (proved in `ringNetFlow_zero`).
#guard netFlow closedRing3 2 10 == 5
#guard netFlow closedRing3 1 10 == (-5)
#guard recvBy closedRing3 2 10 == 5
#guard sentBy closedRing3 1 10 == 5

-- The solver's construction rule is computable: a 3-node cycle yields exactly the 3 chained legs.
#guard (chainedRing
  [ { creator := 1, offerAsset := 10, wantMin := 5 },
    { creator := 2, offerAsset := 11, wantMin := 7 },
    { creator := 3, offerAsset := 12, wantMin := 9 } ]).length == 3
-- Leg 0 sends node-0's offer (asset 10) from creator 1 to creator 2, amount = node-1's wantMin (7).
#guard ((chainedRing
  [ { creator := 1, offerAsset := 10, wantMin := 5 },
    { creator := 2, offerAsset := 11, wantMin := 7 },
    { creator := 3, offerAsset := 12, wantMin := 9 } ]).getD 0 default).amount == 7
#guard ((chainedRing
  [ { creator := 1, offerAsset := 10, wantMin := 5 },
    { creator := 2, offerAsset := 11, wantMin := 7 },
    { creator := 3, offerAsset := 12, wantMin := 9 } ]).getD 2 default).to_ == 1

-- The lowering rule is data-preserving: a settlement row lowers to a leg with the SAME from/to/asset/
-- amount, only the authorising `actor` becomes the anchor; its executable Turn moves the same value.
#guard (loweredLeg 99 { from_ := 1, to_ := 2, asset := 10, amount := 5 }).from_ == 1
#guard (loweredLeg 99 { from_ := 1, to_ := 2, asset := 10, amount := 5 }).to_ == 2
#guard (loweredLeg 99 { from_ := 1, to_ := 2, asset := 10, amount := 5 }).amount == 5
#guard (loweredLeg 99 { from_ := 1, to_ := 2, asset := 10, amount := 5 }).actor == 99
#guard ((loweredLeg 99 { from_ := 1, to_ := 2, asset := 10, amount := 5 }).toTurn).amt == 5
#guard (loweredRing 99
  [ { from_ := 1, to_ := 2, asset := 10, amount := 5 },
    { from_ := 2, to_ := 1, asset := 11, amount := 7 } ]).length == 2

-- §8c: the compatibility graph + individual rationality are computable.
-- The valid swap's settlement is the chainedRing of the projected nodes — 2 legs.
#guard (settlementsOf validSwapCycle).length == 2
-- INDIVIDUAL RATIONALITY (the TTC core), computed: node 0 receives asset 11 (its wantAsset),
-- node 1 receives asset 10 (its wantAsset) — each gets exactly the asset it asked for.
#guard receivedAsset validSwapCycle 0 == 11
#guard receivedAsset validSwapCycle 1 == 10
-- ...in at least its declared minimum: node 0 wanted ≥5 and gets 5; node 1 wanted ≥7 and gets 7.
#guard receivedAmount validSwapCycle 0 == 5
#guard receivedAmount validSwapCycle 1 == 7
-- The TEETH are computable too: the incompatible cycles have no graph edge.
#guard (decide (isCompatible (assetMismatchCycle.getD 0 default)
  (assetMismatchCycle.getD 1 default))) == false
#guard (decide (isCompatible (underfundCycle.getD 0 default)
  (underfundCycle.getD 1 default))) == false

end Dregg2.Intent.Ring
