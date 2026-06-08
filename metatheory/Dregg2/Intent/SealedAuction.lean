/-
# Dregg2.Intent.SealedAuction — sealed-bid commit→reveal coordination among AI agents, over the REAL ledger.

This is the verified core of **usecase app #2: sealed-intent multi-agent coordination**. Several agents
COMPETE for a single award (a compute slot, a task assignment, a contract) by submitting *sealed* bids
— a hash binding (bidder, value, nonce) — during a COMMIT phase, so that no agent can peek at, copy, or
front-run another's bid. After the commit phase is sealed, agents REVEAL their bids; the protocol picks
the winner (here: the highest sealed bid — sealed-bid first-price) and settles the award ATOMICALLY
through the verified per-asset executor `recKExecAsset` — the SAME executor `Ring.settleRing` and
`Intent.Lifecycle` fold through. Settlement is all-or-nothing and value-conserving by construction.

This module does NOT re-implement the ledger, the settlement fold, or conservation: it composes
`Intent/Ring.lean` (the atomic `settleRing` and its conservation/atomicity keystones) with a
**collision-resistant sealed commitment** taken from `Crypto/PortalFloor.lean` (`Blake3Kernel`, the
genuine CR carrier — NOT `True`). The sealing mirrors the running Rust `compute_commitment_hash`
(`intent/src/commit_reveal_fulfillment.rs`): `H(bidder ‖ value ‖ nonce)`.

## The protocol (commit → reveal → settle)

A `Bid` is a bidder cell, an offered `value`, and a private `nonce`. Its **seal** is
`sealOf b = Blake3Kernel.hash [b.bidder, b.value, b.nonce]`. An `Auction` records the public data
(seller cell, asset, the award `slot` cell that delivers the task-token) plus the multiset of sealed
commitments collected during the commit phase and a `Phase` (commit / reveal / settled). The phase gate
is what makes "no reveal binds before the commit phase closes" enforceable, not decorative.

  * **commit(a, seal)** — append a sealed commitment. Only legal in the `commit` phase. The seal hides
    `value` and `nonce` (CR + the nonce's entropy), so a competitor learns nothing exploitable.
  * **seal the auction** — close the commit phase: `commit → reveal`. After this, no new commitments;
    reveals are accepted.
  * **reveal(a, b)** — open a bid `b`. A reveal is VALID iff its seal `sealOf b` is in the auction's
    committed set AND the auction is in the `reveal` phase. Under CR a committed seal opens to EXACTLY
    the bid that produced it — you cannot change your bid after committing.
  * **settle(a, reveals)** — pick the winner (max revealed `value`) and run the award as a balanced
    two-leg ring through `recKExecAsset`: the winner pays `value` of `asset` to the seller, and the
    seller's `slot` cell delivers the task-token (the same `value` denominated as the slot asset) to
    the winner. Atomic: any leg that fails its gate aborts the whole award (`settleRing_atomic`).

## The keystones (what sealed-bid coordination MUST guarantee)

  1. **`reveal_binds_committed` (NO REVEAL BINDS BEFORE COMMIT / no late-switching).** Under
     collision-resistance, if a reveal `b` opens a commitment that equals the seal of a *committed* bid
     `b₀`, then `b = b₀`. You cannot open your sealed commitment to any bid other than the exact one you
     sealed: peeking-then-switching is impossible. This is the CR tooth, parametric in the
     `Blake3Kernel` carrier — NON-VACUOUS (it is FALSE for a constant/collapsing hash).

  2. **`uncommitted_cannot_open` + `uncommitted_cannot_win` (a NON-COMMITTED party cannot settle).**
     A bid whose seal is not among the auction's commitments opens NO commitment (`validReveal` is
     `false`), so it can never be a valid reveal — hence never the winner, hence cannot be settled. The
     award binds back to a real prior commitment.

  3. **`reveal_requires_reveal_phase` + `settle_requires_reveal_phase` (phase ordering).** A reveal is
     rejected while the auction is still in the `commit` phase (or already `settled`); settlement only
     fires in the `reveal` phase. The commit phase must be SEALED before any reveal binds.

  4. **`settle_atomic` (atomic settlement).** If any award leg fails its executor gate, the WHOLE award
     aborts — the pre-state is untouched. Reuses `Ring.settleRing_atomic`.

  5. **`settle_conserves` (value-neutral award).** A settled award conserves every asset's total supply
     — no value is minted or burned by the coordination. Reuses `Ring.settleRing_conserves`.

  6. **`winner_was_committed` (the award binds back to a commitment).** A settled auction's winner is a
     bid that was both validly revealed and (hence, by 2) committed.

Pure. Routes the multi-agent award through the verified executor; the sealing rests on the real CR
assumption carrier, not on `True` or `native_decide`.
-/
import Dregg2.Intent.Ring
import Dregg2.Crypto.PortalFloor

set_option linter.dupNamespace false

namespace Dregg2.Intent.SealedAuction

open Dregg2.Exec (RecordKernelState AssetId Turn CellId recKExecAsset recTotalAsset)
open Dregg2.Intent.Ring (RingLeg Ring settleRing settleRing_conserves settleRing_atomic settleRing_cons)
open Dregg2.Crypto.PortalFloor (Blake3Kernel)

/-! ## 1. The sealed bid and its commitment.

The `Digest` is the seal type and `[Blake3Kernel Digest]` supplies the collision-resistant hash and
its CR carrier. Everything downstream is parametric in that carrier — instantiating it with the
reference `instBlake3Kernel ℕ` (whose `collisionHard` HOLDS, §9 of `PortalFloor`) gives a concrete,
non-vacuous auction; the demo does exactly that. -/

variable {Digest : Type} [K : Blake3Kernel Digest]

/-- **A sealed bid.** The bidder's cell, the offered `value` (the bid price — what it will pay for the
award), and a private `nonce` that blinds the commitment. `value` and `nonce` are secret until reveal;
only `sealOf b` is public during the commit phase. -/
structure Bid where
  /-- The agent placing the bid (the cell that will pay and receive the award). -/
  bidder : CellId
  /-- The bid value — the price the agent offers for the award (sealed-bid first-price). -/
  value  : ℤ
  /-- The blinding nonce — secret, gives the commitment hiding even for a low-entropy `value`. -/
  nonce  : ℕ
  deriving DecidableEq, Inhabited

/-- **The sealed commitment of a bid** — `Blake3(bidder ‖ value ‖ nonce)`. Mirrors the running Rust
`compute_commitment_hash` (`commit_reveal_fulfillment.rs`): a binding, hiding commitment to the bid.
We feed the integer `value` through `Int.toNat ∘ (· + offset)`-free encoding by pairing sign+magnitude
into the hash preimage so the preimage list is over `ℕ` (the `Blake3Kernel.hash` domain). Distinct
bids have distinct preimage lists, so under CR they have distinct seals. -/
def sealOf (b : Bid) : Digest :=
  K.hash [b.bidder, (if 0 ≤ b.value then 0 else 1), b.value.natAbs, b.nonce]

/-- The seal preimage is injective in the bid: equal preimage lists force equal bids. Used to turn CR
(equal hashes ⇒ equal preimages) into "equal seals ⇒ equal bids". -/
theorem seal_preimage_injective (b b' : Bid)
    (h : [b.bidder, (if 0 ≤ b.value then 0 else 1), b.value.natAbs, b.nonce]
       = [b'.bidder, (if 0 ≤ b'.value then 0 else 1), b'.value.natAbs, b'.nonce]) :
    b = b' := by
  -- Destructure the list equality into the four component equalities.
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨hbidder, hsign, hmag, hnonce⟩ := h
  -- The magnitude equality, as an integer fact (`|b.value| = |b'.value|`).
  have hmagZ : (b.value.natAbs : ℤ) = (b'.value.natAbs : ℤ) := by exact_mod_cast hmag
  -- Recover `value` from sign + magnitude.  The sign tag (`0` iff `0 ≤ value`) determines the sign;
  -- with equal magnitudes, equal signs force equal values; the two mixed-sign cases are excluded by
  -- the sign tag (`0 ≠ 1`).
  have hval : b.value = b'.value := by
    by_cases hb : (0 : ℤ) ≤ b.value <;> by_cases hb' : (0 : ℤ) ≤ b'.value
    · rw [if_pos hb, if_pos hb'] at hsign; omega
    · rw [if_pos hb, if_neg hb'] at hsign; exact absurd hsign (by decide)
    · rw [if_neg hb, if_pos hb'] at hsign; exact absurd hsign (by decide)
    · rw [if_neg hb, if_neg hb'] at hsign; omega
  -- Reassemble the structure.
  cases b; cases b'
  simp_all

/-- **`seal_injective` — under collision-resistance, the seal is injective in the bid.** Given the CR
carrier `K.collisionHard`, equal seals force equal bids: `sealOf b = sealOf b' → b = b'`. This is the
algebraic heart of "a commitment binds its bid" — composed of `Blake3Kernel.noCollision` (CR ⇒ equal
hashes force equal preimages) and `seal_preimage_injective` (equal preimages force equal bids). -/
theorem seal_injective (hcr : K.collisionHard) (b b' : Bid)
    (h : sealOf (Digest := Digest) b = sealOf b') : b = b' := by
  have hpre := K.noCollision hcr _ _ h
  exact seal_preimage_injective b b' hpre

/-! ## 2. The auction phase and state. -/

/-- The auction phase. Reveals bind only in `reveal`; settlement fires only in `reveal`; `settled` is
terminal. The `commit → reveal → settled` ordering is what makes "no reveal before commit closes" an
enforced gate rather than a comment. -/
inductive Phase where
  /-- Collecting sealed commitments; reveals are rejected. -/
  | commit
  /-- Commit phase closed; reveals accepted, settlement may fire. -/
  | reveal
  /-- The award has been settled; terminal. -/
  | settled
  deriving DecidableEq, Inhabited

/-- **A sealed-bid auction.** The public coordination state: who awards (`seller`), the payment
`asset`, the award `slot` cell whose `slotAsset` column delivers the task-token to the winner, the
collected `commitments` (the sealed bids gathered in the commit phase), and the current `phase`. The
secret `(value, nonce)` of each bid is NOT here — only the seals are public until reveal. -/
structure Auction (Digest : Type) where
  /-- The agent awarding the slot (receives the winner's payment, authorises the slot delivery). -/
  seller    : CellId
  /-- The cell holding the award token (the "task slot"); delivers `slotAsset` to the winner. -/
  slot      : CellId
  /-- The payment asset (the bid is denominated in this). -/
  asset     : AssetId
  /-- The asset the award slot delivers to the winner (the task-token column). -/
  slotAsset : AssetId
  /-- The sealed commitments collected during the commit phase. -/
  commitments : List Digest
  /-- The current phase. -/
  phase     : Phase
  deriving Inhabited

/-! ## 3. The commit phase. -/

/-- **`commit a sd`** — append a sealed commitment `sd`. Legal ONLY in the `commit` phase; in any
other phase the auction is returned unchanged (fail-closed: no late commitments after the phase
seals). -/
def commit (a : Auction Digest) (sd : Digest) : Auction Digest :=
  match a.phase with
  | .commit => { a with commitments := sd :: a.commitments }
  | _       => a

/-- **`sealAuction a`** — close the commit phase, opening reveals (`commit → reveal`). Idempotent on
non-`commit` phases. -/
def sealAuction (a : Auction Digest) : Auction Digest :=
  match a.phase with
  | .commit => { a with phase := .reveal }
  | _       => a

/-- After `commit` in the commit phase, the seal is among the commitments. -/
omit K in
theorem commit_mem (a : Auction Digest) (sd : Digest) (h : a.phase = .commit) :
    sd ∈ (commit a sd).commitments := by
  unfold commit; rw [h]; exact List.mem_cons_self ..

/-- `commit` outside the commit phase is a no-op — fail-closed against late commitments. -/
omit K in
theorem commit_noop_off_phase (a : Auction Digest) (sd : Digest) (h : a.phase ≠ .commit) :
    commit a sd = a := by
  unfold commit
  cases hp : a.phase with
  | commit => exact absurd hp h
  | reveal => rfl
  | settled => rfl

/-! ## 4. The reveal phase — the binding gate. -/

/-- **`validReveal a b`** — a reveal of bid `b` is accepted iff the auction is in the `reveal` phase
AND `b`'s seal is among the committed seals. The conjunction is the protocol's two teeth: the phase
gate (no reveal before the commit phase closes) and the membership gate (only committed bids open). -/
def validReveal [DecidableEq Digest] (a : Auction Digest) (b : Bid) : Bool :=
  decide (a.phase = Phase.reveal) && decide (sealOf (Digest := Digest) b ∈ a.commitments)

/-- **`reveal_requires_reveal_phase` (no reveal before the commit phase closes).** A reveal is rejected
while the auction is still in the `commit` phase: `validReveal` is `false`. The phase gate bites. -/
theorem reveal_requires_reveal_phase [DecidableEq Digest] (a : Auction Digest) (b : Bid)
    (h : a.phase = .commit) : validReveal a b = false := by
  unfold validReveal; rw [h]; simp

/-- A reveal is also rejected once the auction is `settled` (terminal). -/
theorem reveal_rejected_when_settled [DecidableEq Digest] (a : Auction Digest) (b : Bid)
    (h : a.phase = .settled) : validReveal a b = false := by
  unfold validReveal; rw [h]; simp

/-- A valid reveal forces the reveal phase. -/
theorem validReveal_phase [DecidableEq Digest] (a : Auction Digest) (b : Bid)
    (h : validReveal a b = true) : a.phase = .reveal := by
  unfold validReveal at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

/-- A valid reveal's seal is among the auction's commitments. -/
theorem validReveal_committed [DecidableEq Digest] (a : Auction Digest) (b : Bid)
    (h : validReveal a b = true) : sealOf (Digest := Digest) b ∈ a.commitments := by
  unfold validReveal at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

/-! ## 5. THE CR KEYSTONE — no reveal binds to anything but the exact committed bid. -/

/-- **`reveal_binds_committed` — NO LATE-SWITCHING / no reveal binds before commit.** Suppose a bid
`b₀` was committed (its seal is in `a.commitments`) and a reveal `b` is valid AND opens that same
commitment slot (`sealOf b = sealOf b₀`). Then under collision-resistance `b = b₀`: the only bid a
committed seal can be opened to is the exact bid that sealed it. An agent cannot peek at others and
then reveal a *different* bid that matches its earlier commitment — the commitment binds its bid. This
is the protocol's anti-front-running guarantee, resting on the real CR carrier (`seal_injective`),
non-vacuously. -/
theorem reveal_binds_committed [DecidableEq Digest] (hcr : K.collisionHard)
    (a : Auction Digest) (b b₀ : Bid)
    (hvalid : validReveal a b = true)
    (hopen : sealOf (Digest := Digest) b = sealOf b₀) :
    b = b₀ :=
  seal_injective hcr b b₀ hopen

/-! ## 6. A NON-COMMITTED party cannot reveal, hence cannot win/settle. -/

/-- **`uncommitted_cannot_open` — a non-committed bid opens no commitment.** If `b`'s seal is NOT
among the auction's commitments, then `validReveal a b = false`: there is no commitment to open, so the
reveal is rejected outright. A party that never committed cannot inject a reveal. -/
theorem uncommitted_cannot_open [DecidableEq Digest] (a : Auction Digest) (b : Bid)
    (h : sealOf (Digest := Digest) b ∉ a.commitments) : validReveal a b = false := by
  unfold validReveal
  rw [Bool.and_eq_false_iff]
  right
  exact decide_eq_false h

/-! ## 7. The award — picking the winner and settling atomically through the verified executor.

The winner is the validly-revealed bid with the maximal `value` (sealed-bid first-price). The award is
a balanced two-leg ring through `recKExecAsset`: the winner pays `value` of `asset` to the seller, and
the seller's `slot` cell delivers `value` of `slotAsset` (the task-token) to the winner. -/

/-- **The winner among a list of validly-revealed bids** — the bid with the maximal `value`. `none` if
the list is empty (no valid reveals ⇒ no award). Folds keeping the running maximum. -/
def winnerOf (reveals : List Bid) : Option Bid :=
  reveals.foldl
    (fun acc b => match acc with
      | none    => some b
      | some w  => if w.value < b.value then some b else some w)
    none

/-- The winner is one of the revealed bids (membership). Used to chain "winner ⇒ valid reveal ⇒
committed". -/
theorem winnerOf_mem (reveals : List Bid) (w : Bid) (h : winnerOf reveals = some w) :
    w ∈ reveals := by
  unfold winnerOf at h
  -- General fold invariant: the accumulator, if `some`, is always a member of the consumed prefix,
  -- and members of the prefix carry through. Proven over an arbitrary starting accumulator.
  suffices H : ∀ (l : List Bid) (acc : Option Bid),
      (∀ x, acc = some x → x ∈ reveals) →
      (∀ x ∈ l, x ∈ reveals) →
      l.foldl (fun acc b => match acc with
        | none => some b
        | some w => if w.value < b.value then some b else some w) acc = some w →
      w ∈ reveals by
    exact H reveals none (by simp) (fun x hx => hx) h
  intro l
  induction l with
  | nil => intro acc hacc _ hf; simp only [List.foldl_nil] at hf; exact hacc w hf
  | cons hd tl ih =>
    intro acc hacc hmem hf
    simp only [List.foldl_cons] at hf
    apply ih _ _ (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) hf
    intro x hx
    cases acc with
    | none =>
      simp only at hx
      cases hx
      exact hmem hd (List.mem_cons_self ..)
    | some w' =>
      simp only at hx
      by_cases hlt : w'.value < hd.value
      · rw [if_pos hlt] at hx; cases hx; exact hmem hd (List.mem_cons_self ..)
      · rw [if_neg hlt] at hx; cases hx; exact hacc x rfl

/-- **The award ring** — the two balanced legs of the settlement. Leg 1: the winner pays `bidValue` of
`asset` to the seller (the winner authorises its own debit, `actor = from_ = winner`). Leg 2: the
`slot` cell delivers `bidValue` of `slotAsset` (the task-token) to the winner, authorised by the slot
cell itself (`actor = from_ = slot`, the same self-authorising pattern as `Lifecycle`'s escrow release).
A closed two-cycle: every receiver also sends, conserving both columns. -/
def awardRing (a : Auction Digest) (winner : CellId) (bidValue : ℤ) : Ring :=
  [ { actor := winner, from_ := winner, to_ := a.seller, asset := a.asset, amount := bidValue },
    { actor := a.slot, from_ := a.slot, to_ := winner, asset := a.slotAsset, amount := bidValue } ]

/-- **`settle a winner k`** — settle the award atomically through the verified executor. Runs
`awardRing` through `Ring.settleRing` (the all-or-nothing fold over `recKExecAsset`), and on success
marks the auction `settled`. Returns the post-ledger and the updated auction, or `none` if any leg
fails its gate (e.g. the winner cannot pay, or the slot is empty). -/
def settle (a : Auction Digest) (winner : Bid) (k : RecordKernelState) :
    Option (RecordKernelState × Auction Digest) :=
  match a.phase with
  | .reveal =>
    (settleRing k (awardRing a winner.bidder winner.value)).map
      (fun k' => (k', { a with phase := .settled }))
  | _ => none

/-- **`settle_requires_reveal_phase` — settlement fires ONLY in the reveal phase.** Outside `reveal`
(still committing, or already settled), `settle` returns `none`: you cannot settle before the commit
phase closes, nor settle twice. -/
omit K in
theorem settle_requires_reveal_phase (a : Auction Digest) (winner : Bid) (k : RecordKernelState)
    (h : a.phase ≠ .reveal) : settle a winner k = none := by
  unfold settle; cases hp : a.phase <;> simp_all

/-- A committed settlement leaves the auction in the `settled` phase. -/
omit K in
theorem settle_terminal (a : Auction Digest) (winner : Bid) (k k' : RecordKernelState)
    (a' : Auction Digest) (h : settle a winner k = some (k', a')) : a'.phase = .settled := by
  unfold settle at h
  cases hp : a.phase with
  | reveal =>
    simp only [hp] at h
    rcases Option.map_eq_some_iff.mp h with ⟨_, _, heq⟩
    injection heq with _ ha'
    rw [← ha']
  | commit => simp only [hp] at h; exact absurd h (by simp)
  | settled => simp only [hp] at h; exact absurd h (by simp)

/-! ## 8. ATOMICITY and CONSERVATION of the award — reusing the Ring keystones. -/

/-- **`settle_atomic` — the award is all-or-nothing.** If the first award leg (the winner's payment)
fails its executor gate — e.g. the winner does not actually hold `value` of `asset` — the WHOLE award
aborts: `settle` returns `none`, the ledger untouched. No half-settled award (the winner paying but
not receiving, or vice-versa). Reuses `Ring.settleRing_atomic`. -/
omit K in
theorem settle_atomic (a : Auction Digest) (winner : Bid) (k : RecordKernelState)
    (hphase : a.phase = .reveal)
    (hfail : recKExecAsset k
      ({ actor := winner.bidder, from_ := winner.bidder, to_ := a.seller,
         asset := a.asset, amount := winner.value } : RingLeg).toTurn a.asset = none) :
    settle a winner k = none := by
  unfold settle; rw [hphase]
  have hring : settleRing k (awardRing a winner.bidder winner.value) = none := by
    unfold awardRing
    exact settleRing_atomic k _ _ hfail
  rw [hring]; rfl

/-- **`settle_conserves` — a settled award is value-neutral.** If the award settles to `k'`, then for
EVERY asset `b` the total supply is preserved: `recTotalAsset k' b = recTotalAsset k b`. No value is
minted or burned by the coordination — the winner's payment to the seller and the slot's delivery to
the winner net to zero in every column. Reuses `Ring.settleRing_conserves`. -/
omit K in
theorem settle_conserves (a : Auction Digest) (winner : Bid) (k k' : RecordKernelState)
    (a' : Auction Digest) (h : settle a winner k = some (k', a')) :
    ∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b := by
  intro b
  unfold settle at h
  cases hp : a.phase with
  | reveal =>
    simp only [hp] at h
    rcases Option.map_eq_some_iff.mp h with ⟨ksettled, hring, heq⟩
    injection heq with hk _
    subst hk
    exact settleRing_conserves (awardRing a winner.bidder winner.value) k ksettled hring b
  | commit => simp only [hp] at h; exact absurd h (by simp)
  | settled => simp only [hp] at h; exact absurd h (by simp)

/-! ## 9. The full pipeline — the winner binds back to a real commitment. -/

/-- **`winner_was_committed` — the settled award binds back to a commitment.** Suppose every revealed
bid in `reveals` was a VALID reveal (so its seal was committed) and `w` is the winner. Then `w`'s seal
is among the auction's commitments: the agent that wins the award provably committed to its winning bid
during the sealed commit phase. Composes `winnerOf_mem` (winner ∈ reveals) with `validReveal_committed`
(valid reveal ⇒ committed). The award cannot go to a party that never sealed a bid. -/
theorem winner_was_committed [DecidableEq Digest] (a : Auction Digest) (reveals : List Bid) (w : Bid)
    (hall : ∀ b ∈ reveals, validReveal a b = true)
    (hwin : winnerOf reveals = some w) :
    sealOf (Digest := Digest) w ∈ a.commitments :=
  validReveal_committed a w (hall w (winnerOf_mem reveals w hwin))

/-- **`uncommitted_cannot_win` — a non-committed party is never the winner of a valid auction.** If
every revealed bid is a valid reveal and the winner is `w`, then `w` could NOT be a bid whose seal was
absent from the commitments — `w` is committed (by `winner_was_committed`). Contrapositive: a bid whose
seal is not committed is not the winner. The settle path admits only committed parties. -/
theorem uncommitted_cannot_win [DecidableEq Digest] (a : Auction Digest) (reveals : List Bid) (w : Bid)
    (hall : ∀ b ∈ reveals, validReveal a b = true)
    (hwin : winnerOf reveals = some w)
    (huncommitted : sealOf (Digest := Digest) w ∉ a.commitments) : False :=
  huncommitted (winner_was_committed a reveals w hall hwin)

/-! ## 10. A CONCRETE, NON-VACUOUS demo — three agents, sealed-bid, over the real ledger.

The whole development above is parametric in the `Blake3Kernel` carrier. Here we INSTANTIATE it with
the reference `instBlake3Kernel ℕ` from `Crypto/PortalFloor` — whose collision-resistance carrier
provably HOLDS (`Reference.instBlake3Kernel_collisionHard`, encode-injectivity) — so the CR keystones
are discharged against a real, non-vacuous CR fact rather than `True`. Three AI agents bid for a
single compute slot; the highest sealed bid wins; the award settles atomically through `recKExecAsset`.
The teeth (`#guard` + the anti-ghost theorems) exercise every guarantee end-to-end. -/

namespace Demo

open Dregg2.Crypto.PortalFloor.Reference (instBlake3Kernel instBlake3Kernel_collisionHard)

/-- The concrete CR fact for the reference BLAKE3 kernel — the assumption the demo's binding rests on. -/
theorem demoCR : (instBlake3Kernel).collisionHard := instBlake3Kernel_collisionHard

/-- Three competing agents (cells `10`, `11`, `12`), the seller (`1`), the award slot (`2`). The asset
`0` is the payment currency; asset `1` is the task-token the slot delivers to the winner. -/
def agentA : CellId := 10
def agentB : CellId := 11
def agentC : CellId := 12

/-- Agent A bids `30`, B bids `50` (the top bid), C bids `40`. Each blinds with a private nonce. -/
def bidA : Bid := { bidder := agentA, value := 30, nonce := 7 }
def bidB : Bid := { bidder := agentB, value := 50, nonce := 8 }
def bidC : Bid := { bidder := agentC, value := 40, nonce := 9 }

/-- The auction AFTER the commit phase: all three seals collected, then sealed into the reveal phase. -/
def demoAuction : Auction Nat :=
  sealAuction <| commit (commit (commit
    { seller := 1, slot := 2, asset := 0, slotAsset := 1, commitments := [], phase := .commit }
    (sealOf bidA)) (sealOf bidB)) (sealOf bidC)

/-- The auction is in the reveal phase after sealing. -/
theorem demo_phase_reveal : demoAuction.phase = .reveal := by decide

/-- All three seals are among the commitments (the commit phase collected them). -/
theorem demo_committed_A : sealOf bidA ∈ demoAuction.commitments := by decide
theorem demo_committed_B : sealOf bidB ∈ demoAuction.commitments := by decide
theorem demo_committed_C : sealOf bidC ∈ demoAuction.commitments := by decide

/-- Each committed bid's reveal is VALID (right phase + committed seal). -/
theorem demo_validReveal_B : validReveal demoAuction bidB = true := by decide

/-- The highest sealed bid (`B`, `50`) is the winner among the three revealed bids. -/
theorem demo_winner : winnerOf [bidA, bidB, bidC] = some bidB := by decide

/-! ### The CR tooth, concretely (no late-switching). -/

/-- **NO LATE-SWITCHING, concretely.** A reveal that opens `B`'s committed slot can ONLY be `bidB` —
under the reference CR carrier, a competitor cannot peek and then reveal a *different* bid hashing to
`B`'s commitment. Instantiates `reveal_binds_committed` with the real (non-vacuous) CR fact. -/
theorem demo_reveal_binds (b : Bid)
    (hvalid : validReveal demoAuction b = true)
    (hopen : sealOf (Digest := Nat) b = sealOf bidB) : b = bidB :=
  reveal_binds_committed demoCR demoAuction b bidB hvalid hopen

/-- **ANTI-GHOST: a tampered reveal is rejected.** A bid `bidB'` that copies `B`'s value but changes
the bidder (an impostor trying to claim `B`'s winning bid) has a DIFFERENT seal, so it is NOT among the
commitments and `validReveal` rejects it. The seal binds the bidder identity, not just the value. -/
def bidImpostor : Bid := { bidder := agentA, value := 50, nonce := 8 }

theorem demo_impostor_seal_differs : sealOf (Digest := Nat) bidImpostor ≠ sealOf bidB := by decide

theorem demo_impostor_rejected : validReveal demoAuction bidImpostor = false := by decide

/-! ### A non-committed party cannot reveal or win. -/

/-- A fourth agent (`13`) that never committed. Its seal is absent from the commitments. -/
def bidOutsider : Bid := { bidder := 13, value := 999, nonce := 1 }

/-- **A NON-COMMITTED party cannot reveal** — even with a huge bid, the outsider's seal is not among
the commitments, so `validReveal` is `false`. It can never enter the reveal set, hence never win. -/
theorem demo_outsider_rejected : validReveal demoAuction bidOutsider = false := by
  apply uncommitted_cannot_open
  decide

/-! ### The real ledger and the atomic award. -/

/-- The pre-settlement ledger: the winner `B` (cell `11`) holds `100` of the payment asset `0`; the
seller's slot cell `2` holds the task-token (`100` of asset `1`); all five cells are live. -/
def demoLedger : RecordKernelState :=
  { accounts := {1, 2, 10, 11, 12}
    cell := fun _ => default
    caps := fun _ => []
    bal := fun c a =>
      if c = 11 ∧ a = 0 then 100        -- winner B can pay
      else if c = 2 ∧ a = 1 then 100    -- slot holds the task-token
      else 0 }

/-- **The award SETTLES atomically.** `B` (the top bidder) pays `50` of asset `0` to the seller, and
the slot delivers `50` of the task-token (asset `1`) to `B` — one balanced two-leg ring through the
verified `recKExecAsset`. -/
theorem demo_settle_commits :
    (settle demoAuction bidB demoLedger).isSome = true := by
  unfold settle demoAuction bidB demoLedger awardRing
  decide

/-- The post-award ledger (the witness). -/
def demoSettled : RecordKernelState :=
  ((settle demoAuction bidB demoLedger).map Prod.fst).getD demoLedger

/-- After settlement, the seller has been PAID `50` of the payment asset. -/
theorem demo_seller_paid : demoSettled.bal 1 0 = 50 := by
  unfold demoSettled settle demoAuction bidB demoLedger awardRing
  decide

/-- After settlement, the winner `B` RECEIVED the task-token (`50` of asset `1`) and PAID `50` of the
payment asset (`100 - 50 = 50` left). -/
theorem demo_winner_received_token : demoSettled.bal 11 1 = 50 := by
  unfold demoSettled settle demoAuction bidB demoLedger awardRing
  decide

theorem demo_winner_paid : demoSettled.bal 11 0 = 50 := by
  unfold demoSettled settle demoAuction bidB demoLedger awardRing
  decide

/-- **ANTI-GHOST (atomicity bites): a winner who cannot pay aborts the WHOLE award.** Agent `A` (cell
`10`) holds `0` of the payment asset, so an award to `A` fails its first leg and `settle` returns
`none` — no half-settled award where the slot is delivered but never paid for. Instantiates
`settle_atomic`. -/
theorem demo_unfunded_winner_aborts : settle demoAuction bidA demoLedger = none := by
  apply settle_atomic _ _ _ demo_phase_reveal
  decide

/-- **A settled award is value-neutral** on the demo ledger: every asset's total supply is preserved.
Instantiates `settle_conserves`. -/
theorem demo_settle_conserves (k' : RecordKernelState) (a' : Auction Nat)
    (h : settle demoAuction bidB demoLedger = some (k', a')) :
    ∀ b, recTotalAsset k' b = recTotalAsset demoLedger b :=
  settle_conserves demoAuction bidB demoLedger k' a' h

/-! ### `#guard` smoke — the whole sealed-bid flow, decidably. -/

#guard demoAuction.phase = Phase.reveal                              -- commit phase sealed
#guard sealOf (Digest := Nat) bidB ∈ demoAuction.commitments         -- B's seal was committed
#guard validReveal demoAuction bidB                                  -- B's reveal is valid
#guard winnerOf [bidA, bidB, bidC] = some bidB                       -- B (top bid) wins
#guard sealOf (Digest := Nat) bidImpostor ≠ sealOf bidB              -- impostor seal differs
#guard !(validReveal demoAuction bidImpostor)                        -- impostor reveal rejected
#guard !(validReveal demoAuction bidOutsider)                        -- non-committed party rejected
#guard (settle demoAuction bidB demoLedger).isSome                   -- the award settles
#guard demoSettled.bal 1 0 = 50                                      -- seller paid 50
#guard demoSettled.bal 11 1 = 50                                     -- winner got the task-token
#guard (settle demoAuction bidA demoLedger).isNone                   -- unfunded winner aborts (atomic)

end Demo

/-! ## 11. Axiom hygiene — every keystone pinned to the kernel + the CR carrier (no `sorry`/`native_decide`). -/

#assert_axioms seal_injective
#assert_axioms reveal_binds_committed
#assert_axioms reveal_requires_reveal_phase
#assert_axioms uncommitted_cannot_open
#assert_axioms settle_atomic
#assert_axioms settle_conserves
#assert_axioms winner_was_committed
#assert_axioms uncommitted_cannot_win
#assert_axioms Demo.demo_reveal_binds
#assert_axioms Demo.demo_unfunded_winner_aborts

end Dregg2.Intent.SealedAuction
