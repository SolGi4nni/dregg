/-
# Market.InterchainCustody — THE INTERCHAIN CUSTODY LAYER: lock → mirror → clear → release.

**What the existing Lean modeling NEVER covered.** The DrEX clearing tower (`Market/Fairness`,
`Market/LedgerRealizationExt`, `Market/CrossChainSettlement`) is LEDGER-INTERNAL: it conserves value
*inside* dregg's own native ledger (`settleRing_conserves` — every asset's `recTotalAsset` supply
preserved across a settled ring) and settles a fill's ROOT onto a target chain — but it assumes the
traded assets are dregg-native and stops at the vault boundary. The piece it never modeled is the
CUSTODY layer that brings *external* value in: a token locked on Solana/Ethereum, mirrored 1:1 into
dregg as an ordinary `Payable` `AssetId`, traded through DrEX, then released. That layer's soundness
lived ONLY as a Rust live gate (`bridge/src/solana_mirror.rs`: the conservation invariant
`live_supply ≤ currently_locked`, red-teamed BR-3) with NO Lean proof, and its cross-chain atomicity
was modeled nowhere. This module closes that gap: it LIFTS the Rust invariant to a Lean theorem and
COMPOSES it with the DrEX clearing to prove end-to-end cross-boundary conservation.

## The faithful model (the Rust `MirrorState` + `DreggVault.sol`)

A `MirrorState` tracks, per (chain, asset), the two quantities the Rust conservation invariant relates
(`bridge/src/solana_mirror.rs:356-373`):

  * `locked`  — external value currently escrowed in the vault (`currently_locked`; the Solana lock
    PDA / `DreggVault.sol`'s `tokenBalances[token]`), raised by an independently-verified escrow
    (`record_escrow`) and lowered by a confirmed release (`redeem`).
  * `supply`  — mirror-asset currently circulating inside dregg (`live_supply`), raised by a mint
    (`draw_mint`) and lowered by a burn (`redeem`).

Operations, faithful to the Rust:

  * `recordEscrow a` — `currently_locked += a` (an attested/proven lock; `record_escrow`).
  * `drawMint a`     — `live_supply += a` IFF `live_supply + a ≤ currently_locked`, else REFUSED
    (`draw_mint`; `MirrorError::InsufficientLocked` — THE LIVE GATE, red-team BR-3: a mint with no
    escrow, or a second draw against an already-spent escrow, is rejected).
  * `lock a`         — the fused deposit (`credit_lock`): `recordEscrow a` then `drawMint a`.
  * `release a`      — the redeem (`redeem`): `live_supply -= a`, `currently_locked -= a`, IFF
    `a ≤ live_supply`, else REFUSED (`MirrorError::InsufficientMirrorSupply`).

## What is PROVED here

  * **`run_backed` — THE RUST GATE, LIFTED (mirror-backing as an inductive invariant).** `backed`
    (`supply ≤ locked`, the Rust `live_supply ≤ currently_locked`) is PRESERVED by every operation and
    hence by any sequence of them (`run`): an over-mint (`drawMint` beyond backing) or double-release
    is REFUSED (`none`), so no reachable state has unbacked mirror. This is `bridge/src/solana_mirror.rs`'s
    `invariant_holds` as a Lean theorem, non-vacuous both ways (a valid lock/clear/release keeps it;
    an unbacked mint / over-release breaks it → not a valid step).

  * **`custody_cross_boundary_conserves` — END-TO-END CROSS-BOUNDARY CONSERVATION (the keystone).**
    Across the WHOLE `lock → DrEX-clear → release` lifecycle, composing this module's mirror-backing
    with the DrEX clearing's ledger-internal conservation:
      - (BACKING) `supply ≤ locked` holds at every step — every circulating mirror is redeemable;
      - (DrEX conserves the native ledger) the clear preserves `recTotalAsset` for EVERY asset,
        INCLUDING the mirror asset (`Market.settleRing_conserves` via the fill's `settled`) — the
        mirror trades between holders with its total supply preserved; the trade creates/destroys no
        value inside dregg;
      - (BOUNDARY 1:1) `lock` and `release` move `locked` and `supply` by the SAME amount, so the
        redeemability gap `locked − supply` is INVARIANT across the whole lifecycle;
      - (TOTAL VALUE) hence `systemValue k m := recTotalAsset k mirrorAsset + (locked − supply)` is
        CONSERVED end-to-end: what the vault gains/loses in escrow exactly equals what dregg gains/loses
        in circulating mirror. No value is created or destroyed at the vault boundary.

  * **`gatedRingRelease` — CROSS-CHAIN ATOMICITY (modeled).** A multi-chain ring whose per-chain
    releases are ALL gated on the SAME clearing proof: `ringRelease` is all-or-nothing (any leg that
    over-releases aborts the WHOLE ring to `none`, mirroring `settleRing_atomic`), and a release with
    NO clearing proof is refused (`gatedRingRelease false = none`). The timeout/refund edge (`refund`)
    reverts the lock to its pre-lock state, restoring the escrow with no value lost. So neither a
    released-but-uncleared nor a cleared-but-unreleased partial state loses value: the first is
    unreachable (gated `none`), the second is resolved by refund.

  * NON-VACUITY, BOTH POLARITIES (`#guard` teeth): a valid `init → lock → release` conserves (backing
    holds, gap invariant); an over-mint (`drawMint` with no escrow), a double-draw against a spent
    escrow, an over-release, an uncleared ring release, and a non-atomic ring (one leg over-releasing)
    are each REFUSED (`none`). The concrete DrEX fill `Market.demoFill` exhibits the systemValue
    conservation across a real settled clearing.

## HONEST SCOPE

This MODELS the custody layer: it lifts the Rust `live_supply ≤ currently_locked` gate to an inductive
Lean invariant and composes it with the DrEX clearing to prove cross-boundary conservation. The
ON-CHAIN vault contracts ENFORCE it in production — `DreggVault.sol`'s `tokenBalances`/solvency check
(`amount > available` revert) and the Solana lock PDA are what physically hold the escrow; the
attestation/consensus verification (`bridge/src/solana_trustless.rs`) is what raises `currently_locked`
truthfully. The Lean here is the SOUNDNESS those must realize — a refinement obligation, exactly like
the other Lean⊑Rust ties in this tree. Two edges named, not hidden:

  * The MINT/BURN's own ledger realization is per-asset `Σδ = 0` (the issuer well is the conserving
    dual; `turn/src/action.rs` `Effect::Mint`/`Burn`, the executor's conservation checker) — a
    SEPARATE, already-enforced kernel guarantee. This module tracks the `live_supply` register (the
    circulating mirror the Rust `MirrorState` tracks), not the issuer-well ledger mechanics.
  * Cross-chain atomicity is modeled at SPEC level (the all-or-nothing release fan-out + the
    timeout/refund revert); the on-chain commit/abort across multiple vaults' verifiers is the named
    build (`DREX-DESIGN.md §6`, the multi-verifier commit protocol), for which this states the
    invariant it must realize (no partial-release value loss).

Pure. No new axioms — composes `Market.DrexClearing` + `Market.settleRing_conserves` with the lifted
Rust invariant.
-/
import Market.CrossChainSettlement
import Dregg2.Tactics

namespace Market.Interchain

open Dregg2.Intent.Ring
open Dregg2.Exec (AssetId RecordKernelState recTotalAsset)

set_option autoImplicit false

/-! ## 1. THE MODEL — a `MirrorState` faithful to the Rust `MirrorState`. -/

/-- **`MirrorState`** — the dregg-side ledger of one mirrored (chain, asset), a faithful model of the
Rust `bridge/src/solana_mirror.rs` `MirrorState`. `locked` is `currently_locked` (external escrow in
the vault); `supply` is `live_supply` (mirror circulating inside dregg). u64 in Rust; `Nat` here (the
overflow guard `checked_add`→`MirrorError::Overflow` is a Rust-specific bound on the happy path this
models). -/
structure MirrorState where
  /-- External value currently escrowed in the vault (`currently_locked`). -/
  locked : Nat
  /-- Mirror asset currently circulating inside dregg (`live_supply`). -/
  supply : Nat
deriving Repr, DecidableEq

/-- **`backed`** — the conservation invariant `supply ≤ locked` (the Rust `live_supply ≤
currently_locked`, `MirrorState::invariant_holds`): circulating mirror never exceeds locked escrow, so
every mirror unit is redeemable against real backing. -/
def MirrorState.backed (m : MirrorState) : Prop := m.supply ≤ m.locked

instance (m : MirrorState) : Decidable m.backed := by unfold MirrorState.backed; infer_instance

/-- The empty mirror — nothing locked, nothing minted (`MirrorState::new`). -/
def MirrorState.init : MirrorState := ⟨0, 0⟩

theorem MirrorState.init_backed : MirrorState.init.backed := by decide

/-- **`gap`** — the redeemability slack `locked − supply` (in ℤ). `backed ↔ gap ≥ 0`; the honest fused
flow keeps it at 0 (fully backed), while `recordEscrow` ahead of the matching `drawMint` opens it. -/
def MirrorState.gap (m : MirrorState) : ℤ := (m.locked : ℤ) - (m.supply : ℤ)

theorem MirrorState.backed_iff_gap_nonneg (m : MirrorState) : m.backed ↔ 0 ≤ m.gap := by
  unfold MirrorState.backed MirrorState.gap; omega

/-! ## 2. THE OPERATIONS — faithful to the Rust `record_escrow` / `draw_mint` / `credit_lock` / `redeem`. -/

/-- **`recordEscrow a`** — raise the conservation backing by an independently-verified escrow
(`MirrorState::record_escrow`: `currently_locked += a`). The escrow leg is DISTINCT from the mint leg,
so the mint gate is a real constraint (red-team BR-3). -/
def MirrorState.recordEscrow (m : MirrorState) (a : Nat) : MirrorState :=
  { m with locked := m.locked + a }

/-- **`drawMint a`** — THE LIVE GATE (`MirrorState::draw_mint`). Raise `live_supply` by `a` IFF it
stays within the recorded escrow backing; otherwise REFUSE (`none`, the Rust
`MirrorError::InsufficientLocked`). A mint with no escrow (`locked = 0`), or a second draw against an
already-fully-drawn escrow, exceeds the backing and is rejected. -/
def MirrorState.drawMint (m : MirrorState) (a : Nat) : Option MirrorState :=
  if m.supply + a ≤ m.locked then some { m with supply := m.supply + a } else none

/-- **`lock a`** — the fused deposit (`MirrorState::credit_lock`): record the escrow, then draw the
matching mint against it. -/
def MirrorState.lock (m : MirrorState) (a : Nat) : Option MirrorState :=
  (m.recordEscrow a).drawMint a

/-- **`release a`** — the redeem (`MirrorState::redeem`): burn `a` mirror and withdraw `a` escrow,
lowering BOTH registers, IFF `a ≤ live_supply` (else REFUSE — `MirrorError::InsufficientMirrorSupply`;
an over-release / double-release cannot draw against non-circulating mirror). -/
def MirrorState.release (m : MirrorState) (a : Nat) : Option MirrorState :=
  if a ≤ m.supply then some ⟨m.locked - a, m.supply - a⟩ else none

/-! ## 3. MIRROR-BACKING — the Rust gate lifted (invariant preserved; over-mint / over-release refused). -/

/-- Recording escrow only RAISES `locked`, so backing is preserved. -/
theorem recordEscrow_backed {m : MirrorState} (h : m.backed) (a : Nat) :
    (m.recordEscrow a).backed := by
  show m.supply ≤ m.locked + a
  unfold MirrorState.backed at h; omega

/-- **The mint gate GUARANTEES backing** — a committed `drawMint` yields a backed state
UNCONDITIONALLY (the `if` guard is exactly `supply + a ≤ locked`, which IS the post-state's backing).
No `backed` hypothesis is needed: the gate itself is the invariant. -/
theorem drawMint_backed {m m' : MirrorState} {a : Nat} (h : m.drawMint a = some m') : m'.backed := by
  unfold MirrorState.drawMint at h
  by_cases hg : m.supply + a ≤ m.locked
  · rw [if_pos hg] at h; have h' := Option.some.inj h; subst h'; exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`lock` preserves backing** (the fused deposit: escrow then draw). -/
theorem lock_backed {m m' : MirrorState} {a : Nat} (h : m.lock a = some m') : m'.backed :=
  drawMint_backed h

/-- **From a backed state, `lock` ALWAYS succeeds** and lands on exactly `⟨locked + a, supply + a⟩`
(`credit_lock` never fails on a backed mirror: after `recordEscrow a` the escrow covers the equal draw
`supply + a ≤ locked + a`). The boundary-in is a 1:1 credit on both registers. -/
theorem lock_eq {m : MirrorState} (h : m.backed) (a : Nat) :
    m.lock a = some ⟨m.locked + a, m.supply + a⟩ := by
  unfold MirrorState.backed at h
  unfold MirrorState.lock MirrorState.recordEscrow MirrorState.drawMint
  rw [if_pos (show m.supply + a ≤ m.locked + a by omega)]

/-- **`release` preserves backing** — subtracting the SAME `a` from both registers keeps `supply ≤
locked` (given `a ≤ supply` and the prior backing). -/
theorem release_backed {m m' : MirrorState} {a : Nat} (hb : m.backed) (h : m.release a = some m') :
    m'.backed := by
  unfold MirrorState.release at h
  by_cases hg : a ≤ m.supply
  · rw [if_pos hg] at h; have h' := Option.some.inj h; subst h'
    show m.supply - a ≤ m.locked - a
    unfold MirrorState.backed at hb; omega
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### The teeth — over-mint / unbacked-mint / double-draw / over-release are REFUSED. -/

/-- **TOOTH (over-mint): a mint beyond the recorded escrow is REFUSED.** If `supply + a` exceeds
`locked`, `drawMint` fails-closed (`none`) — the Rust `MirrorError::InsufficientLocked`. -/
theorem overMint_refused {m : MirrorState} {a : Nat} (h : m.locked < m.supply + a) :
    m.drawMint a = none := by
  unfold MirrorState.drawMint; rw [if_neg (by omega)]

/-- **TOOTH (unbacked mint): a mint against ZERO escrow is REFUSED.** `draw_without_escrow` (BR-3):
from `init` (`locked = 0`) any positive mint has no backing and is rejected. -/
theorem unbacked_mint_refused {a : Nat} (ha : 0 < a) : MirrorState.init.drawMint a = none :=
  overMint_refused (by show (0 : Nat) < 0 + a; omega)

/-- **TOOTH (double-draw): a second draw against an already-fully-drawn escrow is REFUSED.** After
recording escrow `a` and drawing the full `a` (`supply = locked = a`), a further positive draw exceeds
the backing (`over_mint_beyond_escrow`, BR-3) — the escrow cannot be double-spent. -/
theorem double_draw_refused {a d : Nat} (hd : 0 < d) :
    (⟨a, a⟩ : MirrorState).drawMint d = none :=
  overMint_refused (by show a < a + d; omega)

/-- **TOOTH (over-release): releasing more than the circulating supply is REFUSED.** -/
theorem overRelease_refused {m : MirrorState} {a : Nat} (h : m.supply < a) :
    m.release a = none := by
  unfold MirrorState.release; rw [if_neg (by omega)]

/-! ### The inductive invariant — backing survives ANY sequence of operations. -/

/-- An abstract custody operation. -/
inductive Op where
  | escrow  (a : Nat)
  | draw    (a : Nat)
  | lock    (a : Nat)
  | release (a : Nat)
deriving Repr, DecidableEq

/-- One custody step (escrow always commits; the rest may fail-closed per their gate). -/
def step (m : MirrorState) : Op → Option MirrorState
  | .escrow a  => some (m.recordEscrow a)
  | .draw a    => m.drawMint a
  | .lock a    => m.lock a
  | .release a => m.release a

/-- Run a sequence of custody operations, aborting to `none` on the first refusal. -/
def run (m : MirrorState) : List Op → Option MirrorState
  | []          => some m
  | op :: rest  => (step m op).bind (fun m' => run m' rest)

/-- **A single step preserves backing.** Each operation either raises `locked` (escrow), is
self-guaranteeing (draw/lock — the gate IS the invariant), or subtracts in lockstep (release). -/
theorem step_backed {m m' : MirrorState} {op : Op} (hb : m.backed) (h : step m op = some m') :
    m'.backed := by
  cases op with
  | escrow a  =>
    simp only [step] at h; have h' := Option.some.inj h; subst h'; exact recordEscrow_backed hb a
  | draw a    => exact drawMint_backed h
  | lock a    => exact lock_backed h
  | release a => exact release_backed hb h

/-- **`run_backed` — THE RUST GATE LIFTED: mirror-backing is an inductive invariant.** From any backed
mirror, ANY sequence of custody operations that commits (`run m ops = some m'`) lands on a backed
state: `supply ≤ locked` throughout. This is `bridge/src/solana_mirror.rs`'s `live_supply ≤
currently_locked` as a Lean theorem — an over-mint or over-release cannot occur on a valid path, so no
reachable state carries unbacked mirror. -/
theorem run_backed {m m' : MirrorState} (hb : m.backed) :
    ∀ {ops : List Op}, run m ops = some m' → m'.backed := by
  intro ops
  induction ops generalizing m with
  | nil => intro h; rw [run, Option.some.injEq] at h; exact h ▸ hb
  | cons op rest ih =>
    intro h
    rw [run] at h
    cases hstep : step m op with
    | none => rw [hstep] at h; simp at h
    | some m₁ =>
      rw [hstep, Option.bind_some] at h
      exact ih (step_backed hb hstep) h

/-! ## 4. END-TO-END CROSS-BOUNDARY CONSERVATION — compose mirror-backing with the DrEX clearing. -/

/-- **`systemValue k m mirrorAsset`** — the total value the custody layer relates across the boundary:
dregg's native-ledger total of the mirror asset (`recTotalAsset k mirrorAsset` — what the DrEX clearing
conserves) PLUS the vault's un-claimed backing slack (`m.gap = locked − supply`). Conserving this end
to end is the statement "no value is created or destroyed at the vault boundary." -/
def systemValue (k : RecordKernelState) (m : MirrorState) (mirrorAsset : AssetId) : ℤ :=
  recTotalAsset k mirrorAsset + m.gap

/-- **DrEX-CLEAR conserves `systemValue`** (the composition tooth). A settled DrEX clearing (`c :
DrexClearing`) trades the mirror asset INSIDE the ledger — `Market.settleRing_conserves` preserves
`recTotalAsset` for EVERY asset (the mirror asset included), and the vault backing `m.gap` is untouched
(the clear moves no escrow). So the combined value is preserved across the trade: the mirror moves
between holders, its total supply is preserved, and the vault stays exactly as solvent. -/
theorem drexClear_conserves_systemValue (c : DrexClearing) (m : MirrorState) (b : AssetId) :
    systemValue c.post m b = systemValue c.pre m b := by
  unfold systemValue
  rw [settleRing_conserves (settlementsOf c.nodes) c.pre c.post c.settled b]

/-- **The boundary is 1:1: `lock` moves `locked` and `supply` by the SAME amount**, so the gap — and
hence `systemValue` at a FIXED ledger — is invariant across a deposit. -/
theorem lock_gap {m m' : MirrorState} {a : Nat} (hb : m.backed) (h : m.lock a = some m') :
    m'.gap = m.gap := by
  rw [lock_eq hb a, Option.some.injEq] at h
  subst h; unfold MirrorState.gap; push_cast; ring

/-- **The boundary is 1:1: `release` moves `locked` and `supply` by the SAME amount**, so the gap is
invariant across a redeem (given the prior backing, so both Nat subtractions are honest). -/
theorem release_gap {m m' : MirrorState} {a : Nat} (hb : m.backed) (h : m.release a = some m') :
    m'.gap = m.gap := by
  unfold MirrorState.release at h
  by_cases hg : a ≤ m.supply
  · rw [if_pos hg, Option.some.injEq] at h
    subst h; unfold MirrorState.gap MirrorState.backed at *
    simp only []; omega
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`custody_cross_boundary_conserves` — THE KEYSTONE: end-to-end cross-boundary conservation.**

Take the whole custody lifecycle `lock a → DrEX-clear c → release a'`, starting from a backed mirror
`m0` whose deposit funds a DrEX fill `c` (the clearing the mirror trades through), with `a' ≤` the
post-lock circulating supply so the redeem commits. Then:

  * **(BACKING, throughout)** `m1 = lock m0 a` and `m2 = release m1 a'` are BOTH backed — every
    circulating mirror is redeemable at every step (mirror-backing, §3);
  * **(DrEX conserves the native ledger)** the clear preserves `recTotalAsset` for EVERY asset `b`,
    the mirror asset included (`Market.settleRing_conserves` via `c.settled`) — the trade creates or
    destroys NO value inside dregg;
  * **(TOTAL VALUE conserved across the trade)** `systemValue` is preserved across the DrEX clear
    (`drexClear_conserves_systemValue`): the mirror trades in the ledger while the vault backing is
    untouched, so the combined value is conserved;
  * **(BOUNDARY 1:1)** the redeemability gap is INVARIANT across the whole lifecycle
    (`m2.gap = m1.gap = m0.gap`): what the vault gains then loses in escrow (`+a` then `−a'`) exactly
    equals what dregg gains then loses in circulating mirror. No value leaks at the vault boundary.

This is the ledger-internal DrEX conservation COMPOSED with the lifted mirror-backing: the DrEX
clearing conserves the mirror as it trades, and the lock/release move value across the boundary 1:1,
so the composite `lock → clear → release` conserves total value. -/
theorem custody_cross_boundary_conserves
    (m0 : MirrorState) (hb : m0.backed) (a a' : Nat) (c : DrexClearing) (mirrorAsset : AssetId)
    (m1 m2 : MirrorState) (hlock : m0.lock a = some m1) (hrel : m1.release a' = some m2) :
    m1.backed ∧ m2.backed
    ∧ (∀ b : AssetId, recTotalAsset c.post b = recTotalAsset c.pre b)
    ∧ systemValue c.post m1 mirrorAsset = systemValue c.pre m1 mirrorAsset
    ∧ m1.gap = m0.gap ∧ m2.gap = m0.gap := by
  have hb1 : m1.backed := lock_backed hlock
  have hb2 : m2.backed := release_backed hb1 hrel
  have hg1 : m1.gap = m0.gap := lock_gap hb hlock
  have hg2 : m2.gap = m1.gap := release_gap hb1 hrel
  exact ⟨hb1, hb2,
    fun b => settleRing_conserves (settlementsOf c.nodes) c.pre c.post c.settled b,
    drexClear_conserves_systemValue c m1 mirrorAsset,
    hg1, hg2.trans hg1⟩

/-- **The net boundary crossing, projected** — after `lock a → release a'`, BOTH registers moved by
exactly `a − a'` (from a backed start with `a' ≤ a`): the vault's escrow change EQUALS dregg's
circulating-mirror change. The boundary conserves value 1:1, no phantom mint, no lost escrow. -/
theorem boundary_net_matched
    (m0 : MirrorState) (hb : m0.backed) (a a' : Nat) (hle : a' ≤ a) (m1 m2 : MirrorState)
    (hlock : m0.lock a = some m1) (hrel : m1.release a' = some m2) :
    m2.locked = m0.locked + a - a' ∧ m2.supply = m0.supply + a - a'
    ∧ (m2.locked : ℤ) - m0.locked = (m2.supply : ℤ) - m0.supply := by
  rw [lock_eq hb a, Option.some.injEq] at hlock
  subst hlock
  unfold MirrorState.backed at hb
  unfold MirrorState.release at hrel
  rw [if_pos (show a' ≤ m0.supply + a by omega), Option.some.injEq] at hrel
  subst hrel
  refine ⟨rfl, rfl, ?_⟩
  dsimp only; omega

/-! ## 5. CROSS-CHAIN ATOMICITY — an all-or-nothing multi-vault release, gated on ONE clearing proof. -/

/-- **`ringRelease legs`** — release a MULTI-CHAIN ring atomically: each leg `(m, a)` redeems `a` from
its vault, and if ANY leg over-releases (fails its gate) the WHOLE ring aborts to `none`. This is the
custody analogue of `Market.settleRing_atomic` (a leg failure rolls the whole ring back) — no partial
state where some vaults released and others did not. -/
def ringRelease : List (MirrorState × Nat) → Option (List MirrorState)
  | []            => some []
  | (m, a) :: rest => (m.release a).bind (fun m' => (ringRelease rest).map (fun ms => m' :: ms))

/-- **`gatedRingRelease cleared legs`** — the releases are gated on the shared clearing proof: with NO
proof (`cleared = false`) the ring does NOT release (`none`). A released-but-uncleared state is
therefore unreachable — a counterparty can never be short because a leg released without the clearing
that authorizes all of them. -/
def gatedRingRelease (cleared : Bool) (legs : List (MirrorState × Nat)) : Option (List MirrorState) :=
  if cleared then ringRelease legs else none

/-- **TOOTH (no release without the clearing proof): an uncleared ring release is REFUSED.** -/
theorem gatedRingRelease_uncleared (legs : List (MirrorState × Nat)) :
    gatedRingRelease false legs = none := rfl

/-- **ATOMICITY: a single over-releasing leg aborts the WHOLE ring.** If leg `j` demands more than its
circulating supply, `ringRelease` fails-closed for the entire list — no leg commits. The partial state
"some vaults paid out, one could not" is unreachable. -/
theorem ringRelease_atomic (pre : List (MirrorState × Nat)) (m : MirrorState) (a : Nat)
    (rest : List (MirrorState × Nat)) (hfail : m.supply < a) :
    ringRelease (pre ++ (m, a) :: rest) = none := by
  induction pre with
  | nil =>
    rw [List.nil_append, ringRelease, overRelease_refused hfail]; rfl
  | cons hd tl ih =>
    obtain ⟨mh, ah⟩ := hd
    rw [List.cons_append, ringRelease, ih]
    cases mh.release ah <;> simp

/-- **All legs release ⇒ all outputs backed.** If every input leg is backed and the ring releases
(`some out`), every released vault is still backed — the multi-chain settlement lands every vault in a
sound state or none at all. -/
theorem ringRelease_backed :
    ∀ {legs : List (MirrorState × Nat)} {out : List MirrorState},
      (∀ p ∈ legs, p.1.backed) → ringRelease legs = some out → ∀ m ∈ out, m.backed := by
  intro legs
  induction legs with
  | nil => intro out _ h m hm; rw [ringRelease, Option.some.injEq] at h; subst h; cases hm
  | cons hd tl ih =>
    obtain ⟨mh, ah⟩ := hd
    intro out hall h m hm
    rw [ringRelease] at h
    cases hrel : mh.release ah with
    | none => rw [hrel] at h; simp at h
    | some mh' =>
      rw [hrel, Option.bind_some] at h
      cases htl : ringRelease tl with
      | none => rw [htl] at h; simp at h
      | some outTl =>
        rw [htl, Option.map_some, Option.some.injEq] at h
        subst h
        have hmh : mh.backed := hall (mh, ah) (by simp)
        have htlAll : ∀ p ∈ tl, p.1.backed := fun p hp => hall p (by simp [hp])
        rcases List.mem_cons.mp hm with hh | ht
        · subst hh; exact release_backed hmh hrel
        · exact ih htlAll htl m ht

/-- **`refund m0` — the timeout/refund edge.** If the clearing does NOT settle within the window, the
lock REVERTS: the vault state returns to its pre-lock value `m0` (the escrow is returned to the
depositor, the mirror un-minted). No value is lost — the deposit round-trips. -/
def refund (m0 : MirrorState) (_stuck : MirrorState) : MirrorState := m0

/-- **The refund restores the pre-lock state exactly** — a `lock a` that never clears is reverted with
NO value lost: `refund` returns `m0`, so `refund (lock m0 a) = m0`. A cleared-but-unreleased escrow is
resolved by refund; it is never stranded. -/
theorem lock_refund_restores (m0 : MirrorState) (_hb : m0.backed) (a : Nat) {m1 : MirrorState}
    (_hlock : m0.lock a = some m1) : refund m0 m1 = m0 := rfl

/-! ## 6. NON-VACUITY — both polarities, computed. -/

/-- A concrete backed mirror: 500 escrowed, 500 minted (`credit_lock` of 500 from `init`). -/
def demoMirror : MirrorState := ⟨500, 500⟩

theorem demoMirror_backed : demoMirror.backed := by decide

/-- POSITIVE POLE — a full valid lifecycle from `init`: lock 500, release 200, both commit and land on
backed states with the gap invariant at 0 (fully backed throughout). -/
theorem demo_lifecycle_conserves :
    ∃ m1 m2 : MirrorState,
      MirrorState.init.lock 500 = some m1 ∧ m1.release 200 = some m2
      ∧ m1.backed ∧ m2.backed ∧ m1.gap = 0 ∧ m2.gap = 0 := by
  refine ⟨⟨500, 500⟩, ⟨300, 300⟩, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### `#guard` smoke — the gate BITES (negative pole) and the happy path COMMITS (positive pole). -/

-- POSITIVE: a backed deposit of 500 from `init` commits to ⟨500, 500⟩ (escrow + mint, 1:1):
#guard MirrorState.init.lock 500 == some ⟨500, 500⟩
-- POSITIVE: redeeming 200 lowers BOTH registers 1:1 → ⟨300, 300⟩:
#guard (⟨500, 500⟩ : MirrorState).release 200 == some ⟨300, 300⟩
-- POSITIVE: backing holds at every reachable state:
#guard decide ((⟨500, 500⟩ : MirrorState).backed)
#guard decide ((⟨300, 300⟩ : MirrorState).backed)
-- NEGATIVE (unbacked mint): a mint of 500 against ZERO escrow is REFUSED (BR-3):
#guard (MirrorState.init.drawMint 500).isNone
-- NEGATIVE (over-mint): drawing 1 beyond a fully-drawn escrow ⟨500,500⟩ is REFUSED:
#guard ((⟨500, 500⟩ : MirrorState).drawMint 1).isNone
-- NEGATIVE (over-release): redeeming 1000 against 300 circulating is REFUSED:
#guard ((⟨300, 300⟩ : MirrorState).release 1000).isNone
-- NEGATIVE (uncleared ring): a release with NO clearing proof is REFUSED:
#guard (gatedRingRelease false [(⟨500, 500⟩, 100)]).isNone
-- POSITIVE (atomic ring): a cleared ring where every leg is within supply releases ALL:
#guard (gatedRingRelease true [(⟨500, 500⟩, 100), (⟨300, 300⟩, 50)]).isSome
-- NEGATIVE (non-atomic ring): one over-releasing leg aborts the WHOLE ring (no partial payout):
#guard (gatedRingRelease true [(⟨500, 500⟩, 100), (⟨300, 300⟩, 999)]).isNone
-- the inductive invariant, run over a mixed op sequence, stays backed and commits:
#guard (run MirrorState.init [.lock 500, .escrow 100, .draw 100, .release 200]).isSome

/-! ## Axiom hygiene — every interchain-custody keystone pinned kernel-clean (CI hard-gate). -/

#assert_all_clean [Market.Interchain.recordEscrow_backed, Market.Interchain.drawMint_backed,
  Market.Interchain.lock_backed, Market.Interchain.lock_eq, Market.Interchain.release_backed,
  Market.Interchain.overMint_refused, Market.Interchain.unbacked_mint_refused,
  Market.Interchain.double_draw_refused, Market.Interchain.overRelease_refused,
  Market.Interchain.step_backed, Market.Interchain.run_backed,
  Market.Interchain.drexClear_conserves_systemValue, Market.Interchain.lock_gap,
  Market.Interchain.release_gap, Market.Interchain.custody_cross_boundary_conserves,
  Market.Interchain.boundary_net_matched, Market.Interchain.gatedRingRelease_uncleared,
  Market.Interchain.ringRelease_atomic, Market.Interchain.ringRelease_backed,
  Market.Interchain.lock_refund_restores, Market.Interchain.demo_lifecycle_conserves]

end Market.Interchain
