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

  * **`custody_cross_boundary_conserves` — END-TO-END CROSS-BOUNDARY CONSERVATION (the keystone), a
    genuine CROSS-PREDICATE.** Over a `CustodyWorld` (the vault registers PLUS the dregg-ledger
    circulating total of the mirror asset), across the WHOLE `wlock → wclear → wrelease` lifecycle, the
    invariant `Solvent` — `ledgerMirror = supply ∧ supply ≤ locked`, hence `ledgerMirror ≤ locked` — is
    PRESERVED:
      - (TIE, ACROSS THE BOUNDARY) the dregg-ledger mirror total EQUALS the vault register and is backed
        by external escrow — a real relation between the two sides, FALSIFIABLE FOUR WAYS
        (`phantomMint_not_solvent`: a register out-running the ledger is not solvent;
        `forged_clear_breaks_solvency` / `demo_forged_clear_refused`: a clear that MOVES the tracked
        total with no clearing behind it is refused, mutation asserted present first;
        `mistied_clear_not_solvent`: the `htie` hypothesis is LOAD-BEARING — clearing against the wrong
        pool de-synchronizes the tie; `nonconserving_clear_unpackageable`: a minting `pre → post` admits
        NO `DrexClearing` at all, the refusal sits in the kernel executor);
      - (THE CLEARING GENUINELY PARTICIPATES) `wclear` UPDATES `ledgerMirror` to the clearing's post-state
        total of the mirror asset, and it stays invariant ONLY because the REAL `settleRing_conserves`
        preserves that asset (`wclear_ledgerMirror`); the clearing `c` is tied to the boundary by the
        hypothesis that the world's ledger mirror IS `c`'s pre-total of `mirrorAsset` — not a free
        variable added to both sides of an already-proven equation;
      - (SURVIVES END TO END) after the full round trip the tie still holds, so no dregg-ledger mirror is
        left unbacked and no escrow is lost at the vault boundary.

  * **`gatedRingRelease` — CROSS-CHAIN ATOMICITY, gated on an ACCEPTED clearing proof (not a flag).**
    The gate takes the ACTUAL proof object — an `Option DrexClearing`, where a `DrexClearing` is
    proof-CARRYING (its `settled` field IS the kernel-real `settleRing` commitment; a non-conserving
    "clearing" is unrepresentable, `nonconserving_clear_unpackageable`) — and releases ONLY if the
    settlement verifier `settleDrex` (the on-chain `DreggSettlement.settle` twin) ACCEPTS it against
    the target chain's current proven root. Three refusals are forced, each a theorem: no proof at all
    (`gatedRingRelease_no_proof`); a REAL proof replayed onto a foreign anchor
    (`gatedRingRelease_unanchored` — the `ContinuityBroken` gate lifts through the release); and, even
    with an accepted proof, any single over-releasing leg aborts the WHOLE ring
    (`gatedRingRelease_atomic`, mirroring `settleRing_atomic`). The timeout/refund edge (`refund a`)
    REDEEMS the stuck deposit — an actual `release` that recomputes both registers, proven to round-trip
    a never-cleared lock back to its pre-lock state (`lock_refund_restores`), no value lost. So neither a
    released-but-uncleared nor a cleared-but-unreleased partial state loses value: the first is
    unreachable (refused), the second is resolved by refund. Named residuals, still OPEN: the per-leg
    release AMOUNTS are not yet derived from the clearing's per-leg deliveries, and ONE shared
    `settleDrex` accept stands in for each chain's own verifier register — the invariant the
    multi-verifier commit protocol (`DREX-DESIGN.md §6`) must realize.

  * NON-VACUITY, BOTH POLARITIES (named theorems + `#guard` smoke): a valid `init → lock → release`
    conserves (backing holds, gap invariant); an over-mint (`drawMint` with no escrow), a double-draw
    against a spent escrow, an over-release, a proof-less or mis-anchored ring release, and a
    non-atomic ring (one leg over-releasing) are each REFUSED (`none`). The concrete kernel-settled
    DrEX fill `Market.demoFill` drives BOTH poles for real: the keystone fires on it end-to-end
    (`demo_custody_lifecycle_conserves`, discharging `htie` by computation) and the release gate opens
    on it exactly when its anchor matches (`demo_gated_ring_releases` vs
    `demo_gated_ring_refused_wrong_root`).

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
  * Cross-chain atomicity is modeled at SPEC level, but the gate is BOUND: the release fan-out is
    conditioned on the settlement verifier `settleDrex` ACCEPTING an actual `DrexClearing` against the
    chain's proven root (not on a flag). Two residuals remain OPEN by name: the per-leg release
    amounts are not derived from the clearing's per-leg deliveries, and one shared verifier accept
    stands in for the per-chain registers — the on-chain commit/abort across multiple vaults'
    verifiers is the named build (`DREX-DESIGN.md §6`, the multi-verifier commit protocol), for which
    this states the invariant it must realize (no partial-release value loss).

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

/-! ## 4. END-TO-END CROSS-BOUNDARY CONSERVATION — compose mirror-backing with the DrEX clearing.

The keystone below is a GENUINE cross-boundary conservation, not a disjoint conjunction. The tie it
maintains — the dregg-ledger's circulating total of the mirror asset EQUALS the vault's mirror register
(`recTotalAsset _ mirrorAsset = supply`), and that register is backed by external escrow
(`supply ≤ locked`) — is a real CROSS-PREDICATE between the two sides of the boundary, forced through
the whole `lock → clear → release` lifecycle. The clearing genuinely participates: the clear step
UPDATES the tracked ledger-mirror total to the clearing's post-state total, and it stays invariant ONLY
because the REAL `settleRing_conserves` preserves the mirror asset (`wclear_ledgerMirror`) — the
clearing `c` is tied to the boundary by the hypothesis that the world's ledger mirror IS `c`'s
mirror-asset total. -/

/-- **`CustodyWorld`** — the combined cross-boundary state: the vault registers (`vault`, the Rust
`MirrorState`) PLUS the dregg native-ledger circulating total of the mirror asset (`ledgerMirror`,
i.e. `recTotalAsset _ mirrorAsset`). Bundling them is what lets a lifecycle op move BOTH sides and lets
the invariant TIE them — the previous `systemValue` kept them disjoint, so its "conservation" was the
mirror asset's ledger total plus a backing slack added to BOTH sides of an already-proven equation, with
nothing forcing the clearing to trade the mirror. -/
structure CustodyWorld where
  /-- vault side: external escrow + mirror register (the Rust `MirrorState`). -/
  vault : MirrorState
  /-- dregg side: the native-ledger circulating total of the mirror asset (`recTotalAsset _ mirrorAsset`). -/
  ledgerMirror : ℤ
deriving Repr, DecidableEq

/-- **`Solvent w`** — the CROSS-BOUNDARY invariant: the dregg-ledger mirror total EQUALS the vault's
circulating register (`ledgerMirror = supply`), and that register is backed by external escrow
(`supply ≤ locked`). Chaining the two gives `ledgerMirror ≤ locked`: every mirror unit inside dregg's
ledger is backed by real escrow held in the external vault. This is a genuine relation ACROSS the
boundary — a disjoint conjunction could never express "the dregg ledger is backed by the foreign chain." -/
def CustodyWorld.Solvent (w : CustodyWorld) : Prop :=
  w.ledgerMirror = (w.vault.supply : ℤ) ∧ w.vault.supply ≤ w.vault.locked

/-- **`wlock a`** — deposit: escrow `a` in the vault AND mint `a` mirror into the dregg ledger. Raises
`locked`, `supply`, AND `ledgerMirror` by `a` (the mint puts `a` into the ledger). -/
def CustodyWorld.wlock (w : CustodyWorld) (a : Nat) : Option CustodyWorld :=
  (w.vault.lock a).map (fun v => { vault := v, ledgerMirror := w.ledgerMirror + (a : ℤ) })

/-- **`wrelease a`** — redeem: burn `a` mirror from the dregg ledger AND withdraw `a` escrow. Lowers
`locked`, `supply`, AND `ledgerMirror` by `a`. -/
def CustodyWorld.wrelease (w : CustodyWorld) (a : Nat) : Option CustodyWorld :=
  (w.vault.release a).map (fun v => { vault := v, ledgerMirror := w.ledgerMirror - (a : ℤ) })

/-- **`wclear c b`** — a DrEX clearing `c` trades the mirror asset `b` INSIDE the dregg ledger: the
world's tracked `ledgerMirror` is UPDATED to the clearing's post-state total of the mirror asset; the
vault is untouched (the clear moves no escrow). -/
def CustodyWorld.wclear (w : CustodyWorld) (c : DrexClearing) (b : AssetId) : CustodyWorld :=
  { w with ledgerMirror := recTotalAsset c.post b }

/-- **The clear preserves the ledger-mirror total — the REAL clearing tie.** The post-state total of
the mirror asset EQUALS its pre-state total (`Market.settleRing_conserves` via `c.settled`), so the clear
lands `ledgerMirror` on the clearing's PRE-total. This is where `c` genuinely participates: the clearing
conserves the mirror asset it trades. -/
theorem wclear_ledgerMirror (w : CustodyWorld) (c : DrexClearing) (b : AssetId) :
    (w.wclear c b).ledgerMirror = recTotalAsset c.pre b :=
  settleRing_conserves (settlementsOf c.nodes) c.pre c.post c.settled b

/-- **`wlock` preserves solvency** — raising `locked`, `supply`, `ledgerMirror` all by `a` keeps
`ledgerMirror = supply` and `supply ≤ locked`. -/
theorem wlock_solvent {w w' : CustodyWorld} {a : Nat} (hs : w.Solvent) (h : w.wlock a = some w') :
    w'.Solvent := by
  obtain ⟨he, hbk⟩ := hs
  have hb : w.vault.backed := hbk
  simp only [CustodyWorld.wlock] at h
  rw [lock_eq hb a, Option.map_some, Option.some.injEq] at h
  subst h
  refine ⟨?_, ?_⟩
  · show w.ledgerMirror + (a : ℤ) = ((w.vault.supply + a : Nat) : ℤ)
    rw [he]; push_cast; ring
  · show w.vault.supply + a ≤ w.vault.locked + a
    omega

/-- **`wrelease` preserves solvency** — lowering `locked`, `supply`, `ledgerMirror` all by `a` keeps the
tie (given the redeem commits, so `a ≤ supply`). -/
theorem wrelease_solvent {w w' : CustodyWorld} {a : Nat} (hs : w.Solvent) (h : w.wrelease a = some w') :
    w'.Solvent := by
  obtain ⟨he, hbk⟩ := hs
  simp only [CustodyWorld.wrelease, MirrorState.release] at h
  by_cases hg : a ≤ w.vault.supply
  · rw [if_pos hg, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_⟩
    · show w.ledgerMirror - (a : ℤ) = ((w.vault.supply - a : Nat) : ℤ)
      rw [he]; omega
    · show w.vault.supply - a ≤ w.vault.locked - a
      omega
  · rw [if_neg hg] at h; simp at h

/-- **`wclear` preserves solvency (the composition tooth) — given the clearing trades THE mirror asset.**
If the world's tracked ledger-mirror total IS the clearing's pre-state total (`htie` — the clearing `c`
operates on the mirror asset), the clear preserves both `ledgerMirror` and solvency: the real
`settleRing_conserves` keeps the mirror asset's total, and the vault is untouched. -/
theorem wclear_solvent {w : CustodyWorld} (c : DrexClearing) (b : AssetId)
    (hs : w.Solvent) (htie : w.ledgerMirror = recTotalAsset c.pre b) :
    (w.wclear c b).Solvent ∧ (w.wclear c b).ledgerMirror = w.ledgerMirror := by
  obtain ⟨he, hbk⟩ := hs
  have hpres : (w.wclear c b).ledgerMirror = w.ledgerMirror := by
    rw [wclear_ledgerMirror]; exact htie.symm
  refine ⟨⟨?_, hbk⟩, hpres⟩
  rw [hpres]; exact he

/-- **The boundary is 1:1: `lock` moves `locked` and `supply` by the SAME amount**, so the
redeemability slack `gap` is invariant across a deposit. -/
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

/-- **`custody_cross_boundary_conserves` — THE KEYSTONE: end-to-end cross-boundary conservation, a REAL
cross-predicate.**

Take the whole custody lifecycle `wlock a → wclear c → wrelease a'` over a `CustodyWorld`, starting
`Solvent`, where the clearing `c` genuinely trades the mirror asset: the world's ledger-mirror total
after the deposit IS `c`'s pre-state total of `mirrorAsset` (`htie`). Then:

  * **(SOLVENT throughout)** `w1`, `w1.wclear c mirrorAsset`, and `w3` are ALL `Solvent` — at every step
    the dregg-ledger mirror total EQUALS the vault register and that register is backed by escrow;
  * **(THE CLEARING CONSERVES THE TRACKED MIRROR)** the clear leaves `ledgerMirror` invariant
    (`(w1.wclear c mirrorAsset).ledgerMirror = w1.ledgerMirror`) — and this holds ONLY because the REAL
    `settleRing_conserves` preserves the mirror asset `c` trades (`wclear_ledgerMirror` + `htie`); `c` is
    genuinely tied to the boundary, not a free variable added to both sides of an equation;
  * **(THE TIE SURVIVES END TO END)** `w3.ledgerMirror = w3.vault.supply` and
    `w3.ledgerMirror ≤ w3.vault.locked`: after the full round trip the dregg-ledger mirror total still
    equals the vault register and is still fully backed by external escrow. No value leaks at the vault
    boundary, and no dregg-ledger mirror is left unbacked.

Unlike the previous `systemValue` version, the conserved quantity here is a genuine relation ACROSS the
boundary (dregg-ledger total ↔ vault escrow), the clearing genuinely participates (via `htie` +
`settleRing_conserves`), and the invariant is FALSIFIABLE (see `phantomMint_not_solvent`). -/
theorem custody_cross_boundary_conserves
    (w0 : CustodyWorld) (hs0 : w0.Solvent) (a a' : Nat)
    (c : DrexClearing) (mirrorAsset : AssetId)
    (w1 w3 : CustodyWorld)
    (hlock : w0.wlock a = some w1)
    (htie : w1.ledgerMirror = recTotalAsset c.pre mirrorAsset)
    (hrel : (w1.wclear c mirrorAsset).wrelease a' = some w3) :
    w1.Solvent
    ∧ (w1.wclear c mirrorAsset).Solvent
    ∧ w3.Solvent
    ∧ (w1.wclear c mirrorAsset).ledgerMirror = w1.ledgerMirror
    ∧ w3.ledgerMirror = (w3.vault.supply : ℤ)
    ∧ w3.ledgerMirror ≤ (w3.vault.locked : ℤ) := by
  have hs1 : w1.Solvent := wlock_solvent hs0 hlock
  obtain ⟨hs2, hpres⟩ := wclear_solvent c mirrorAsset hs1 htie
  have hs3 : w3.Solvent := wrelease_solvent hs2 hrel
  refine ⟨hs1, hs2, hs3, hpres, hs3.1, ?_⟩
  rw [hs3.1]; exact_mod_cast hs3.2

/-- **A concrete solvent world** — 500 escrowed, 500 mirror both in the vault register and the dregg
ledger (a fully-backed, fully-drawn deposit). -/
def demoWorld : CustodyWorld := ⟨⟨500, 500⟩, 500⟩

/-- POSITIVE POLE — the tie holds for a genuine matched deposit. -/
theorem demoWorld_solvent : demoWorld.Solvent := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **TOOTH — the tie is a REAL CROSS-PREDICATE that BITES.** A phantom-mint world (the vault register
claims 50 mirror circulating, but the dregg ledger holds only 40) is NOT `Solvent`, even though the vault
backing `50 ≤ 100` holds. A DISJOINT conjunction of "backing" and "ledger conservation" could never catch
this — only a predicate that TIES the dregg ledger to the vault register does. -/
theorem phantomMint_not_solvent : ¬ (CustodyWorld.mk ⟨100, 50⟩ 40).Solvent := by
  rintro ⟨he, _⟩
  exact absurd he (by decide)

/-- **`wclearForged t`** — the SHAPE of a non-conserving clear: land the tracked ledger-mirror total
on an arbitrary `t`, answering to no clearing. This is the mutation the keystone must refuse — a
"clear" that mints (or burns) mirror inside the dregg ledger with no settled clearing behind it. -/
def CustodyWorld.wclearForged (w : CustodyWorld) (t : ℤ) : CustodyWorld :=
  { w with ledgerMirror := t }

/-- **TOOTH (the forged clear BREAKS solvency).** From any solvent world, a forged clear that MOVES
the tracked total (`hmut` — the mutation asserted PRESENT, not a no-op twin of the honest clear)
lands on a NON-solvent world: the dregg ledger no longer matches the vault register. The honest
`wclear` keeps solvency (`wclear_solvent`) precisely because `settleRing_conserves` pins its landing
total; the forged one has no such pin and the cross-predicate catches it. -/
theorem forged_clear_breaks_solvency {w : CustodyWorld} (hs : w.Solvent) {t : ℤ}
    (hmut : t ≠ w.ledgerMirror) : ¬ (w.wclearForged t).Solvent := by
  rintro ⟨he, _⟩
  exact hmut (he.trans hs.1.symm)

/-- The concrete refusal, MUTATION FIRST: minting one phantom mirror unit into `demoWorld`'s ledger
via a forged clear. Clause 1 asserts the mutation is PRESENT (the tracked total genuinely moved,
`501 ≠ 500` — the hostile input is not the honest one); clause 2 is the verdict (REFUSED). -/
theorem demo_forged_clear_refused :
    (demoWorld.wclearForged 501).ledgerMirror ≠ demoWorld.ledgerMirror
    ∧ ¬ (demoWorld.wclearForged 501).Solvent :=
  ⟨by decide, forged_clear_breaks_solvency demoWorld_solvent (by decide)⟩

/-- **TOOTH (`htie` is LOAD-BEARING, not decoration).** Clearing against a pool whose pre-state
mirror total DIFFERS from the world's tracked total breaks solvency: `settleRing_conserves` lands the
clear on the POOL's total, so a clearing tied to the wrong pool de-synchronizes the dregg ledger from
the vault register. The keystone's `htie` hypothesis is exactly the obligation a caller must
discharge — and `demo_custody_lifecycle_conserves` discharges it by computation on the real fill. -/
theorem mistied_clear_not_solvent {w : CustodyWorld} (hs : w.Solvent) (c : DrexClearing)
    (b : AssetId) (hoff : recTotalAsset c.pre b ≠ w.ledgerMirror) :
    ¬ (w.wclear c b).Solvent := by
  rintro ⟨he, _⟩
  exact hoff (((wclear_ledgerMirror w c b).symm.trans he).trans hs.1.symm)

/-- **TOOTH (a non-conserving clearing is REFUSED AT FORMATION).** A `pre → post` transition that
changes ANY asset's total admits NO `DrexClearing` packaging at all: its `settled` field would need
`settleRing pre … = some post`, which `Market.minting_post_unsettleable` refuses. So the forged clear
above can never arrive through the honest `wclear` — there is no proof-carrying clearing whose
settlement mints; the refusal sits in the verified kernel executor, upstream of this module. -/
theorem nonconserving_clear_unpackageable (k k'' : RecordKernelState) (b : AssetId)
    (hmint : recTotalAsset k'' b ≠ recTotalAsset k b) :
    ¬ ∃ c : DrexClearing, c.pre = k ∧ c.post = k'' := by
  rintro ⟨c, rfl, rfl⟩
  exact minting_post_unsettleable c.pre c.post c.nodes b hmint c.settled

/-- **POSITIVE POLE — the keystone FIRES on the REAL clearing.** The full lifecycle, concrete: from
an empty world, deposit 7 (escrow + mint), clear through the kernel-settled `Market.demoFill` — which
GENUINELY trades the mirror asset (asset 10: cell 1's 7 units move to cell 2; its pre-state total IS
the world's tracked 7, discharging `htie` by computation) — then redeem 7. Every hypothesis of
`custody_cross_boundary_conserves` is discharged on the real fill; solvency holds at every step and
the round trip lands back on the empty world. SATISFIABLE here, REFUTABLE next door
(`demo_forged_clear_refused`, `mistied_clear_not_solvent`) — a floor, not a tautology. -/
theorem demo_custody_lifecycle_conserves :
    ∃ w1 w3 : CustodyWorld,
      (⟨⟨0, 0⟩, 0⟩ : CustodyWorld).wlock 7 = some w1
      ∧ w1.ledgerMirror = recTotalAsset demoFill.pre 10
      ∧ (w1.wclear demoFill 10).wrelease 7 = some w3
      ∧ w1.Solvent ∧ (w1.wclear demoFill 10).Solvent ∧ w3.Solvent
      ∧ w3 = ⟨⟨0, 0⟩, 0⟩ := by
  have hs0 : (⟨⟨0, 0⟩, 0⟩ : CustodyWorld).Solvent := ⟨by decide, by decide⟩
  have hlock : (⟨⟨0, 0⟩, 0⟩ : CustodyWorld).wlock 7 = some ⟨⟨7, 7⟩, 7⟩ := by decide
  have htie : (⟨⟨7, 7⟩, 7⟩ : CustodyWorld).ledgerMirror = recTotalAsset demoFill.pre 10 := by
    decide
  have hrel : ((⟨⟨7, 7⟩, 7⟩ : CustodyWorld).wclear demoFill 10).wrelease 7
      = some ⟨⟨0, 0⟩, 0⟩ := by decide
  obtain ⟨h1, h2, h3, -, -, -⟩ :=
    custody_cross_boundary_conserves ⟨⟨0, 0⟩, 0⟩ hs0 7 7 demoFill 10
      ⟨⟨7, 7⟩, 7⟩ ⟨⟨0, 0⟩, 0⟩ hlock htie hrel
  exact ⟨⟨⟨7, 7⟩, 7⟩, ⟨⟨0, 0⟩, 0⟩, hlock, htie, hrel, h1, h2, h3, rfl⟩

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

/-! ## 5. CROSS-CHAIN ATOMICITY — an all-or-nothing multi-vault release, gated on ONE ACCEPTED
clearing proof.

The gate is NOT a flag. `gatedRingRelease` takes the actual proof object — an `Option DrexClearing`,
proof-CARRYING by construction (`settled` is the kernel-real `settleRing` commitment; a
non-conserving "clearing" cannot even be built, `nonconserving_clear_unpackageable`) — and releases
ONLY if the settlement verifier `settleDrex` (the on-chain `DreggSettlement.settle` twin) ACCEPTS it
against the target chain's current proven root. Named residuals, OPEN: per-leg release amounts are
not yet derived from the clearing's per-leg deliveries; one shared verifier accept stands in for the
per-chain registers (`DREX-DESIGN.md §6`, the multi-verifier commit protocol). -/

/-- **`ringRelease legs`** — release a MULTI-CHAIN ring atomically: each leg `(m, a)` redeems `a` from
its vault, and if ANY leg over-releases (fails its gate) the WHOLE ring aborts to `none`. This is the
custody analogue of `Market.settleRing_atomic` (a leg failure rolls the whole ring back) — no partial
state where some vaults released and others did not. -/
def ringRelease : List (MirrorState × Nat) → Option (List MirrorState)
  | []            => some []
  | (m, a) :: rest => (m.release a).bind (fun m' => (ringRelease rest).map (fun ms => m' :: ms))

/-- **`gatedRingRelease rootOf S proof legs`** — the multi-vault ring release, gated on ONE ACCEPTED
clearing proof. `proof` is the actual proof object (`Option DrexClearing` — proof-carrying: its
`settled` field is the kernel-real `settleRing` commitment), and the gate is the settlement verifier
itself: `settleDrex rootOf S c` must ACCEPT `c` against the chain's current proven root (else
fail-closed — `ContinuityBroken`). Only then does the ring release, still all-or-nothing per
`ringRelease`. A released-but-uncleared state is therefore unreachable: no proof, a mis-anchored
proof, or any over-releasing leg each refuse the WHOLE ring. -/
def gatedRingRelease {Root : Type} [DecidableEq Root] (rootOf : RecordKernelState → Root)
    (S : ProvenState Root) (proof : Option DrexClearing) (legs : List (MirrorState × Nat)) :
    Option (List MirrorState) :=
  proof.bind fun c => (settleDrex rootOf S c).bind fun _ => ringRelease legs

/-- **TOOTH (no release without a clearing proof): a proof-less ring release is REFUSED.** With no
`DrexClearing` there is nothing to verify and the ring does not release. Unlike the retired
`cleared : Bool` gate, `true` cannot be conjured here: opening the gate requires an actual settled
clearing AND the verifier's accept. -/
theorem gatedRingRelease_no_proof {Root : Type} [DecidableEq Root]
    (rootOf : RecordKernelState → Root) (S : ProvenState Root) (legs : List (MirrorState × Nat)) :
    gatedRingRelease rootOf S none legs = none := rfl

/-- **TOOTH (a mis-anchored proof does not release): a REAL clearing proof replayed onto a foreign
proven root is REFUSED.** The verifier's `ContinuityBroken` gate (`settleDrex_continuity_broken`)
lifts through the release: possessing a genuine settled clearing is NOT enough — it must chain from
the exact state the target chain has already proven. -/
theorem gatedRingRelease_unanchored {Root : Type} [DecidableEq Root]
    (rootOf : RecordKernelState → Root) (S : ProvenState Root) (c : DrexClearing)
    (hbreak : rootOf c.pre ≠ S.provenRoot) (legs : List (MirrorState × Nat)) :
    gatedRingRelease rootOf S (some c) legs = none := by
  show ((settleDrex rootOf S c).bind fun _ => ringRelease legs) = none
  rw [settleDrex_continuity_broken rootOf S c hbreak]
  rfl

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

/-- **ATOMICITY SURVIVES THE GATE: even an ACCEPTED proof releases all-or-nothing.** With a genuine
clearing proof in hand, a single over-releasing leg still aborts the WHOLE ring — the gate authorizes
the release; it never weakens the per-leg refusals. -/
theorem gatedRingRelease_atomic {Root : Type} [DecidableEq Root]
    (rootOf : RecordKernelState → Root) (S : ProvenState Root) (c : DrexClearing)
    (pre : List (MirrorState × Nat)) (m : MirrorState) (a : Nat)
    (rest : List (MirrorState × Nat)) (hfail : m.supply < a) :
    gatedRingRelease rootOf S (some c) (pre ++ (m, a) :: rest) = none := by
  show ((settleDrex rootOf S c).bind fun _ => ringRelease (pre ++ (m, a) :: rest)) = none
  cases settleDrex rootOf S c with
  | none => rfl
  | some S' =>
    show ringRelease (pre ++ (m, a) :: rest) = none
    exact ringRelease_atomic pre m a rest hfail

/-- **POSITIVE POLE — the gate OPENS on the real accepted proof and the ring releases atomically.**
`Market.demoFill` (the concrete kernel-settled bilateral swap) verified against the anchor matching
its pre-state (`Market.demoProven`) releases BOTH legs, each vault's registers lowered 1:1. -/
theorem demo_gated_ring_releases :
    gatedRingRelease demoRoot demoProven (some demoFill)
      [(⟨500, 500⟩, 100), (⟨300, 300⟩, 50)] = some [⟨400, 400⟩, ⟨250, 250⟩] := by decide

/-- **NEGATIVE POLE — the SAME real proof against a FOREIGN anchor releases NOTHING.** The clearing
is genuine; the anchor (`Market.demoProvenBad`) is wrong; the whole ring refuses. With the positive
pole this is the discriminator: the gate is not a `True`-carrier. -/
theorem demo_gated_ring_refused_wrong_root :
    gatedRingRelease demoRoot demoProvenBad (some demoFill)
      [(⟨500, 500⟩, 100), (⟨300, 300⟩, 50)] = none := by decide

/-- **NEGATIVE POLE (atomicity) — an accepted proof plus ONE over-releasing leg = NO leg releases.** -/
theorem demo_gated_ring_aborts_on_one_bad_leg :
    gatedRingRelease demoRoot demoProven (some demoFill)
      [(⟨500, 500⟩, 100), (⟨300, 300⟩, 999)] = none := by decide

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

/-- **`refund a m` — the timeout/refund edge** (`redeem` on a stuck lock). If the clearing does NOT
settle within the window, the deposit is reverted by REDEEMING it: withdraw the `a` escrow and un-mint
the `a` mirror (`locked -= a`, `supply -= a`), IFF the lock is still fully in place (`a ≤ supply`), else
refused. This ACTUALLY COMPUTES the reverted state (it is a genuine `release` of the stuck deposit back
to the depositor) — not a constant returning its input. -/
def refund (a : Nat) (m : MirrorState) : Option MirrorState := m.release a

/-- **The refund RESTORES the pre-lock state exactly — a genuine round trip, not `rfl` over a constant.**
A `lock a` that never clears is reverted by refunding `a`: the refund recomputes both registers
(`locked + a - a`, `supply + a - a`) and the arithmetic collapses back to `m0`, so `refund a (lock m0 a)
= some m0`. No value is lost — a cleared-but-unreleased escrow is resolved by refund, never stranded. -/
theorem lock_refund_restores (m0 : MirrorState) (hb : m0.backed) (a : Nat) {m1 : MirrorState}
    (hlock : m0.lock a = some m1) : refund a m1 = some m0 := by
  rw [lock_eq hb a, Option.some.injEq] at hlock
  subst hlock
  unfold refund MirrorState.release
  rw [if_pos (Nat.le_add_left a m0.supply)]
  simp only [Nat.add_sub_cancel]

/-- **TOOTH (over-refund refused)** — refunding more than is circulating fails-closed (an already-cleared
or partially-released lock cannot be double-refunded). -/
theorem overRefund_refused {m : MirrorState} {a : Nat} (h : m.supply < a) : refund a m = none :=
  overRelease_refused h

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
-- (the ring-release gate's poles are NAMED kernel theorems, not guards: `gatedRingRelease_no_proof`,
--  `demo_gated_ring_releases`, `demo_gated_ring_refused_wrong_root`,
--  `demo_gated_ring_aborts_on_one_bad_leg` — each over the REAL `demoFill` proof object.)
-- the inductive invariant, run over a mixed op sequence, stays backed and commits:
#guard (run MirrorState.init [.lock 500, .escrow 100, .draw 100, .release 200]).isSome

/-! ## Axiom hygiene — every interchain-custody keystone pinned kernel-clean (CI hard-gate). -/

#assert_all_clean [Market.Interchain.recordEscrow_backed, Market.Interchain.drawMint_backed,
  Market.Interchain.lock_backed, Market.Interchain.lock_eq, Market.Interchain.release_backed,
  Market.Interchain.overMint_refused, Market.Interchain.unbacked_mint_refused,
  Market.Interchain.double_draw_refused, Market.Interchain.overRelease_refused,
  Market.Interchain.step_backed, Market.Interchain.run_backed,
  Market.Interchain.wclear_ledgerMirror, Market.Interchain.wlock_solvent,
  Market.Interchain.wrelease_solvent, Market.Interchain.wclear_solvent,
  Market.Interchain.lock_gap, Market.Interchain.release_gap,
  Market.Interchain.custody_cross_boundary_conserves, Market.Interchain.demoWorld_solvent,
  Market.Interchain.phantomMint_not_solvent, Market.Interchain.forged_clear_breaks_solvency,
  Market.Interchain.demo_forged_clear_refused, Market.Interchain.mistied_clear_not_solvent,
  Market.Interchain.nonconserving_clear_unpackageable,
  Market.Interchain.demo_custody_lifecycle_conserves,
  Market.Interchain.boundary_net_matched, Market.Interchain.gatedRingRelease_no_proof,
  Market.Interchain.gatedRingRelease_unanchored, Market.Interchain.gatedRingRelease_atomic,
  Market.Interchain.demo_gated_ring_releases, Market.Interchain.demo_gated_ring_refused_wrong_root,
  Market.Interchain.demo_gated_ring_aborts_on_one_bad_leg,
  Market.Interchain.ringRelease_atomic, Market.Interchain.ringRelease_backed,
  Market.Interchain.lock_refund_restores, Market.Interchain.overRefund_refused,
  Market.Interchain.demo_lifecycle_conserves]

end Market.Interchain
