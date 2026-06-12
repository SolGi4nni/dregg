/-
# Dregg2.Apps.Trustline — the bilateral line of credit (mutual credit) as a verified cell-program.

**The organ this births** (docs/ORGANS.md §1): trustlines are "built but stillborn at one uncalled
init" — the Stingray bounded-counter machinery exists end to end (`coord/src/shared_budget.rs`,
`coord/src/budget.rs`, the executor `BudgetGate` in `turn/src/budget_gate.rs`, the per-turn seeding
at `node/src/blocklace_sync.rs:2081`), but `node/src/state.rs:1129 init_budget_coordinator` has ZERO
callers, so the gate is always `None` (and the settlement edges `collect_spending_certificates` /
`rebalance_budgets` dangle uncalled too). This module models the thing the init edge births: the
DIRECTIONAL bilateral line of credit, and proves its keystones. The companion design doc
(`docs/TRUSTLINES.md`) names the init/settle weld.

**The model.** "Issuer A extends holder B a line of N" is an ATTENUATED CAPABILITY whose exercise
debits a shared counter:

  * the LINE is a Stingray `Slice` (`Proof/Stingray.Slice` = `BudgetSlice { ceiling, spent }`):
    `ceiling = N` (the attenuation bound, immutable), `spent = drawn` (the exercised amount) —
    `draw_slice_tracks_tryDebit` proves the draw gate IS `Slice.tryDebit`, literally the counter the
    payment-channel demo (`demo-agent/examples/payment_channel_burst.rs`) and the executor's
    `BudgetGate.try_debit` (`turn/src/budget_gate.rs:70`) run;
  * the line is DIRECTIONAL (A→B is not B→A): B draws against A's credit; the drawn amount is a move
    against A's SIGNED WELL in the issuer-asset model (`Substrate/IssuerLedger`, `AssetId := issuer
    CellId`): the holder's credit register carries `+drawn`, the issuer's well `−drawn`, and the
    bilateral sum is EXACTLY ZERO at every reachable state (`trustline_conserved_forever`);
  * draws are digest-identified (`BudgetSlice::debits`, `turn/src/budget_gate.rs:29`): a digest
    commits at most once, ever (`draw_replay_refused`, `no_double_draw_forever`);
  * SETTLEMENT: repayment is monotone-down on `drawn` and restores the line exactly
    (`draw_repay_roundtrip`); closing the line settles the residual against a hard-asset ledger pair
    conservatively (`settlePay_conserves_hard`, `settleAll_clears`) — the `rebalance_budgets`
    `(agent, total_spent)` settlement list (`node/src/state.rs:1213`) applied as a move.

## Keystones PROVED

  1. **BOUNDED BY THE LINE** (`draw_within_line`, `trustline_within_line_forever`): drawing never
     exceeds the extended line, along EVERY adversarial schedule of draws/repays — the
     `StorageGatewayMandate.sgm_volume_legal_forever` pattern on the credit counter.
  2. **BILATERAL CONSERVATION** (`bilateral_conserved`, `trustline_conserved_forever`): holder
     credit + issuer well = 0 forever — the draw is a MOVE against A's well, never a mint; the
     issuer-move model's exact law on the bilateral pair.
  3. **NO DOUBLE DRAW** (`draw_replay_refused`, `draw_records`, `no_double_draw_forever`): a debit
     digest commits at most once; the digest registry is duplicate-free at every reachable state.
  4. **SETTLEMENT RESTORES THE LINE** (`repay_monotone_down`, `draw_repay_roundtrip`,
     `settleAll_clears`, `settlePay_conserves_hard`): repay is monotone-down then the available line
     is back up — draw `a` then repay `a` restores `drawn`/credit/well exactly (the spent digest
     stays burned: one-shot forever); full settlement zeroes the line and moves exactly the drawn
     amount across the hard-asset pair, conserving it.
  5. **THE ATTENUATION PUN** (`holder_credit_le_line_forever`, `ceiling_immutable_forever`): the
     holder's exercised credit never exceeds the attenuation bound, and the bound itself is an
     immutable register — a line of credit IS an attenuated capability with a balance bound
     (`Exec/AuthTurn.recKDelegateAtten`'s granted ⊆ held, with the `⊆` made quantitative).
  6. **MONOTONE REDEMPTION — the deployed settle** (§9: `settle_monotone`,
     `settled_monotone_forever`, `settle_le_drawn_forever`, `repay_below_settled_refused`): the
     node (`node/src/trustline_service.rs`, `TL_SETTLED_SLOT`) settles by marching the `settled`
     register UP, never zeroing `drawn`; repay is floored at the settled amount — settled credit
     is hard money already paid out and cannot be repaid back.
  7. **SOLVENCY** (§10/§12: `solvency`, `solvency_forever`, `escrow_solvent_forever`): the
     program-constraint chain `settled ≤ drawn ≤ ceiling` IS solvency — cumulative payouts never
     exceed the escrowed line, and the fullReserve escrow column never goes negative, along every
     adversarial schedule of draws/repays/settles.
  8. **THE COLLATERAL AXIS REIFIED** (§12: `Collateral`, `settleC_conserves_hard` parametric over
     BOTH points; `settleReserve_conserves_hard`/`settleReserve_conserves_pair` = the deployed
     fullReserve point; `settleC_pureCredit_agrees_settlePay` recovers §5b exactly): the Rust
     escrow→holder settle is a theorem INSTANCE of one conservation law, not a divergence.
  9. **DERIVED REGISTERS + THE EPOCH WELD** (§11/§10b: `derived_view_faithful`,
     `view_determines_line`; `epochSlice_remaining`, `drawS_fires_iff_epoch_tryDebit`,
     `draw_replay_refused_across_epochs`): the deployment's drawn-derived credit view loses
     nothing; the `ensure_coordinator` rebuild rule is faithful (the two draw gates agree at
     every reachable state); a committed digest is refused at EVERY later epoch — the node
     `TrustlineRegistry` forever-carrier law.

Non-vacuity both polarities (§7/§13 `#guard`s): a within-line draw ADMITS (and the boundary draw is
tight); an over-line draw, a replayed digest, and an over-repay are each REFUSED. No
`sorry`/`:= True`/`native_decide`; `#assert_axioms`-clean (⊆ {propext, Classical.choice,
Quot.sound}). No executor import — the cell shape (which registers, which slot caveats) is the
design doc's §3; the SGM/CWM mandate modules are the executor-welding precedent.
-/
import Dregg2.Proof.Stingray
import Dregg2.Tactics

namespace Dregg2.Apps.Trustline

open Dregg2.Proof.Stingray (Slice)

/-! ## §1 — The trustline state (the bilateral cell's registers).

The trustline IS a cell; A (issuer) and B (holder) are the parties; these are its registers. The
`ceiling` is the extended line N (immutable for the line's life — re-extension is a new birth or a
governed amendment); `drawn` is the shared counter; `draws` is the debit-digest registry
(`BudgetSlice::debits`); `holderAcct`/`issuerWell` are the bilateral signed-well pair in the
issuer's asset (`AssetId := issuer`, the issuer carries the negative well). -/

/-- The bilateral trustline: issuer A extends holder B a line of `ceiling`. Directional — this
record IS the A→B line; a B→A line is a separate trustline with the roles swapped. -/
structure Line where
  /-- The extended line N — the attenuation bound (`Slice.ceiling`). Immutable register. -/
  ceiling : Nat
  /-- Outstanding drawn amount — the shared counter (`Slice.spent`). -/
  drawn : Nat
  /-- Committed draw digests (`BudgetSlice::debits`, `turn/src/budget_gate.rs:29`) — the
  no-double-draw registry. A digest is one-shot FOREVER (repayment does not resurrect it). -/
  draws : List Nat
  /-- The holder's credit balance in the issuer-asset: `+drawn`. -/
  holderAcct : Int
  /-- The issuer's signed well in its own asset: `−drawn` (the issuer-move model — the draw is
  PRODUCTION at the issuer's negative-capable well, never an out-of-thin-air mint). -/
  issuerWell : Int
  deriving Repr, DecidableEq

/-- The trustline's `Slice` face: the line IS the Stingray bounded counter
(`coord/src/budget.rs::BudgetSlice`), `ceiling = N`, `spent = drawn`. -/
def Line.slice (t : Line) : Slice := ⟨t.ceiling, t.drawn⟩

/-- Remaining undrawn line (`BudgetSlice::remaining`, truncated subtraction = saturating). -/
def Line.remaining (t : Line) : Nat := t.ceiling - t.drawn

/-- The remaining line agrees with the slice face's remaining. -/
theorem Line.remaining_eq_slice (t : Line) : t.remaining = t.slice.remaining := rfl

/-- **Well-formedness — the reachable-state invariant.** Drawn within the line; the bilateral pair
carries exactly `±drawn`; the digest registry is duplicate-free. -/
def Line.WF (t : Line) : Prop :=
  t.drawn ≤ t.ceiling
    ∧ t.holderAcct = (t.drawn : Int)
    ∧ t.issuerWell = -(t.drawn : Int)
    ∧ t.draws.Nodup

instance (t : Line) : Decidable t.WF := by
  unfold Line.WF; infer_instance

/-! ## §2 — Birth, draw, repay (the ops). -/

/-- **`init` — the BIRTH of the line** (the missing `init_budget_coordinator` edge,
`node/src/state.rs:1129`): issuer extends a fresh line of `n`. Nothing drawn, no digests, both
wells level. The REAL birth must be funded by a ledger debit at the issuer (design doc §2); this
is the post-birth cell state it installs. -/
def Line.init (n : Nat) : Line :=
  { ceiling := n, drawn := 0, draws := [], holderAcct := 0, issuerWell := 0 }

/-- **`draw` — the holder exercises the line** (`BudgetSlice::try_debit` + digest registration).
Fail-closed twice over: a replayed digest is refused (no-double-draw); an amount beyond the
remaining line is refused (the attenuation bound). On commit: counter up, digest burned, holder
credit up, issuer well down — a MOVE against the issuer's well. -/
def draw (t : Line) (digest amt : Nat) : Option Line :=
  if digest ∈ t.draws then none
  else if amt ≤ t.ceiling - t.drawn then
    some { t with drawn := t.drawn + amt
                , draws := digest :: t.draws
                , holderAcct := t.holderAcct + (amt : Int)
                , issuerWell := t.issuerWell - (amt : Int) }
  else none

/-- **`repay` — the holder restores the line.** Fail-closed: repaying more than is drawn is
refused (over-repayment would MINT credit at the issuer's well). On commit: counter down, holder
credit down, issuer well up — the inverse move. The digest registry is untouched: spent digests
stay burned. -/
def repay (t : Line) (amt : Nat) : Option Line :=
  if amt ≤ t.drawn then
    some { t with drawn := t.drawn - amt
                , holderAcct := t.holderAcct - (amt : Int)
                , issuerWell := t.issuerWell + (amt : Int) }
  else none

/-- **`draw_spec` — the commit-shape lemma.** A committed draw means: the digest was fresh, the
amount fit the remaining line, and the post-state is exactly the four-register move. -/
theorem draw_spec {t t' : Line} {d amt : Nat} (h : draw t d amt = some t') :
    d ∉ t.draws ∧ amt ≤ t.ceiling - t.drawn
      ∧ t' = { t with drawn := t.drawn + amt
                    , draws := d :: t.draws
                    , holderAcct := t.holderAcct + (amt : Int)
                    , issuerWell := t.issuerWell - (amt : Int) } := by
  unfold draw at h
  by_cases hd : d ∈ t.draws
  · rw [if_pos hd] at h; exact absurd h (by simp)
  · rw [if_neg hd] at h
    by_cases hb : amt ≤ t.ceiling - t.drawn
    · rw [if_pos hb] at h
      simp only [Option.some.injEq] at h
      exact ⟨hd, hb, h.symm⟩
    · rw [if_neg hb] at h; exact absurd h (by simp)

/-- **`repay_spec` — the settle-shape lemma.** A committed repay means: the amount was within the
outstanding draw, and the post-state is exactly the inverse three-register move. -/
theorem repay_spec {t t' : Line} {amt : Nat} (h : repay t amt = some t') :
    amt ≤ t.drawn
      ∧ t' = { t with drawn := t.drawn - amt
                    , holderAcct := t.holderAcct - (amt : Int)
                    , issuerWell := t.issuerWell + (amt : Int) } := by
  unfold repay at h
  by_cases hb : amt ≤ t.drawn
  · rw [if_pos hb] at h
    simp only [Option.some.injEq] at h
    exact ⟨hb, h.symm⟩
  · rw [if_neg hb] at h; exact absurd h (by simp)

/-- Birth is well-formed. -/
theorem init_WF (n : Nat) : (Line.init n).WF := by
  simp [Line.WF, Line.init]

/-- Birth opens the whole line: remaining = n. -/
theorem init_remaining (n : Nat) : (Line.init n).remaining = n := by
  simp [Line.remaining, Line.init]

/-! ## §3 — Keystone 1: BOUNDED BY THE LINE (per-step). -/

/-- **`draw_within_line`** — a committed draw stays within the line (the `boundedBy` ceiling,
the SGM volume-budget shape). -/
theorem draw_within_line {t t' : Line} {d amt : Nat} (hwf : t.WF)
    (h : draw t d amt = some t') : t'.drawn ≤ t'.ceiling := by
  obtain ⟨hle, -, -, -⟩ := hwf
  obtain ⟨-, hb, rfl⟩ := draw_spec h
  show t.drawn + amt ≤ t.ceiling
  omega

/-- **`over_line_draw_refused` — the REFUSAL tooth.** An over-line draw is fail-closed `none`,
at every state, unconditionally. -/
theorem over_line_draw_refused {t : Line} {d amt : Nat}
    (h : ¬ amt ≤ t.ceiling - t.drawn) : draw t d amt = none := by
  unfold draw
  by_cases hd : d ∈ t.draws
  · rw [if_pos hd]
  · rw [if_neg hd, if_neg h]

/-- A committed draw advances the counter by exactly `amt`, leaves the line fixed, and burns
the digest. -/
theorem draw_records {t t' : Line} {d amt : Nat} (h : draw t d amt = some t') :
    t'.drawn = t.drawn + amt ∧ t'.ceiling = t.ceiling ∧ d ∈ t'.draws := by
  obtain ⟨-, -, rfl⟩ := draw_spec h
  exact ⟨rfl, rfl, List.mem_cons_self ..⟩

/-! ## §4 — Keystone 3: NO DOUBLE DRAW (per-step). -/

/-- **`draw_replay_refused`** — a digest already in the registry can never debit again, no matter
the amount. The anti-replay the `BudgetSlice::debits` list carries in Rust, here a theorem. -/
theorem draw_replay_refused {t : Line} {d amt : Nat} (h : d ∈ t.draws) :
    draw t d amt = none :=
  if_pos h

/-- A committed draw's digest was FRESH — `draw` commits a given digest at most once, ever. -/
theorem draw_digest_was_fresh {t t' : Line} {d amt : Nat} (h : draw t d amt = some t') :
    d ∉ t.draws :=
  (draw_spec h).1

/-- Repay leaves the digest registry untouched: repayment never resurrects a spent digest. -/
theorem repay_draws_fixed {t t' : Line} {amt : Nat} (h : repay t amt = some t') :
    t'.draws = t.draws := by
  obtain ⟨-, rfl⟩ := repay_spec h
  rfl

/-! ## §5 — Keystones 2 & 4: CONSERVATION and SETTLEMENT (per-step). -/

/-- **`bilateral_conserved`** — at every well-formed state, holder credit + issuer well = 0.
The draw is a move against A's well: value is never created across the pair. -/
theorem bilateral_conserved {t : Line} (hwf : t.WF) :
    t.holderAcct + t.issuerWell = 0 := by
  obtain ⟨-, hh, hw, -⟩ := hwf
  rw [hh, hw]
  omega

/-- **`repay_monotone_down`** — a committed repay debits the counter by exactly `amt`
(and leaves the line fixed): settlement is monotone-down on `drawn`. -/
theorem repay_monotone_down {t t' : Line} {amt : Nat} (h : repay t amt = some t') :
    t'.drawn = t.drawn - amt ∧ t'.ceiling = t.ceiling := by
  obtain ⟨-, rfl⟩ := repay_spec h
  exact ⟨rfl, rfl⟩

/-- **`over_repay_refused` — the over-repayment tooth.** Repaying more than is drawn is
fail-closed `none` (it would mint credit at the issuer's well). -/
theorem over_repay_refused {t : Line} {amt : Nat} (h : ¬ amt ≤ t.drawn) :
    repay t amt = none :=
  if_neg h

/-- **`draw_repay_roundtrip` — SETTLEMENT RESTORES THE LINE.** Draw `a`, repay `a`: the counter,
the holder credit, the issuer well, and the remaining line are all back exactly where they started
— monotone-down-then-up, value-neutral. (Only the spent digest stays burned: anti-replay survives
settlement.) -/
theorem draw_repay_roundtrip {t t₁ t₂ : Line} {d a : Nat}
    (h₁ : draw t d a = some t₁) (h₂ : repay t₁ a = some t₂) :
    t₂.drawn = t.drawn ∧ t₂.holderAcct = t.holderAcct ∧ t₂.issuerWell = t.issuerWell
      ∧ t₂.remaining = t.remaining := by
  obtain ⟨-, hb, rfl⟩ := draw_spec h₁
  obtain ⟨-, rfl⟩ := repay_spec h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t.drawn + a - a = t.drawn
    omega
  · show t.holderAcct + (a : Int) - (a : Int) = t.holderAcct
    omega
  · show t.issuerWell - (a : Int) + (a : Int) = t.issuerWell
    omega
  · show t.ceiling - (t.drawn + a - a) = t.ceiling - t.drawn
    omega

/-! ### §5b — Settlement against the hard-asset ledger.

Closing the line returns to the ledger: the residual `drawn` is paid in a HARD asset (an ordinary
move, holder→issuer) while the credit legs unwind. This is `rebalance_budgets`'s
`(agent, total_spent)` settlement list (`node/src/state.rs:1213-1216`) applied as a move — the
design doc's §4 weld. We model the hard-asset pair explicitly and prove the settle conserves it. -/

/-- A trustline together with the parties' hard-asset balances (the settlement target ledger). -/
structure Channel where
  tl : Line
  /-- Issuer's hard-asset balance (e.g. the devnet payment asset). -/
  issuerHard : Int
  /-- Holder's hard-asset balance. -/
  holderHard : Int
  deriving Repr, DecidableEq

/-- **`settlePay`** — settle `amt` of the outstanding draw: the holder pays `amt` hard asset to
the issuer AND the credit legs unwind by `amt` (a `repay`). Fail-closed via `repay`'s gate. -/
def settlePay (c : Channel) (amt : Nat) : Option Channel :=
  (repay c.tl amt).map fun tl' =>
    { tl := tl', issuerHard := c.issuerHard + (amt : Int), holderHard := c.holderHard - (amt : Int) }

/-- **`settlePay_conserves_hard`** — settlement is a MOVE on the hard-asset pair: the combined
hard balance is exactly conserved (the `rebalance_conserves` shape, on the bilateral ledger). -/
theorem settlePay_conserves_hard {c c' : Channel} {amt : Nat} (h : settlePay c amt = some c') :
    c'.issuerHard + c'.holderHard = c.issuerHard + c.holderHard := by
  unfold settlePay at h
  cases hr : repay c.tl amt with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some tl' =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      show c.issuerHard + (amt : Int) + (c.holderHard - (amt : Int)) = c.issuerHard + c.holderHard
      omega

/-- **`settleAll`** — close the line: settle the whole outstanding draw. Total — the full repay
always fires (`drawn ≤ drawn`). -/
def settleAll (c : Channel) : Channel := (settlePay c c.tl.drawn).getD c

/-- **`settleAll_clears`** — closing the line zeroes the counter and levels BOTH credit wells:
the trustline returns to its just-born shape (full line available), and the hard-asset move paid
exactly the drawn amount. -/
theorem settleAll_clears (c : Channel) (hwf : c.tl.WF) :
    (settleAll c).tl.drawn = 0
      ∧ (settleAll c).tl.holderAcct = 0
      ∧ (settleAll c).tl.issuerWell = 0
      ∧ (settleAll c).issuerHard = c.issuerHard + (c.tl.drawn : Int) := by
  obtain ⟨-, hh, hw, -⟩ := hwf
  unfold settleAll settlePay repay
  rw [if_pos (Nat.le_refl c.tl.drawn)]
  simp only [Option.map_some, Option.getD_some]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show c.tl.drawn - c.tl.drawn = 0
    omega
  · show c.tl.holderAcct - (c.tl.drawn : Int) = 0
    rw [hh]; omega
  · show c.tl.issuerWell + (c.tl.drawn : Int) = 0
    rw [hw]; omega
  · trivial

/-! ## §6 — The FOREVER crowns: every keystone along every adversarial schedule.

The `sgm_volume_legal_forever` pattern: an adversary picks any infinite schedule of draws and
repays (any digests, any amounts); refused ops are no-ops; the invariant rides the trajectory. -/

/-- One adversarial op against the line. -/
inductive TLOp where
  | draw (digest amt : Nat)
  | repay (amt : Nat)
  deriving Repr, DecidableEq

/-- An adversarial schedule. -/
def TLSched : Type := Nat → TLOp

/-- One step: apply the op; a refused op leaves the state fixed (fail-closed no-op). -/
def step (t : Line) : TLOp → Line
  | .draw d a => (draw t d a).getD t
  | .repay a  => (repay t a).getD t

/-- The trajectory under a schedule. -/
def traj (t₀ : Line) (sched : TLSched) : Nat → Line
  | 0     => t₀
  | n + 1 => step (traj t₀ sched n) (sched n)

/-- A committed draw preserves well-formedness. -/
theorem draw_preserves_WF {t t' : Line} {d amt : Nat} (hwf : t.WF)
    (h : draw t d amt = some t') : t'.WF := by
  obtain ⟨hle, hh, hw, hnd⟩ := hwf
  obtain ⟨hd, hb, rfl⟩ := draw_spec h
  unfold Line.WF
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t.drawn + amt ≤ t.ceiling
    omega
  · show t.holderAcct + (amt : Int) = ((t.drawn + amt : Nat) : Int)
    omega
  · show t.issuerWell - (amt : Int) = -((t.drawn + amt : Nat) : Int)
    omega
  · show (d :: t.draws).Nodup
    exact List.nodup_cons.mpr ⟨hd, hnd⟩

/-- A committed repay preserves well-formedness. -/
theorem repay_preserves_WF {t t' : Line} {amt : Nat} (hwf : t.WF)
    (h : repay t amt = some t') : t'.WF := by
  obtain ⟨hle, hh, hw, hnd⟩ := hwf
  obtain ⟨hb, rfl⟩ := repay_spec h
  unfold Line.WF
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t.drawn - amt ≤ t.ceiling
    omega
  · show t.holderAcct - (amt : Int) = ((t.drawn - amt : Nat) : Int)
    omega
  · show t.issuerWell + (amt : Int) = -((t.drawn - amt : Nat) : Int)
    omega
  · show t.draws.Nodup
    exact hnd

/-- One adversarial step preserves well-formedness (refused ops are identity). -/
theorem step_preserves_WF (t : Line) (op : TLOp) (hwf : t.WF) : (step t op).WF := by
  cases op with
  | draw d a =>
      show ((draw t d a).getD t).WF
      cases h : draw t d a with
      | some t' => simp only [Option.getD_some]; exact draw_preserves_WF hwf h
      | none    => simp only [Option.getD_none]; exact hwf
  | repay a =>
      show ((repay t a).getD t).WF
      cases h : repay t a with
      | some t' => simp only [Option.getD_some]; exact repay_preserves_WF hwf h
      | none    => simp only [Option.getD_none]; exact hwf

/-- **`trustline_WF_forever`** — well-formedness rides every adversarial trajectory. -/
theorem trustline_WF_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).WF := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih => exact step_preserves_WF (traj t₀ sched k) (sched k) ih

/-- **KEYSTONE 1 forever: `trustline_within_line_forever`** — drawing never exceeds the line,
along every adversarial schedule. -/
theorem trustline_within_line_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).drawn ≤ (traj t₀ sched n).ceiling :=
  fun n => (trustline_WF_forever t₀ hinit sched n).1

/-- **KEYSTONE 2 forever: `trustline_conserved_forever`** — the bilateral pair sums to zero at
every reachable state: no schedule of draws/repays creates or destroys value across the line. -/
theorem trustline_conserved_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).holderAcct + (traj t₀ sched n).issuerWell = 0 :=
  fun n => bilateral_conserved (trustline_WF_forever t₀ hinit sched n)

/-- **KEYSTONE 3 forever: `no_double_draw_forever`** — the digest registry is duplicate-free at
every reachable state: no digest ever debits twice. -/
theorem no_double_draw_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).draws.Nodup :=
  fun n => (trustline_WF_forever t₀ hinit sched n).2.2.2

/-- **THE PUN forever: `holder_credit_le_line_forever`** — the holder's exercised credit never
exceeds the attenuation bound: granted ⊆ held, quantitatively, at every reachable state. -/
theorem holder_credit_le_line_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).holderAcct ≤ ((traj t₀ sched n).ceiling : Int) := by
  intro n
  obtain ⟨hle, hh, -, -⟩ := trustline_WF_forever t₀ hinit sched n
  rw [hh]
  omega

/-- The line itself is an immutable register: no op ever moves the ceiling. -/
theorem step_ceiling_fixed (t : Line) (op : TLOp) : (step t op).ceiling = t.ceiling := by
  cases op with
  | draw d a =>
      show ((draw t d a).getD t).ceiling = t.ceiling
      cases h : draw t d a with
      | some t' => simp only [Option.getD_some]; exact (draw_records h).2.1
      | none    => rfl
  | repay a =>
      show ((repay t a).getD t).ceiling = t.ceiling
      cases h : repay t a with
      | some t' => simp only [Option.getD_some]; exact (repay_monotone_down h).2
      | none    => rfl

/-- **`ceiling_immutable_forever`** — the extended line is the same N at every reachable state
(the `.immutable` slot-caveat shape, design doc §3). -/
theorem ceiling_immutable_forever (t₀ : Line) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).ceiling = t₀.ceiling := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [show traj t₀ sched (k+1) = step (traj t₀ sched k) (sched k) from rfl,
          step_ceiling_fixed, ih]

/-! ## §6b — The Stingray bridge: the draw gate IS `Slice.tryDebit`.

The trustline's counter is LITERALLY the bounded counter the executor's `BudgetGate` runs
(`turn/src/budget_gate.rs:70 try_debit`) and the payment-channel demo bursts against — lines of
credit and payment channels are one primitive at two settings (docs/ORGANS.md §1). -/

/-- **`draw_slice_tracks_tryDebit`** — a committed draw's counter move IS `Slice.tryDebit` on the
line's slice face: same gate, same arithmetic, same post-state. -/
theorem draw_slice_tracks_tryDebit {t t' : Line} {d amt : Nat}
    (h : draw t d amt = some t') : t.slice.tryDebit amt = some t'.slice := by
  obtain ⟨-, hb, rfl⟩ := draw_spec h
  unfold Slice.tryDebit
  rw [if_pos (show amt ≤ t.slice.remaining from hb)]
  rfl

/-- **`draw_fires_iff_tryDebit`** — for a fresh digest, the draw fires IFF the Stingray counter's
`tryDebit` fires: the trustline gate adds exactly the anti-replay leg, nothing else. -/
theorem draw_fires_iff_tryDebit (t : Line) (d amt : Nat) (hfresh : d ∉ t.draws) :
    (draw t d amt).isSome = (t.slice.tryDebit amt).isSome := by
  unfold draw Slice.tryDebit
  rw [if_neg hfresh]
  by_cases hb : amt ≤ t.ceiling - t.drawn
  · rw [if_pos hb, if_pos (show amt ≤ t.slice.remaining from hb)]
    rfl
  · rw [if_neg hb, if_neg (show ¬ amt ≤ t.slice.remaining from hb)]
    rfl

/-! ## §7 — It RUNS: non-vacuity, both polarities. -/

/-- Demo: issuer extends holder a line of 100. -/
def demo₀ : Line := Line.init 100

#guard decide demo₀.WF
#guard demo₀.remaining == 100

-- POSITIVE polarity: a within-line draw ADMITS (digest 7, amount 30).
#guard (draw demo₀ 7 30).isSome

/-- After the first draw: 30 drawn, 70 remaining. -/
def demo₁ : Line := (draw demo₀ 7 30).getD demo₀

#guard demo₁.drawn == 30
#guard demo₁.remaining == 70
#guard demo₁.holderAcct == 30
#guard demo₁.issuerWell == -30
-- CONSERVATION: the bilateral pair sums to zero.
#guard demo₁.holderAcct + demo₁.issuerWell == 0
#guard decide demo₁.WF

-- NEGATIVE polarity 1: replaying digest 7 is REFUSED (any amount).
#guard (draw demo₁ 7 1).isNone
-- NEGATIVE polarity 2: an over-line draw is REFUSED (80 > 70 remaining).
#guard (draw demo₁ 8 80).isNone
-- ...but the boundary draw (exactly the remaining 70) ADMITS — the bound is tight.
#guard (draw demo₁ 8 70).isSome
-- NEGATIVE polarity 3: over-repay is REFUSED (31 > 30 drawn).
#guard (repay demo₁ 31).isNone

/-- Settlement: repay the full 30 — the line is restored. -/
def demo₂ : Line := (repay demo₁ 30).getD demo₁

#guard demo₂.drawn == 0
#guard demo₂.remaining == 100
#guard demo₂.holderAcct == 0
#guard demo₂.issuerWell == 0
-- The spent digest stays burned: anti-replay survives settlement.
#guard (draw demo₂ 7 10).isNone
-- A fresh digest draws fine on the restored line.
#guard (draw demo₂ 9 100).isSome

/-- Hard-asset settlement: close the line at 30 drawn; both parties start with 500 hard. -/
def demoCh : Channel := { tl := demo₁, issuerHard := 500, holderHard := 500 }
/-- The closed channel. -/
def demoCh' : Channel := settleAll demoCh

#guard demoCh'.tl.drawn == 0
#guard demoCh'.issuerHard == 530
#guard demoCh'.holderHard == 470
-- The hard pair is conserved: 530 + 470 = 500 + 500.
#guard demoCh'.issuerHard + demoCh'.holderHard == demoCh.issuerHard + demoCh.holderHard

/-! ## §8 — Axiom-hygiene tripwires. -/

#assert_axioms draw_spec
#assert_axioms repay_spec
#assert_axioms init_WF
#assert_axioms init_remaining
#assert_axioms draw_within_line
#assert_axioms over_line_draw_refused
#assert_axioms draw_records
#assert_axioms draw_replay_refused
#assert_axioms draw_digest_was_fresh
#assert_axioms repay_draws_fixed
#assert_axioms bilateral_conserved
#assert_axioms repay_monotone_down
#assert_axioms over_repay_refused
#assert_axioms draw_repay_roundtrip
#assert_axioms settlePay_conserves_hard
#assert_axioms settleAll_clears
#assert_axioms draw_preserves_WF
#assert_axioms repay_preserves_WF
#assert_axioms trustline_WF_forever
#assert_axioms trustline_within_line_forever
#assert_axioms trustline_conserved_forever
#assert_axioms no_double_draw_forever
#assert_axioms holder_credit_le_line_forever
#assert_axioms ceiling_immutable_forever
#assert_axioms draw_slice_tracks_tryDebit
#assert_axioms draw_fires_iff_tryDebit

/-! ## §9 — The `settled` register: monotone redemption (the DEPLOYED settlement shape).

The node weld (`node/src/trustline_service.rs` + `cell/src/blueprint.rs` `TL_SETTLED_SLOT`)
settles by marching a MONOTONE redemption register: `settle paid` does `settled := settled +
paid` and pays the holder `paid` out of the escrow, leaving `drawn` in place — §5b's `settleAll`
zeroing is the pureCredit unwind (§12), not the deployed fullReserve shape. The installed program
teeth (`trustline_state_constraints` tooth 4): `Monotonic(settled)` + `settled ≤ drawn` on top of
the existing `drawn ≤ ceiling`; the inequality chain IS solvency (`solvency`): cumulative payouts
= `settled` ≤ `ceiling` = the escrowed line. Repay gains the SETTLED FLOOR: the deployed gate is
`amt ≤ drawn − settled` (`post_trustline_repay`'s `outstanding`), strictly tighter than §2's
`amt ≤ drawn` — settled credit is hard money already paid out and cannot be repaid back. -/

/-- A trustline with the settlement register: §1's `Line` + `settled` (`TL_SETTLED_SLOT`). -/
structure SLine where
  /-- The underlying line (the §1 registers). -/
  tl : Line
  /-- Cumulative drawn value already redeemed to the holder by epoch settlement. Monotone. -/
  settled : Nat
  deriving Repr, DecidableEq

/-- Outstanding unsettled draw — the deployed repay/settle budget (`drawn − settled`). -/
def SLine.outstanding (s : SLine) : Nat := s.tl.drawn - s.settled

/-- Settled well-formedness: the line is WF and `settled ≤ drawn` (program tooth 4). -/
def SLine.WF (s : SLine) : Prop := s.tl.WF ∧ s.settled ≤ s.tl.drawn

instance (s : SLine) : Decidable s.WF := by
  unfold SLine.WF; infer_instance

/-- Birth of a settled line: fresh line, nothing settled. -/
def SLine.init (n : Nat) : SLine := { tl := Line.init n, settled := 0 }

/-- Birth is well-formed. -/
theorem init_SWF (n : Nat) : (SLine.init n).WF := ⟨init_WF n, Nat.le_refl 0⟩

/-- Draw on the settled line — the §2 gate unchanged (`settled` plays no part in draws:
the deployed remaining is `line − drawn`, `resolve_trustline`). -/
def drawS (s : SLine) (digest amt : Nat) : Option SLine :=
  (draw s.tl digest amt).map fun tl' => { s with tl := tl' }

/-- Repay with the SETTLED FLOOR (the deployed gate, `post_trustline_repay`): fail-closed
beyond the outstanding `drawn − settled`. -/
def repayS (s : SLine) (amt : Nat) : Option SLine :=
  if amt ≤ s.outstanding then (repay s.tl amt).map fun tl' => { s with tl := tl' } else none

/-- **`settleS` — the deployed settle** (`post_trustline_settle`): march `settled` up by the
paid amount; `drawn` and the digest registry untouched. Fail-closed beyond the outstanding draw
(the executor refuses `settled > drawn` — program tooth 4). The hard-asset leg lives on the
channel (§12 `settleC`). -/
def settleS (s : SLine) (paid : Nat) : Option SLine :=
  if paid ≤ s.outstanding then some { s with settled := s.settled + paid } else none

/-- Commit-shape lemma for `drawS`. -/
theorem drawS_spec {s s' : SLine} {d amt : Nat} (h : drawS s d amt = some s') :
    ∃ tl', draw s.tl d amt = some tl' ∧ s' = { s with tl := tl' } := by
  unfold drawS at h
  cases htl : draw s.tl d amt with
  | none => rw [htl] at h; exact absurd h (by simp)
  | some tl' =>
      rw [htl] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨tl', rfl, h.symm⟩

/-- Commit-shape lemma for `repayS`: the floor held AND the underlying repay committed. -/
theorem repayS_spec {s s' : SLine} {amt : Nat} (h : repayS s amt = some s') :
    amt ≤ s.outstanding ∧ ∃ tl', repay s.tl amt = some tl' ∧ s' = { s with tl := tl' } := by
  unfold repayS at h
  by_cases hg : amt ≤ s.outstanding
  · rw [if_pos hg] at h
    cases htl : repay s.tl amt with
    | none => rw [htl] at h; exact absurd h (by simp)
    | some tl' =>
        rw [htl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨hg, tl', rfl, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- Commit-shape lemma for `settleS`. -/
theorem settleS_spec {s s' : SLine} {paid : Nat} (h : settleS s paid = some s') :
    paid ≤ s.outstanding ∧ s' = { s with settled := s.settled + paid } := by
  unfold settleS at h
  by_cases hg : paid ≤ s.outstanding
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`settle_monotone`** — a committed settle marches `settled` UP by exactly `paid`
(the `Monotonic(TL_SETTLED_SLOT)` program tooth, per-step). -/
theorem settle_monotone {s s' : SLine} {paid : Nat} (h : settleS s paid = some s') :
    s'.settled = s.settled + paid ∧ s.settled ≤ s'.settled := by
  obtain ⟨-, rfl⟩ := settleS_spec h
  exact ⟨rfl, Nat.le_add_right ..⟩

/-- Settle leaves the whole underlying line fixed: `drawn`, `ceiling`, AND the digest registry —
a settle epoch never resurrects a burned digest. -/
theorem settleS_tl_fixed {s s' : SLine} {paid : Nat} (h : settleS s paid = some s') :
    s'.tl = s.tl := by
  obtain ⟨-, rfl⟩ := settleS_spec h
  rfl

/-- **`repay_below_settled_refused` — the settled-floor tooth.** A repay beyond the outstanding
`drawn − settled` is fail-closed `none`, EVEN when §2's plain gate (`amt ≤ drawn`) would have
admitted it: settled credit is hard money already paid to the holder. -/
theorem repay_below_settled_refused {s : SLine} {amt : Nat} (h : ¬ amt ≤ s.outstanding) :
    repayS s amt = none :=
  if_neg h

/-- **`over_settle_refused`** — settling more than the outstanding draw is fail-closed `none`
(it would redeem value that was never drawn: `settled > drawn` violates program tooth 4). -/
theorem over_settle_refused {s : SLine} {paid : Nat} (h : ¬ paid ≤ s.outstanding) :
    settleS s paid = none :=
  if_neg h

/-- The settled floor is TIGHT: a repay fires IFF it is within the outstanding draw. -/
theorem repayS_fires_iff (s : SLine) (amt : Nat) :
    (repayS s amt).isSome = true ↔ amt ≤ s.outstanding := by
  unfold repayS
  by_cases hg : amt ≤ s.outstanding
  · rw [if_pos hg]
    have hd : amt ≤ s.tl.drawn := Nat.le_trans hg (Nat.sub_le _ _)
    unfold repay
    rw [if_pos hd]
    simp [hg]
  · rw [if_neg hg]
    simp [hg]

/-- The settle gate is TIGHT: a settle fires IFF it is within the outstanding draw. -/
theorem settleS_fires_iff (s : SLine) (paid : Nat) :
    (settleS s paid).isSome = true ↔ paid ≤ s.outstanding := by
  unfold settleS
  by_cases hg : paid ≤ s.outstanding
  · rw [if_pos hg]; simp [hg]
  · rw [if_neg hg]; simp [hg]

/-- A committed draw preserves settled well-formedness (`drawn` only goes up). -/
theorem drawS_preserves_WF {s s' : SLine} {d amt : Nat} (hwf : s.WF)
    (h : drawS s d amt = some s') : s'.WF := by
  obtain ⟨htl, hs⟩ := hwf
  obtain ⟨tl', htl', rfl⟩ := drawS_spec h
  refine ⟨draw_preserves_WF htl htl', ?_⟩
  have hdr := (draw_records htl').1
  show s.settled ≤ tl'.drawn
  omega

/-- A committed repay preserves settled well-formedness — BECAUSE of the settled floor
(`drawn` lands at `drawn − amt ≥ settled` exactly when `amt ≤ outstanding`). -/
theorem repayS_preserves_WF {s s' : SLine} {amt : Nat} (hwf : s.WF)
    (h : repayS s amt = some s') : s'.WF := by
  obtain ⟨htl, hs⟩ := hwf
  obtain ⟨hg, tl', htl', rfl⟩ := repayS_spec h
  refine ⟨repay_preserves_WF htl htl', ?_⟩
  have hdr := (repay_monotone_down htl').1
  have hg' : amt ≤ s.tl.drawn - s.settled := hg
  show s.settled ≤ tl'.drawn
  omega

/-- A committed settle preserves settled well-formedness (`settled` lands ≤ `drawn`). -/
theorem settleS_preserves_WF {s s' : SLine} {paid : Nat} (hwf : s.WF)
    (h : settleS s paid = some s') : s'.WF := by
  obtain ⟨htl, hs⟩ := hwf
  obtain ⟨hg, rfl⟩ := settleS_spec h
  refine ⟨htl, ?_⟩
  have hg' : paid ≤ s.tl.drawn - s.settled := hg
  show s.settled + paid ≤ s.tl.drawn
  omega

/-! ## §10 — The FOREVER crowns on the settled model: draws, repays, AND settle epochs.

The §6 adversarial-schedule pattern, with `settle` added to the adversary's alphabet. Every §6
keystone survives the extension, and the new settled-register laws ride the same trajectories. -/

/-- One adversarial op against the settled line (the §6 `TLOp` alphabet + `settle`). -/
inductive SOp where
  | draw (digest amt : Nat)
  | repay (amt : Nat)
  | settle (paid : Nat)
  deriving Repr, DecidableEq

/-- An adversarial schedule over the settled alphabet. -/
def SSched : Type := Nat → SOp

/-- One step: apply the op; a refused op leaves the state fixed (fail-closed no-op). -/
def stepS (s : SLine) : SOp → SLine
  | .draw d a  => (drawS s d a).getD s
  | .repay a   => (repayS s a).getD s
  | .settle p  => (settleS s p).getD s

/-- The trajectory under a settled schedule. -/
def trajS (s₀ : SLine) (sched : SSched) : Nat → SLine
  | 0     => s₀
  | n + 1 => stepS (trajS s₀ sched n) (sched n)

/-- One adversarial step preserves settled well-formedness. -/
theorem stepS_preserves_WF (s : SLine) (op : SOp) (hwf : s.WF) : (stepS s op).WF := by
  cases op with
  | draw d a =>
      show ((drawS s d a).getD s).WF
      cases h : drawS s d a with
      | some s' => simp only [Option.getD_some]; exact drawS_preserves_WF hwf h
      | none    => simp only [Option.getD_none]; exact hwf
  | repay a =>
      show ((repayS s a).getD s).WF
      cases h : repayS s a with
      | some s' => simp only [Option.getD_some]; exact repayS_preserves_WF hwf h
      | none    => simp only [Option.getD_none]; exact hwf
  | settle p =>
      show ((settleS s p).getD s).WF
      cases h : settleS s p with
      | some s' => simp only [Option.getD_some]; exact settleS_preserves_WF hwf h
      | none    => simp only [Option.getD_none]; exact hwf

/-- **`sline_WF_forever`** — settled well-formedness rides every adversarial trajectory. -/
theorem sline_WF_forever (s₀ : SLine) (hinit : s₀.WF) (sched : SSched) :
    ∀ n, (trajS s₀ sched n).WF := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih => exact stepS_preserves_WF (trajS s₀ sched k) (sched k) ih

/-- **`settle_le_drawn_forever`** — `settled ≤ drawn` at every reachable state: redemption
never runs ahead of exercise, along every schedule of draws/repays/settles. -/
theorem settle_le_drawn_forever (s₀ : SLine) (hinit : s₀.WF) (sched : SSched) :
    ∀ n, (trajS s₀ sched n).settled ≤ (trajS s₀ sched n).tl.drawn :=
  fun n => (sline_WF_forever s₀ hinit sched n).2

/-- **`solvency`** — the program inequality chain IS solvency: cumulative payouts (`settled`)
never exceed the escrowed line (`ceiling`), via `settled ≤ drawn ≤ ceiling`. -/
theorem solvency {s : SLine} (hwf : s.WF) : s.settled ≤ s.tl.ceiling := by
  obtain ⟨⟨hle, -, -, -⟩, hs⟩ := hwf
  omega

/-- **`solvency_forever`** — payouts ≤ the escrowed line at every reachable state. -/
theorem solvency_forever (s₀ : SLine) (hinit : s₀.WF) (sched : SSched) :
    ∀ n, (trajS s₀ sched n).settled ≤ (trajS s₀ sched n).tl.ceiling :=
  fun n => solvency (sline_WF_forever s₀ hinit sched n)

/-- KEYSTONE 1 lifts to the settled model: drawn ≤ ceiling forever. -/
theorem sline_within_line_forever (s₀ : SLine) (hinit : s₀.WF) (sched : SSched) :
    ∀ n, (trajS s₀ sched n).tl.drawn ≤ (trajS s₀ sched n).tl.ceiling :=
  fun n => (sline_WF_forever s₀ hinit sched n).1.1

/-- KEYSTONE 2 lifts to the settled model: the bilateral credit pair sums to zero forever. -/
theorem sline_conserved_forever (s₀ : SLine) (hinit : s₀.WF) (sched : SSched) :
    ∀ n, (trajS s₀ sched n).tl.holderAcct + (trajS s₀ sched n).tl.issuerWell = 0 :=
  fun n => bilateral_conserved (sline_WF_forever s₀ hinit sched n).1

/-- KEYSTONE 3 lifts to the settled model: the digest registry is duplicate-free at every
reachable state — INCLUDING across settle epochs. -/
theorem no_double_draw_forever_across_settles (s₀ : SLine) (hinit : s₀.WF) (sched : SSched) :
    ∀ n, (trajS s₀ sched n).tl.draws.Nodup :=
  fun n => (sline_WF_forever s₀ hinit sched n).1.2.2.2

/-- One step never moves `settled` down (draw/repay leave it fixed; settle marches it up). -/
theorem stepS_settled_mono (s : SLine) (op : SOp) : s.settled ≤ (stepS s op).settled := by
  cases op with
  | draw d a =>
      show s.settled ≤ ((drawS s d a).getD s).settled
      cases h : drawS s d a with
      | some s' =>
          obtain ⟨tl', -, rfl⟩ := drawS_spec h
          simp only [Option.getD_some]
          exact Nat.le_refl _
      | none => simp only [Option.getD_none]; exact Nat.le_refl _
  | repay a =>
      show s.settled ≤ ((repayS s a).getD s).settled
      cases h : repayS s a with
      | some s' =>
          obtain ⟨-, tl', -, rfl⟩ := repayS_spec h
          simp only [Option.getD_some]
          exact Nat.le_refl _
      | none => simp only [Option.getD_none]; exact Nat.le_refl _
  | settle p =>
      show s.settled ≤ ((settleS s p).getD s).settled
      cases h : settleS s p with
      | some s' =>
          obtain ⟨-, rfl⟩ := settleS_spec h
          simp only [Option.getD_some]
          exact Nat.le_add_right ..
      | none => simp only [Option.getD_none]; exact Nat.le_refl _

/-- **`settled_monotone_forever`** — the settled register NEVER moves down along any schedule:
the `Monotonic(TL_SETTLED_SLOT)` program caveat, as a trajectory law. -/
theorem settled_monotone_forever (s₀ : SLine) (sched : SSched) :
    ∀ n m, n ≤ m → (trajS s₀ sched n).settled ≤ (trajS s₀ sched m).settled := by
  intro n m hnm
  induction m with
  | zero =>
      have h0 : n = 0 := Nat.le_zero.mp hnm
      subst h0
      exact Nat.le_refl _
  | succ k ih =>
      by_cases hk : n ≤ k
      · exact Nat.le_trans (ih hk) (stepS_settled_mono (trajS s₀ sched k) (sched k))
      · have heq : n = k + 1 := by omega
        subst heq
        exact Nat.le_refl _

/-- One step never REMOVES a digest from the registry (draw conses; repay and settle leave it
fixed): the registry is monotone — the node `TrustlineRegistry` shape. -/
theorem stepS_draws_mono (s : SLine) (op : SOp) {d : Nat} (hd : d ∈ s.tl.draws) :
    d ∈ (stepS s op).tl.draws := by
  cases op with
  | draw dg a =>
      show d ∈ ((drawS s dg a).getD s).tl.draws
      cases h : drawS s dg a with
      | some s' =>
          obtain ⟨tl', htl', rfl⟩ := drawS_spec h
          obtain ⟨-, -, rfl⟩ := draw_spec htl'
          simp only [Option.getD_some]
          exact List.mem_cons_of_mem _ hd
      | none => simp only [Option.getD_none]; exact hd
  | repay a =>
      show d ∈ ((repayS s a).getD s).tl.draws
      cases h : repayS s a with
      | some s' =>
          obtain ⟨-, tl', htl', rfl⟩ := repayS_spec h
          simp only [Option.getD_some]
          show d ∈ tl'.draws
          rw [repay_draws_fixed htl']
          exact hd
      | none => simp only [Option.getD_none]; exact hd
  | settle p =>
      show d ∈ ((settleS s p).getD s).tl.draws
      cases h : settleS s p with
      | some s' =>
          obtain ⟨-, rfl⟩ := settleS_spec h
          simp only [Option.getD_some]
          exact hd
      | none => simp only [Option.getD_none]; exact hd

/-- **`digest_burned_forever`** — once a digest is in the registry it is there at EVERY later
state, across repays AND settle epochs. This is the law of the node's `TrustlineRegistry`
(the FOREVER anti-replay carrier) — the Stingray slice's own `debits` list resets at each
rebalance epoch and is NOT this carrier. -/
theorem digest_burned_forever (s₀ : SLine) (sched : SSched) {d n : Nat}
    (h : d ∈ (trajS s₀ sched n).tl.draws) :
    ∀ m, n ≤ m → d ∈ (trajS s₀ sched m).tl.draws := by
  intro m hnm
  induction m with
  | zero =>
      have h0 : n = 0 := Nat.le_zero.mp hnm
      subst h0
      exact h
  | succ k ih =>
      by_cases hk : n ≤ k
      · exact stepS_draws_mono (trajS s₀ sched k) (sched k) (ih hk)
      · have heq : n = k + 1 := by omega
        subst heq
        exact h

/-- **`draw_replay_refused_across_epochs` — the WIDENED anti-replay scope.** A digest committed
at step `n` is refused at EVERY later step `m ≥ n`, no matter how many settle (rebalance) epochs
pass in between: `try_debit_fresh`'s slice registry resets at rebalance, so the forever property
is carried by the node `TrustlineRegistry`, and this is exactly its law. -/
theorem draw_replay_refused_across_epochs (s₀ : SLine) (sched : SSched) {d n : Nat}
    (h : d ∈ (trajS s₀ sched n).tl.draws) {m : Nat} (hnm : n ≤ m) (amt : Nat) :
    drawS (trajS s₀ sched m) d amt = none := by
  have hd := digest_burned_forever s₀ sched h m hnm
  unfold drawS
  rw [draw_replay_refused hd]
  rfl

/-- One step leaves the ceiling fixed on the settled alphabet too. -/
theorem stepS_ceiling_fixed (s : SLine) (op : SOp) : (stepS s op).tl.ceiling = s.tl.ceiling := by
  cases op with
  | draw d a =>
      show ((drawS s d a).getD s).tl.ceiling = s.tl.ceiling
      cases h : drawS s d a with
      | some s' =>
          obtain ⟨tl', htl', rfl⟩ := drawS_spec h
          simp only [Option.getD_some]
          exact (draw_records htl').2.1
      | none => rfl
  | repay a =>
      show ((repayS s a).getD s).tl.ceiling = s.tl.ceiling
      cases h : repayS s a with
      | some s' =>
          obtain ⟨-, tl', htl', rfl⟩ := repayS_spec h
          simp only [Option.getD_some]
          exact (repay_monotone_down htl').2
      | none => rfl
  | settle p =>
      show ((settleS s p).getD s).tl.ceiling = s.tl.ceiling
      cases h : settleS s p with
      | some s' =>
          obtain ⟨-, rfl⟩ := settleS_spec h
          rfl
      | none => rfl

/-- **`sline_ceiling_immutable_forever`** — the line is the same N at every reachable state of
the settled model: settlement never amends the extension. -/
theorem sline_ceiling_immutable_forever (s₀ : SLine) (sched : SSched) :
    ∀ n, (trajS s₀ sched n).tl.ceiling = s₀.tl.ceiling := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [show trajS s₀ sched (k+1) = stepS (trajS s₀ sched k) (sched k) from rfl,
          stepS_ceiling_fixed, ih]

/-! ### §10b — The epoch-slice weld: `ensure_coordinator`'s rebuild rule is faithful.

The node rebuilds the Stingray coordinator shadow from the cell registers
(`node/src/trustline_service.rs::ensure_coordinator`): `total_balance = line − settled`, with the
outstanding `drawn − settled` re-debited. Its doc-comment claims "the two draw gates agree at
every reachable state" — here that claim is a theorem. -/

/-- The rebalance-epoch slice the node rebuilds: `ceiling = line − settled`,
`spent = drawn − settled`. -/
def SLine.epochSlice (s : SLine) : Slice := ⟨s.tl.ceiling - s.settled, s.tl.drawn - s.settled⟩

/-- **`epochSlice_remaining`** — the rebuild rule is FAITHFUL: the rebuilt epoch slice's
remaining equals the cell's remaining line (`line − drawn`) at every well-formed state. -/
theorem epochSlice_remaining {s : SLine} (hwf : s.WF) :
    s.epochSlice.remaining = s.tl.remaining := by
  obtain ⟨⟨hle, -, -, -⟩, hs⟩ := hwf
  show s.tl.ceiling - s.settled - (s.tl.drawn - s.settled) = s.tl.ceiling - s.tl.drawn
  omega

/-- **`drawS_fires_iff_epoch_tryDebit`** — for a fresh digest, the deployed draw gate
(`try_debit_fresh` on the REBUILT epoch slice) and the model draw gate agree exactly, at every
epoch — `draw_fires_iff_tryDebit` widened from the birth slice to every rebalance epoch. -/
theorem drawS_fires_iff_epoch_tryDebit {s : SLine} (hwf : s.WF) (d amt : Nat)
    (hfresh : d ∉ s.tl.draws) :
    (drawS s d amt).isSome = (s.epochSlice.tryDebit amt).isSome := by
  have h1 : (drawS s d amt).isSome = (draw s.tl d amt).isSome := by
    unfold drawS
    cases draw s.tl d amt <;> rfl
  rw [h1, draw_fires_iff_tryDebit s.tl d amt hfresh]
  have hrem : s.epochSlice.remaining = s.tl.slice.remaining := by
    rw [epochSlice_remaining hwf]
    exact Line.remaining_eq_slice s.tl
  unfold Slice.tryDebit
  by_cases hb : amt ≤ s.tl.slice.remaining
  · rw [if_pos hb, if_pos (show amt ≤ s.epochSlice.remaining by rw [hrem]; exact hb)]
    rfl
  · rw [if_neg hb, if_neg (show ¬ amt ≤ s.epochSlice.remaining by rw [hrem]; exact hb)]

/-- **`drawS_tracks_epoch_tryDebit`** — a committed draw moves the rebuilt epoch slice exactly
as `Slice.tryDebit`: the counter gate and the executor tooth cannot disagree at any epoch. -/
theorem drawS_tracks_epoch_tryDebit {s s' : SLine} {d amt : Nat} (hwf : s.WF)
    (h : drawS s d amt = some s') :
    s.epochSlice.tryDebit amt = some s'.epochSlice := by
  obtain ⟨-, hs⟩ := hwf
  obtain ⟨tl', htl', rfl⟩ := drawS_spec h
  obtain ⟨-, hb, rfl⟩ := draw_spec htl'
  unfold Slice.tryDebit
  rw [if_pos (show amt ≤ s.epochSlice.remaining by
        show amt ≤ s.tl.ceiling - s.settled - (s.tl.drawn - s.settled)
        omega)]
  refine congrArg some (Slice.ext rfl ?_)
  show s.tl.drawn - s.settled + amt = s.tl.drawn + amt - s.settled
  omega

/-! ## §11 — Derived credit registers: the deployed cell carries NO ±drawn pair.

The Rust position (`TrustlinePosition` / `resolve_trustline`) stores `ceiling`/`drawn`/`settled`
and DERIVES the bilateral credit view from `drawn` — `holderAcct = +drawn` / `issuerWell =
−drawn` are exactly `Line.WF`'s coupling equations, so the deployment carries them implicitly.
Faithfulness, both directions: reconstruction from the stored registers is exact
(`derived_view_faithful`), and the derived view determines the modeled state
(`view_determines_line`) — no information loss. -/

/-- Reconstruct a `Line` from the registers the deployment stores (the derived view). -/
def Line.ofView (ceiling drawn : Nat) (draws : List Nat) : Line :=
  { ceiling := ceiling, drawn := drawn, draws := draws
  , holderAcct := (drawn : Int), issuerWell := -(drawn : Int) }

/-- The reconstruction is well-formed whenever the stored registers are legal. -/
theorem ofView_WF {ceiling drawn : Nat} {draws : List Nat}
    (hle : drawn ≤ ceiling) (hnd : draws.Nodup) : (Line.ofView ceiling drawn draws).WF :=
  ⟨hle, rfl, rfl, hnd⟩

/-- **`derived_view_faithful`** — on every well-formed state, reconstructing from the stored
registers returns EXACTLY the modeled state: the ± credit pair is redundant given `drawn`. -/
theorem derived_view_faithful {t : Line} (hwf : t.WF) :
    Line.ofView t.ceiling t.drawn t.draws = t := by
  obtain ⟨-, hh, hw, -⟩ := hwf
  show Line.mk t.ceiling t.drawn t.draws (t.drawn : Int) (-(t.drawn : Int)) = t
  rw [← hw, ← hh]

/-- **`view_determines_line` — NO INFORMATION LOSS.** Two well-formed states agreeing on the
registers the deployment stores are EQUAL: deriving `holderAcct`/`issuerWell` from `drawn`
(instead of carrying them) loses nothing. -/
theorem view_determines_line {t u : Line} (ht : t.WF) (hu : u.WF)
    (hc : t.ceiling = u.ceiling) (hd : t.drawn = u.drawn) (hds : t.draws = u.draws) :
    t = u := by
  rw [← derived_view_faithful ht, ← derived_view_faithful hu, hc, hd, hds]

/-- The settled-line reconstruction (`TrustlinePosition` + the registry). -/
def SLine.ofView (ceiling drawn settled : Nat) (draws : List Nat) : SLine :=
  { tl := Line.ofView ceiling drawn draws, settled := settled }

/-- `derived_view_faithful` lifted to the settled model. -/
theorem sline_derived_view_faithful {s : SLine} (hwf : s.WF) :
    SLine.ofView s.tl.ceiling s.tl.drawn s.settled s.tl.draws = s := by
  show SLine.mk (Line.ofView s.tl.ceiling s.tl.drawn s.tl.draws) s.settled = s
  rw [derived_view_faithful hwf.1]

/-! ## §12 — The collateral axis, reified (docs/ORGANS.md parameterization discipline).

§5b's `settlePay` is the pureCredit point (holder repays HARD value to the issuer; the credit
legs unwind); the deployed node is the fullReserve point (the issuer escrowed the full line at
open; settle pays the holder OUT OF THE ESCROW while `settled` marches). One axis, two points,
ONE parametric conservation keystone — the Rust settle is a theorem instance, not a divergence. -/

/-- The collateral backing of a line (docs/TRUSTLINES.md §2/§5). -/
inductive Collateral where
  /-- The full line is escrowed at open (payment-channel point — the DEPLOYED node weld). -/
  | fullReserve
  /-- No hard backing; the line is the issuer's consented risk (mutual-credit point — §5b). -/
  | pureCredit
  deriving Repr, DecidableEq

/-- The bilateral channel across the collateral axis: the settled line + the three hard-asset
columns (the trustline cell's own escrow balance, and the two parties' balances). -/
structure ChannelC where
  /-- The settled trustline registers. -/
  s : SLine
  /-- The trustline cell's own hard balance — the fullReserve escrow (`cell.state.balance()`;
  zero at the pureCredit point). -/
  escrow : Int
  /-- Issuer's hard-asset balance. -/
  issuerHard : Int
  /-- Holder's hard-asset balance. -/
  holderHard : Int
  deriving Repr, DecidableEq

/-- Replace the registers, keep the hard columns (draws/repays move no hard value). -/
def ChannelC.withS (c : ChannelC) (s' : SLine) : ChannelC := { c with s := s' }

/-- The total hard-asset column. -/
def ChannelC.hardTotal (c : ChannelC) : Int := c.escrow + c.issuerHard + c.holderHard

/-- The §5b projection (drop the escrow column, forget `settled`). -/
def ChannelC.channel (c : ChannelC) : Channel :=
  { tl := c.s.tl, issuerHard := c.issuerHard, holderHard := c.holderHard }

/-- **`settleC` — settlement at a point of the collateral axis.**
* `fullReserve` (the deployed `post_trustline_settle`): the `settled` register marches up and
  the cell pays the holder out of the escrow — `Effect::Transfer { from: trustline, to: holder }`.
* `pureCredit` (§5b `settlePay`): the credit legs unwind (a floored repay) and the holder pays
  the issuer hard value. -/
def settleC : Collateral → ChannelC → Nat → Option ChannelC
  | .fullReserve, c, paid =>
      (settleS c.s paid).map fun s' =>
        { c with s := s'
               , escrow := c.escrow - (paid : Int)
               , holderHard := c.holderHard + (paid : Int) }
  | .pureCredit, c, paid =>
      (repayS c.s paid).map fun s' =>
        { c with s := s'
               , issuerHard := c.issuerHard + (paid : Int)
               , holderHard := c.holderHard - (paid : Int) }

/-- **`settleC_conserves_hard` — THE PARAMETRIC CONSERVATION KEYSTONE.** At BOTH points of the
collateral axis, settlement is a MOVE on the hard columns: the total is exactly conserved. -/
theorem settleC_conserves_hard (mode : Collateral) {c c' : ChannelC} {paid : Nat}
    (h : settleC mode c paid = some c') : c'.hardTotal = c.hardTotal := by
  cases mode with
  | fullReserve =>
      simp only [settleC] at h
      cases hs : settleS c.s paid with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some s' =>
          rw [hs] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          show c.escrow - (paid : Int) + c.issuerHard + (c.holderHard + (paid : Int))
              = c.escrow + c.issuerHard + c.holderHard
          omega
  | pureCredit =>
      simp only [settleC] at h
      cases hr : repayS c.s paid with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some s' =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          show c.escrow + (c.issuerHard + (paid : Int)) + (c.holderHard - (paid : Int))
              = c.escrow + c.issuerHard + c.holderHard
          omega

/-- The deployed fullReserve settle, commit-shape: gate + the exact five-register move
(`settled` up, `drawn`/`draws`/`ceiling` fixed, escrow→holder by exactly `paid`). -/
theorem settleC_fullReserve_spec {c c' : ChannelC} {paid : Nat}
    (h : settleC .fullReserve c paid = some c') :
    paid ≤ c.s.outstanding
      ∧ c'.s.settled = c.s.settled + paid
      ∧ c'.s.tl = c.s.tl
      ∧ c'.escrow = c.escrow - (paid : Int)
      ∧ c'.holderHard = c.holderHard + (paid : Int)
      ∧ c'.issuerHard = c.issuerHard := by
  simp only [settleC] at h
  cases hs : settleS c.s paid with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some s' =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hg, rfl⟩ := settleS_spec hs
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl⟩

/-- **`settleReserve_conserves_hard`** — the DEPLOYED point as a theorem instance: the Rust
settle (`escrow → holder` Transfer of the net position) conserves the hard column — the
fullReserve analogue of `settlePay_conserves_hard`. -/
theorem settleReserve_conserves_hard {c c' : ChannelC} {paid : Nat}
    (h : settleC .fullReserve c paid = some c') : c'.hardTotal = c.hardTotal :=
  settleC_conserves_hard .fullReserve h

/-- The deployed settle conserves the BILATERAL pair it touches (escrow + holder), and never
touches the issuer's column at all. -/
theorem settleReserve_conserves_pair {c c' : ChannelC} {paid : Nat}
    (h : settleC .fullReserve c paid = some c') :
    c'.escrow + c'.holderHard = c.escrow + c.holderHard ∧ c'.issuerHard = c.issuerHard := by
  obtain ⟨-, -, -, hesc, hhold, hiss⟩ := settleC_fullReserve_spec h
  rw [hesc, hhold]
  exact ⟨by omega, hiss⟩

/-- **`settleC_pureCredit_agrees_settlePay`** — the pureCredit point IS §5b's `settlePay`: a
committed pure-credit settle projects to a committed `settlePay` with the same hard moves, and
never touches the escrow column. -/
theorem settleC_pureCredit_agrees_settlePay {c c' : ChannelC} {paid : Nat}
    (h : settleC .pureCredit c paid = some c') :
    settlePay c.channel paid = some c'.channel ∧ c'.escrow = c.escrow := by
  simp only [settleC] at h
  cases hr : repayS c.s paid with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some s' =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨-, tl', htl', rfl⟩ := repayS_spec hr
      refine ⟨?_, rfl⟩
      have hrt : repay c.channel.tl paid = some tl' := htl'
      unfold settlePay
      rw [hrt]
      simp only [Option.map_some]
      rfl

/-- The pureCredit gate is COMPLETE at its native setting (`settled = 0`, where it lives):
anything `settlePay` admits, the axis point admits — §5b is recovered, not narrowed. -/
theorem settleC_pureCredit_total {c : ChannelC} (h0 : c.s.settled = 0) {paid : Nat}
    (hp : paid ≤ c.s.tl.drawn) : (settleC .pureCredit c paid).isSome := by
  have hg : paid ≤ c.s.outstanding := by
    show paid ≤ c.s.tl.drawn - c.s.settled
    omega
  have hr : (repayS c.s paid).isSome = true := (repayS_fires_iff c.s paid).mpr hg
  simp only [settleC]
  cases h : repayS c.s paid with
  | none => rw [h] at hr; exact absurd hr (by simp)
  | some s' => rfl

/-! ### §12b — The hard column along adversarial channel trajectories (both modes). -/

/-- One channel step at a collateral mode: draws/repays move ONLY the credit registers
(the deployed draw/repay routes move no hard value — value moves at settle). -/
def stepC (mode : Collateral) (c : ChannelC) : SOp → ChannelC
  | .draw d a  => ((drawS c.s d a).map c.withS).getD c
  | .repay a   => ((repayS c.s a).map c.withS).getD c
  | .settle p  => (settleC mode c p).getD c

/-- The channel trajectory under a schedule, at a collateral mode. -/
def trajC (mode : Collateral) (c₀ : ChannelC) (sched : SSched) : Nat → ChannelC
  | 0     => c₀
  | n + 1 => stepC mode (trajC mode c₀ sched n) (sched n)

/-- One channel step conserves the hard column, at both modes. -/
theorem stepC_hard_fixed (mode : Collateral) (c : ChannelC) (op : SOp) :
    (stepC mode c op).hardTotal = c.hardTotal := by
  cases op with
  | draw d a =>
      show (((drawS c.s d a).map c.withS).getD c).hardTotal = c.hardTotal
      cases drawS c.s d a <;> rfl
  | repay a =>
      show (((repayS c.s a).map c.withS).getD c).hardTotal = c.hardTotal
      cases repayS c.s a <;> rfl
  | settle p =>
      show ((settleC mode c p).getD c).hardTotal = c.hardTotal
      cases h : settleC mode c p with
      | some c' => simp only [Option.getD_some]; exact settleC_conserves_hard mode h
      | none => rfl

/-- **`hard_conserved_forever`** — at BOTH points of the collateral axis, the total hard column
is constant along every adversarial schedule: settlement moves value, never makes it. The
`.fullReserve` instance is the deployed Rust point. -/
theorem hard_conserved_forever (mode : Collateral) (c₀ : ChannelC) (sched : SSched) :
    ∀ n, (trajC mode c₀ sched n).hardTotal = c₀.hardTotal := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [show trajC mode c₀ sched (k+1) = stepC mode (trajC mode c₀ sched k) (sched k) from rfl,
          stepC_hard_fixed, ih]

/-! ### §12c — fullReserve solvency: the escrow column can always pay. -/

/-- The fullReserve OPEN shape (the deployed `post_trustline_open`): fresh line, the FULL line
escrowed by a real issuer debit (a move, never a mint). -/
def ChannelC.openReserve (n : Nat) (issuerHard holderHard : Int) : ChannelC :=
  { s := SLine.init n
  , escrow := (n : Int)
  , issuerHard := issuerHard - (n : Int)
  , holderHard := holderHard }

/-- The funded birth is a MOVE: opening conserves the hard column. -/
theorem openReserve_is_a_move (n : Nat) (ih hh : Int) :
    (ChannelC.openReserve n ih hh).hardTotal = ih + hh := by
  show (n : Int) + (ih - (n : Int)) + hh = ih + hh
  omega

/-- fullReserve channel well-formedness: registers WF + the escrow column carries EXACTLY the
unredeemed line (`line − settled`): the open flow escrows `line`; each settle pays out of it. -/
def ChannelC.ReserveWF (c : ChannelC) : Prop :=
  c.s.WF ∧ c.escrow = (c.s.tl.ceiling : Int) - (c.s.settled : Int)

instance (c : ChannelC) : Decidable c.ReserveWF := by
  unfold ChannelC.ReserveWF; infer_instance

/-- The open shape is ReserveWF. -/
theorem openReserve_ReserveWF (n : Nat) (ih hh : Int) :
    (ChannelC.openReserve n ih hh).ReserveWF := by
  refine ⟨init_SWF n, ?_⟩
  show (n : Int) = (n : Int) - ((0 : Nat) : Int)
  omega

/-- **`escrow_solvent`** — under ReserveWF the escrow is never negative: cumulative payouts
(`settled`) ≤ the escrowed line (`solvency`), so the escrow→holder settle can always pay. -/
theorem escrow_solvent {c : ChannelC} (h : c.ReserveWF) : 0 ≤ c.escrow := by
  obtain ⟨hwf, he⟩ := h
  have hsol := solvency hwf
  omega

/-- One fullReserve channel step preserves ReserveWF (draws/repays touch neither escrow nor
`settled`; settle moves both in lockstep). -/
theorem stepC_preserves_ReserveWF (c : ChannelC) (op : SOp) (h : c.ReserveWF) :
    (stepC .fullReserve c op).ReserveWF := by
  obtain ⟨hwf, he⟩ := h
  cases op with
  | draw d a =>
      show (((drawS c.s d a).map c.withS).getD c).ReserveWF
      cases hd : drawS c.s d a with
      | some s' =>
          simp only [Option.map_some, Option.getD_some]
          refine ⟨drawS_preserves_WF hwf hd, ?_⟩
          obtain ⟨tl', htl', rfl⟩ := drawS_spec hd
          obtain ⟨-, -, rfl⟩ := draw_spec htl'
          exact he
      | none => exact ⟨hwf, he⟩
  | repay a =>
      show (((repayS c.s a).map c.withS).getD c).ReserveWF
      cases hr : repayS c.s a with
      | some s' =>
          simp only [Option.map_some, Option.getD_some]
          refine ⟨repayS_preserves_WF hwf hr, ?_⟩
          obtain ⟨-, tl', htl', rfl⟩ := repayS_spec hr
          obtain ⟨-, rfl⟩ := repay_spec htl'
          exact he
      | none => exact ⟨hwf, he⟩
  | settle p =>
      show ((settleC .fullReserve c p).getD c).ReserveWF
      cases hq : settleC .fullReserve c p with
      | some c' =>
          simp only [Option.getD_some]
          simp only [settleC] at hq
          cases hs : settleS c.s p with
          | none => rw [hs] at hq; exact absurd hq (by simp)
          | some s' =>
              rw [hs] at hq
              simp only [Option.map_some, Option.some.injEq] at hq
              subst hq
              refine ⟨settleS_preserves_WF hwf hs, ?_⟩
              obtain ⟨hg, rfl⟩ := settleS_spec hs
              show c.escrow - (p : Int)
                  = (c.s.tl.ceiling : Int) - ((c.s.settled + p : Nat) : Int)
              omega
      | none => simp only [Option.getD_none]; exact ⟨hwf, he⟩

/-- **`reserveWF_forever`** — the escrow-tracks-the-unredeemed-line coupling rides every
adversarial fullReserve trajectory. -/
theorem reserveWF_forever (c₀ : ChannelC) (hinit : c₀.ReserveWF) (sched : SSched) :
    ∀ n, (trajC .fullReserve c₀ sched n).ReserveWF := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih => exact stepC_preserves_ReserveWF (trajC .fullReserve c₀ sched k) (sched k) ih

/-- **`escrow_solvent_forever` — SOLVENCY, the deployed form.** The escrow column is never
negative at any reachable state: payouts ≤ the escrowed line, along every adversarial schedule
of draws, repays, and settle epochs. -/
theorem escrow_solvent_forever (c₀ : ChannelC) (hinit : c₀.ReserveWF) (sched : SSched) :
    ∀ n, 0 ≤ (trajC .fullReserve c₀ sched n).escrow :=
  fun n => escrow_solvent (reserveWF_forever c₀ hinit sched n)

/-! ## §13 — It RUNS: non-vacuity for the settled model, both polarities. -/

/-- Settled demo: line 100. -/
def sdemo₀ : SLine := SLine.init 100

#guard decide sdemo₀.WF

/-- Draw 30 (digest 7). -/
def sdemo₁ : SLine := (drawS sdemo₀ 7 30).getD sdemo₀

#guard sdemo₁.tl.drawn == 30
#guard sdemo₁.settled == 0

/-- Settle 20 of the 30 outstanding (the epoch close redeems the net position). -/
def sdemo₂ : SLine := (settleS sdemo₁ 20).getD sdemo₁

#guard sdemo₂.settled == 20
-- The deployed settle does NOT zero drawn (the §5b settleAll shape is the OTHER axis point):
#guard sdemo₂.tl.drawn == 30
#guard sdemo₂.outstanding == 10
#guard decide sdemo₂.WF
-- POSITIVE polarity: a repay within the outstanding admits (and the boundary is tight).
#guard (repayS sdemo₂ 10).isSome
-- NEGATIVE polarity (THE SETTLED FLOOR): 11 ≤ drawn (the §2 gate would admit!) but beyond
-- the outstanding 10 → REFUSED. Settled credit cannot be repaid back.
#guard (repayS sdemo₂ 11).isNone
#guard (repay sdemo₂.tl 11).isSome
-- NEGATIVE polarity: over-settle refused; the boundary settle admits.
#guard (settleS sdemo₂ 11).isNone
#guard (settleS sdemo₂ 10).isSome
-- The digest burned before the settle epoch is STILL burned after it (forever carrier)…
#guard (drawS sdemo₂ 7 1).isNone
-- …and fresh draws keep working across the epoch (remaining = 100 − 30 = 70, tight).
#guard (drawS sdemo₂ 8 70).isSome
#guard (drawS sdemo₂ 8 71).isNone
-- The epoch-slice weld: the rebuilt slice (ceiling 80, spent 10) agrees with the cell.
#guard sdemo₂.epochSlice.remaining == 70
#guard sdemo₂.tl.remaining == 70

/-- fullReserve channel demo — the node e2e numbers (`settle_applies_net_position…`):
line 100 escrowed at open, draw 30, repay 10, settle the net 20. -/
def rdemo₀ : ChannelC := ChannelC.openReserve 100 500 500

#guard rdemo₀.escrow == 100
#guard rdemo₀.issuerHard == 400
#guard decide rdemo₀.ReserveWF
#guard rdemo₀.hardTotal == 1000

/-- Draw 30 (digest 1), repay 10 → net position 20. -/
def rdemo₁ : ChannelC := stepC .fullReserve (stepC .fullReserve rdemo₀ (.draw 1 30)) (.repay 10)

#guard rdemo₁.s.tl.drawn == 20
#guard rdemo₁.s.outstanding == 20
#guard rdemo₁.escrow == 100   -- draws/repays move NO hard value

/-- The epoch settle: escrow pays the holder the net 20, `settled` marches. -/
def rdemo₂ : ChannelC := stepC .fullReserve rdemo₁ (.settle 20)

#guard rdemo₂.s.settled == 20
#guard rdemo₂.s.tl.drawn == 20
#guard rdemo₂.escrow == 80
#guard rdemo₂.holderHard == 520
-- CONSERVATION: the hard column is exactly what it was at open.
#guard rdemo₂.hardTotal == rdemo₀.hardTotal
-- SOLVENCY coupling: escrow = line − settled, and ReserveWF rides.
#guard decide rdemo₂.ReserveWF
-- NEGATIVE polarity: settled credit cannot be repaid back (outstanding 0; drawn 20).
#guard (repayS rdemo₂.s 1).isNone
#guard (settleS rdemo₂.s 1).isNone
-- ReserveWF non-vacuity, negative polarity: a drained escrow violates the coupling.
#guard !(decide ({ rdemo₂ with escrow := 0 } : ChannelC).ReserveWF)

/-- pureCredit demo — §5b recovered on the axis: drawn 30 (the §7 `demo₁`), settle 30. -/
def pdemo₀ : ChannelC :=
  { s := { tl := demo₁, settled := 0 }, escrow := 0, issuerHard := 500, holderHard := 500 }

/-- The pure-credit settle: holder pays the issuer hard; the credit legs unwind. -/
def pdemo₁ : ChannelC := (settleC .pureCredit pdemo₀ 30).getD pdemo₀

#guard pdemo₁.s.tl.drawn == 0
#guard pdemo₁.escrow == 0
-- The same numbers as §7's `demoCh' = settleAll demoCh`: the axis point IS settlePay.
#guard pdemo₁.issuerHard == demoCh'.issuerHard
#guard pdemo₁.holderHard == demoCh'.holderHard
#guard pdemo₁.hardTotal == pdemo₀.hardTotal
-- POSITIVE/NEGATIVE polarity at the pureCredit point:
#guard (settleC .pureCredit pdemo₀ 30).isSome
#guard (settleC .pureCredit pdemo₀ 31).isNone

/-! ## §14 — Axiom-hygiene tripwires for §9–§12. -/

#assert_axioms drawS_spec
#assert_axioms repayS_spec
#assert_axioms settleS_spec
#assert_axioms init_SWF
#assert_axioms settle_monotone
#assert_axioms settleS_tl_fixed
#assert_axioms repay_below_settled_refused
#assert_axioms over_settle_refused
#assert_axioms repayS_fires_iff
#assert_axioms settleS_fires_iff
#assert_axioms drawS_preserves_WF
#assert_axioms repayS_preserves_WF
#assert_axioms settleS_preserves_WF
#assert_axioms stepS_preserves_WF
#assert_axioms sline_WF_forever
#assert_axioms settle_le_drawn_forever
#assert_axioms solvency
#assert_axioms solvency_forever
#assert_axioms sline_within_line_forever
#assert_axioms sline_conserved_forever
#assert_axioms no_double_draw_forever_across_settles
#assert_axioms stepS_settled_mono
#assert_axioms settled_monotone_forever
#assert_axioms stepS_draws_mono
#assert_axioms digest_burned_forever
#assert_axioms draw_replay_refused_across_epochs
#assert_axioms stepS_ceiling_fixed
#assert_axioms sline_ceiling_immutable_forever
#assert_axioms epochSlice_remaining
#assert_axioms drawS_fires_iff_epoch_tryDebit
#assert_axioms drawS_tracks_epoch_tryDebit
#assert_axioms ofView_WF
#assert_axioms derived_view_faithful
#assert_axioms view_determines_line
#assert_axioms sline_derived_view_faithful
#assert_axioms settleC_conserves_hard
#assert_axioms settleC_fullReserve_spec
#assert_axioms settleReserve_conserves_hard
#assert_axioms settleReserve_conserves_pair
#assert_axioms settleC_pureCredit_agrees_settlePay
#assert_axioms settleC_pureCredit_total
#assert_axioms stepC_hard_fixed
#assert_axioms hard_conserved_forever
#assert_axioms openReserve_is_a_move
#assert_axioms openReserve_ReserveWF
#assert_axioms escrow_solvent
#assert_axioms stepC_preserves_ReserveWF
#assert_axioms reserveWF_forever
#assert_axioms escrow_solvent_forever

end Dregg2.Apps.Trustline
