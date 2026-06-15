/-
# Dregg2.Apps.HostingLease — paying coin to be hosted is a VERIFIED VALUE TURN, and a lapsed fee
EVICTS — the deos app-hosting economy as ONE cell program.

`docs/PG-DREGG-ON-SEL4-DEOS-SPINE.md` makes the persist-PD the durable "postgres" of the seL4 deos OS:
an app is a CELL with durable hosted state in the persist-PD, and (the economy this file models) hosting
that app COSTS COIN — per hosting period the app pays a fee to the host cell. That payment is a real
value move (`turn/src/action.rs:819` `Effect::Transfer`, conservative), committed as a verified turn
through the durable spine. When the fee LAPSES (the app's prepaid balance cannot cover the period's
fee), the host EVICTS the app — its durable hosting is dropped, fail-closed. The Rust realization runs
green over real `redb` durability (`sel4/persist-hosttest/src/hosting.rs`); THIS file is the proof that
the lease's gate cannot be amplified and that the eviction is FORCED when the budget lapses.

## The lease — a cap with a TIME + BUDGET caveat over the durable slot

The brief names it exactly: a hosting lease is *a capability to occupy a durable hosting slot, bounded
by a budget (the prepaid balance) and a time window (the paid-through period)*. In the kernel's predicate
language (`Exec/Program.lean`) that is a `RecordProgram` whose `charge` gate is a conjunction of four
caveats — each a `StateConstraint`, each a theorem in BOTH polarities (the honest charge COMMITS; each
adversarial charge is `admitsCtx = false`):

  * **provenance** (`senderInField hostF`) — only the HOST the slot records may charge the lease. A
    capability holder who is not the host cannot bill the app. (The lease is the host's right to collect,
    not anyone's.)
  * **the BUDGET caveat** (`balanceGe leaseFee`) — the app's prepaid sealed balance must COVER the
    period's fee. A charge against an app that cannot pay is UNSAT — which is exactly the eviction
    trigger: a lapsed app's charge does not commit, so the host evicts (the Rust `charge_period` takes
    the `Evicted` branch). This is the budget half of the lease cap.
  * **the FEE FLOOR** (`balanceDeltaGe (-leaseFee)`) — the host may not debit the app by MORE than the
    agreed fee in one period. The lease bounds the host's draw: a host that tries to drain the app past
    the fee is UNSAT (no over-charge). The lease caps the value that may move, in both directions.
  * **the TIME caveat** (`strictMono periodF`) — the billing period strictly advances. A replay of an
    already-paid period (double-billing) or a stalled plateau is UNSAT. This is the time window of the
    lease: each period is charged once, in order.

The conjunction is ONE predicate (all-or-nothing): a charge that fails ANY caveat does not commit, and a
charge that fails the BUDGET caveat is precisely the one the runtime turns into an eviction.

## Why this is not a toy

The naive "hosting bill" trusts the host to charge correctly and the app to have paid. Four real attacks,
each closed by a clause here:

  * **the impostor collector.** Anyone could try to bill the app and pocket the fee. `senderInField hostF`
    binds the charge to the recorded host (`impostor_charge_rejected`).
  * **the free rider.** An app with no balance keeps its hosting by simply not paying. `balanceGe leaseFee`
    makes a charge against an unfunded app UNSAT — so the host evicts (`lapsed_app_charge_rejected`); the
    app cannot ride for free.
  * **the over-charge / drain.** A compromised or greedy host bills the app to zero in one period.
    `balanceDeltaGe (-leaseFee)` floors the debit at the agreed fee (`over_charge_rejected`).
  * **the double-bill / replay.** The host re-bills an already-paid period. `strictMono periodF` rejects
    it (`replayed_period_rejected`).

And the honest charge — host-signed, app funded, exactly-fee debit, next period — COMMITS
(`honest_charge_admits`): the gate is non-vacuous, there is a real hosting charge the lease lets through.

## The lease state — its fields

  * `host`   — the host cell that may collect the fee (provenance binding);
  * `period` — the strictly-increasing billing-period counter (the time window, replay-safe);
  * the cell's SEALED balance — the prepaid value, carried in `TurnCtx.balance` / `.balanceBefore`
    (the BUDGET; covered-by ∧ floored-debit are the two budget caveats).

The fee `leaseFee` is the published lease parameter (a host could store it as a governed slot — the
`balanceDeltaLeField` field-valued shape `SubscriptionMetered.lean` uses; kept a literal here so the
budget/eviction teeth are crisp).

## Conservation / non-amplification carrier

The charge gate constrains the SEALED balance (the budget caveats) and writes only the `period`/`host`
metadata — it writes NO capability table, so a charge cannot mint or amplify authority (the constraint
language reads/constrains record fields + the kernel balance; it has no cap-table write). The substantive
non-amplification is the executor's (this is a `RecordProgram`, evaluated, never a cap mint). The value
CONSERVATION (the fee leaves the app and arrives at the host, Σ unchanged) is the Rust realization's
property, proved green over the durable ledger (`hosting.rs::value_conserved_across_a_full_hosting_run`);
here the LEASE caveats prove the per-cell budget discipline (coverage + floor) that makes that transfer
admissible at all.

## Honest scope

  * `balanceGe`/`balanceDeltaGe` are the BOUNDED / ordering pole (§8): a budget gate on a decrementable
    balance is i-confluent only under the single serializer (n=1). Named, not laundered — the same scope
    `Exec/Program.lean` carries for the balance atoms, and the same scope the durable persist-PD honours
    (the n=1 synchronous-commit single writer, `docs/FIRMAMENT.md` §3).
  * The sealed balance + its pre-image (`balanceBefore`) are the executor-held kernel balances at
    program-check time (Rust `old_balance`/`new_balance`); the §8 seam is the kernel balance carrier,
    not a record field. The budget arithmetic is proved here.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide` —
`decide` / `#guard` / `Exec.Program`-keystone reuse only. `lake build` green (LOCAL).
-/
import Dregg2.Exec.Program

namespace Dregg2.Apps.HostingLease

open Dregg2.Exec

/-! ## §0 — The lease's field names, parameters, and identities. -/

/-- The host cell that may collect the hosting fee (provenance binding). -/
abbrev hostF : FieldName := "host"
/-- The strictly-increasing billing-period counter (the time window). -/
abbrev periodF : FieldName := "period"

/-- The published per-period hosting fee. The app's prepaid balance must cover it (the BUDGET caveat),
and the host may debit at most it (the FEE FLOOR). Kept a literal so the eviction/over-charge teeth are
crisp; a host could store it as a governed slot (the `balanceDeltaLeField` field-valued shape). -/
abbrev leaseFee : Int := 10

/-- The recorded host's identity (only it may charge the lease). -/
abbrev hostPk : Int := 0x40
/-- An impostor's identity (holds a capability, but is not the host). -/
abbrev impostorPk : Int := 0x99

/-! ## §1 — THE CHARGE GATE as a `RecordProgram` (provenance ∧ budget ∧ fee-floor ∧ time).

The lease's charge program is a conjunction of four caveats, each a `StateConstraint`:

  * `senderInField hostF`      — **provenance**: the charge must be signed by the recorded host.
  * `balanceGe leaseFee`       — **the BUDGET caveat**: the app's prepaid balance must cover the fee.
    A charge against an unfunded app is UNSAT ⇒ the host evicts (the eviction trigger).
  * `balanceDeltaGe (−leaseFee)` — **the FEE FLOOR**: the per-period debit may not exceed the fee
    (`Δbalance ≥ −leaseFee`). The host cannot drain the app past the agreed fee.
  * `strictMono periodF`       — **the TIME caveat**: the billing period strictly advances (no replay /
    no double-bill).

The conjunction is ONE predicate (all-or-nothing): a charge that fails the BUDGET caveat is exactly the
one the runtime turns into an eviction; any other failure refuses the charge outright. -/
def chargeConstraints : List StateConstraint :=
  [ .simple (.senderInField hostF)            -- provenance: only the host charges
  , .simple (.balanceGe leaseFee)             -- BUDGET: the app's balance covers the fee
  , .simple (.balanceDeltaGe (-leaseFee))     -- FEE FLOOR: debit ≤ the agreed fee
  , .simple (.strictMono periodF) ]           -- TIME: the period strictly advances

/-- **The hosting-lease charge program** — the per-period charge policy as ONE coalgebra structure-map.
The lease cap: a TIME (period) + BUDGET (balance) caveat over the durable hosting slot. -/
def leaseProgram : RecordProgram := .predicate chargeConstraints

/-! ## §2 — Extraction plumbing (the `SubscriptionMetered` pattern). -/

/-- Every constraint binds on an admitted charge (`admitsCtx` on `.predicate` IS the conjunction). -/
private theorem admitted_mem {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : leaseProgram.admitsCtx ctx m o n = true)
    {c : StateConstraint} (hc : c ∈ chargeConstraints) :
    evalConstraintCtx ctx c o n = true := by
  have hall : chargeConstraints.all (fun c => evalConstraintCtx ctx c o n) = true := h
  exact List.all_eq_true.mp hall c hc

/-- A charge that admits drives `admitsCtx = true` to `true` for the extraction `by_contra`. -/
private theorem admits_of_not_false {ctx : TurnCtx} {m : Nat} {o n : Value}
    (hc : ¬ leaseProgram.admitsCtx ctx m o n = false) :
    leaseProgram.admitsCtx ctx m o n = true := by
  cases h : leaseProgram.admitsCtx ctx m o n with
  | true => rfl
  | false => exact absurd h hc

/-! ## §3 — THE TEETH on the charge policy (both polarities, all PROVED). -/

/-- **① IMPOSTOR TOOTH — a charge not signed by the recorded host is UNSAT.** Any charge whose sender is
NOT the host the slot records is rejected: `admitsCtx = false`. The lease is the host's right to collect —
a capability holder who is not the host cannot bill the app. -/
theorem impostor_charge_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (recordedHost : Int)
    (hhost : n.scalar hostF = some recordedHost)
    (himpostor : ctx.sender ≠ some recordedHost) :
    leaseProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hprov := admitted_mem hne (c := .simple (.senderInField hostF)) (.head _)
  have hsend : evalSimpleCtx ctx (.senderInField hostF) o n = true := by
    simpa [evalConstraintCtx] using hprov
  obtain ⟨s, hs, hv⟩ := (evalSimpleCtx_senderInField_iff ctx hostF o n).mp hsend
  rw [hhost] at hv; injection hv with hv; subst hv; exact himpostor hs

/-- **② FREE-RIDER / LAPSED-FEE TOOTH — a charge against an app that cannot cover the fee is UNSAT.** A
charge whose post-state sealed balance is BELOW the lease fee is rejected: `admitsCtx = false`. This is
the EVICTION TRIGGER: a lapsed app's charge does not commit, so the host evicts it (the Rust
`charge_period` takes the `Evicted` branch, dropping the durable hosting, fail-closed). An app cannot keep
its hosting by not paying. -/
theorem lapsed_app_charge_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (bal : Int)
    (hbal : ctx.balance = some bal)
    (hlapsed : bal < leaseFee) :
    leaseProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hcov := admitted_mem hne (c := .simple (.balanceGe leaseFee)) (.tail _ (.head _))
  have hge : evalSimpleCtx ctx (.balanceGe leaseFee) o n = true := by
    simpa [evalConstraintCtx] using hcov
  obtain ⟨b, hb, hle⟩ := (evalSimpleCtx_balanceGe_iff ctx leaseFee o n).mp hge
  rw [hbal] at hb; injection hb with hb; subst hb; omega

/-- **③ OVER-CHARGE TOOTH — a charge debiting more than the lease fee is UNSAT.** A charge whose per-period
sealed-balance change is MORE NEGATIVE than the fee (`Δbalance < −leaseFee`, i.e. the host draws more than
the agreed fee) is rejected: `admitsCtx = false`. The lease caps the host's draw — a greedy/compromised
host cannot drain the app past the fee in one period. -/
theorem over_charge_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (before after : Int)
    (hbefore : ctx.balanceBefore = some before)
    (hafter : ctx.balance = some after)
    (hdrain : after - before < -leaseFee) :
    leaseProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hfloor := admitted_mem hne (c := .simple (.balanceDeltaGe (-leaseFee)))
    (.tail _ (.tail _ (.head _)))
  have hge : evalSimpleCtx ctx (.balanceDeltaGe (-leaseFee)) o n = true := by
    simpa [evalConstraintCtx] using hfloor
  obtain ⟨a, b, ha, hb, hle⟩ := (evalSimpleCtx_balanceDeltaGe_iff ctx (-leaseFee) o n).mp hge
  rw [hbefore] at ha; injection ha with ha; subst ha
  rw [hafter] at hb; injection hb with hb; subst hb
  omega

/-- **④ REPLAY / DOUBLE-BILL TOOTH — a charge that does not advance the period is UNSAT.** A charge whose
new period is NOT strictly greater than the old (a replay of an already-paid period, or a stalled plateau)
is rejected: `admitsCtx = false`. The time window of the lease: each period is charged once, in order. -/
theorem replayed_period_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (oldP newP : Int)
    (hold : o.scalar periodF = some oldP)
    (hnew : n.scalar periodF = some newP)
    (hreplay : ¬ oldP < newP) :
    leaseProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hmono := admitted_mem hne (c := .simple (.strictMono periodF))
    (.tail _ (.tail _ (.tail _ (.head _))))
  have hsm : evalSimpleCtx ctx (.strictMono periodF) o n = true := by
    simpa [evalConstraintCtx] using hmono
  rw [show evalSimpleCtx ctx (.strictMono periodF) o n = evalSimple (.strictMono periodF) o n from rfl]
    at hsm
  obtain ⟨a, b, ha, hb, hlt⟩ := (evalSimple_strictMono_iff periodF o n).mp hsm
  rw [hold] at ha; injection ha with ha; subst ha
  rw [hnew] at hb; injection hb with hb; subst hb
  exact hreplay hlt

/-- **⑤ THE HONEST HOSTING CHARGE COMMITS (the gate is not constant-false).** A charge signed by the
recorded host, against an app whose balance covers the fee, debiting exactly the fee, advancing the
period, ADMITS. The conjunction of the four caveats is non-vacuous: there is a real hosting charge the
lease lets through — the paid period the Rust `charge_period` commits as a conserving Transfer. -/
theorem honest_charge_admits (ctx : TurnCtx) (m : Nat) (o n : Value)
    (oldP newP before after : Int)
    (hsender : ctx.sender = some hostPk)
    (hhost : n.scalar hostF = some hostPk)
    (holdP : o.scalar periodF = some oldP) (hnewP : n.scalar periodF = some newP) (hadv : oldP < newP)
    (hbefore : ctx.balanceBefore = some before) (hafter : ctx.balance = some after)
    (hcover : leaseFee ≤ after)                 -- the app still covers the fee after the debit
    (hfloor : -leaseFee ≤ after - before) :     -- the debit did not exceed the fee
    leaseProgram.admitsCtx ctx m o n = true := by
  have c1 : evalConstraintCtx ctx (.simple (.senderInField hostF)) o n = true := by
    show evalSimpleCtx ctx (.senderInField hostF) o n = true
    exact (evalSimpleCtx_senderInField_iff ctx hostF o n).mpr ⟨hostPk, hsender, hhost⟩
  have c2 : evalConstraintCtx ctx (.simple (.balanceGe leaseFee)) o n = true := by
    show evalSimpleCtx ctx (.balanceGe leaseFee) o n = true
    exact (evalSimpleCtx_balanceGe_iff ctx leaseFee o n).mpr ⟨after, hafter, hcover⟩
  have c3 : evalConstraintCtx ctx (.simple (.balanceDeltaGe (-leaseFee))) o n = true := by
    show evalSimpleCtx ctx (.balanceDeltaGe (-leaseFee)) o n = true
    exact (evalSimpleCtx_balanceDeltaGe_iff ctx (-leaseFee) o n).mpr
      ⟨before, after, hbefore, hafter, hfloor⟩
  have c4 : evalConstraintCtx ctx (.simple (.strictMono periodF)) o n = true := by
    show evalSimpleCtx ctx (.strictMono periodF) o n = true
    rw [show evalSimpleCtx ctx (.strictMono periodF) o n = evalSimple (.strictMono periodF) o n from rfl]
    exact (evalSimple_strictMono_iff periodF o n).mpr ⟨oldP, newP, holdP, hnewP, hadv⟩
  show chargeConstraints.all (fun c => evalConstraintCtx ctx c o n) = true
  simp only [chargeConstraints, List.all_cons, List.all_nil, c1, c2, c3, c4, Bool.and_true]

/-! ## §4 — NON-VACUITY TEETH (`#guard`): the lease policy BITES on the concrete fee, both polarities. -/

section Witnesses

/-- A faithful hosting charge context: the host signs, the app's balance is 90 (was 100, a −10 debit =
exactly the fee), period advances. -/
def chargeCtx : TurnCtx :=
  { sender := some hostPk, balance := some 90, balanceBefore := some 100 }
def slotNew : Value :=
  .record [(hostF, .int hostPk), (periodF, .int 6)]
def slotOld : Value :=
  .record [(hostF, .int hostPk), (periodF, .int 5)]

-- ① COMMIT: a faithful hosting charge ADMITS (host-signed, period 5→6, −10 debit = the fee, balance 90 ≥ fee).
#guard leaseProgram.admitsCtx chargeCtx 0 slotOld slotNew

-- ① REFUSE (impostor): the SAME charge but signed by an impostor (not the host). REJECTED.
#guard leaseProgram.admitsCtx
  { chargeCtx with sender := some impostorPk } 0 slotOld slotNew == false

-- ① REFUSE (no sender): unsigned charge. REJECTED (fail-closed provenance).
#guard leaseProgram.admitsCtx
  { chargeCtx with sender := none } 0 slotOld slotNew == false

-- ② REFUSE (lapsed fee → EVICT): the app's balance is 5 (was 15), below the fee 10. The charge is UNSAT,
-- so the host evicts (the runtime's Evicted branch). REJECTED.
#guard leaseProgram.admitsCtx
  { sender := some hostPk, balance := some 5, balanceBefore := some 15 } 0 slotOld slotNew == false

-- ② REFUSE (zero balance → EVICT): an app with 0 balance cannot pay; the charge is UNSAT ⇒ eviction.
#guard leaseProgram.admitsCtx
  { sender := some hostPk, balance := some 0, balanceBefore := some 0 } 0 slotOld slotNew == false

-- ③ REFUSE (over-charge): balance 80 (was 100, a −20 debit) — twice the fee. The host drew too much. REJECTED.
#guard leaseProgram.admitsCtx
  { sender := some hostPk, balance := some 80, balanceBefore := some 100 } 0 slotOld slotNew == false

-- ③ REFUSE (absent balance endpoint): no pre-balance ⇒ the fee floor fails closed. REJECTED.
#guard leaseProgram.admitsCtx
  { chargeCtx with balanceBefore := none } 0 slotOld slotNew == false

-- ④ REFUSE (replay / double-bill): the new period (5) equals the old (5) — not strictly increasing. REJECTED.
#guard leaseProgram.admitsCtx chargeCtx 0 slotOld
  (.record [(hostF, .int hostPk), (periodF, .int 5)]) == false

-- ④ REFUSE (skip-back): the new period (4) is BELOW the old (5). REJECTED.
#guard leaseProgram.admitsCtx chargeCtx 0 slotOld
  (.record [(hostF, .int hostPk), (periodF, .int 4)]) == false

-- The BUDGET caveat isolated: balance 10 (exactly the fee) ADMITS the coverage clause; balance 9 REJECTS.
#guard evalSimpleCtx { balance := some 10 } (.balanceGe leaseFee) (.record []) (.record [])
#guard evalSimpleCtx { balance := some 9 } (.balanceGe leaseFee) (.record []) (.record []) == false

-- The FEE FLOOR isolated: a −10 debit (exactly the fee) ADMITS; a −11 debit (over the fee) REJECTS.
#guard evalSimpleCtx { balance := some 90, balanceBefore := some 100 } (.balanceDeltaGe (-leaseFee))
  (.record []) (.record [])
#guard evalSimpleCtx { balance := some 89, balanceBefore := some 100 } (.balanceDeltaGe (-leaseFee))
  (.record []) (.record []) == false

end Witnesses

/-! ## §5 — Axiom hygiene. Every load-bearing charge theorem checked kernel-clean. -/

#assert_all_clean [
  impostor_charge_rejected,
  lapsed_app_charge_rejected,
  over_charge_rejected,
  replayed_period_rejected,
  honest_charge_admits
]

end Dregg2.Apps.HostingLease
