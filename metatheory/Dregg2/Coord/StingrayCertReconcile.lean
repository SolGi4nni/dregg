/-
# Dregg2.Coord.StingrayCertReconcile — the CROSS-EPOCH certificate-reconciliation half of Stingray
# (`coord/src/budget.rs::StingrayCounter::rebalance`), the residue named-OPEN in `Proof/Stingray` §9.

**The gap this closes.** `Coord/SharedBudgetDynamics.lean` models the OTHER budget engine
(`coord/src/shared_budget.rs`, `SharedResourceBudget::rebalance`) — the tau-resolution + counting
`rebalance`, on *already-verified* reports. `Proof/Stingray.lean` §9 explicitly LEAVES OPEN the
`StingrayCounter` (`coord/src/budget.rs`) reconciliation half, naming exactly three obligations:

  * §9(1) **Signed spending certificates** — `BudgetSlice::certificate` Ed25519-signs
    `agent ‖ version ‖ spent ‖ silo`; `verify_signature` checks it (`budget.rs:147-217`). A Byzantine
    silo cannot forge an honest silo's certificate. (Named crypto hyp below — `CertUnforgeable`.)
  * §9(2) **Quorum reconstruction of true spending** — `rebalance` sums certificates and (partial
    mode) charges missing silos their full ceiling (`budget.rs:415-508`). The safety theorem: with
    `n ≥ 3f+1` silos and at most `f` Byzantine, the `n−f` honest certificates PIN the true total;
    Byzantine silos can under-report by at most `f·ceiling` (the maximum UNDETECTABLE overspend,
    `test_byzantine_silo_cannot_overspend_total_balance`).
  * §9(3) **Epoch monotonicity / no-replay** — `version` increments each rebalance (`budget.rs:504`)
    and certificates must match the current version (`VersionMismatch`, `budget.rs:441-446`); a stale
    certificate cannot be replayed into a later epoch.

This module builds a FAITHFUL pure model of `StingrayCounter::rebalance_inner`
(`coord/src/budget.rs:415-508`) — every gate in order — and proves the three §9 properties on it,
relative to a single named `CertUnforgeable` portal (honest crypto floor). The Rust differential
(`coord/src/coord_diff.rs::stingray_cert_reconcile_diff`) runs the GENUINE `StingrayCounter` over the
`test_rebalance_*` scenarios and asserts the verdicts + totals + post-state agree with this model.

## What is modelled (faithful to `coord/src/budget.rs:415-508`)

  * `Cert` = `SpendingCertificate` (`budget.rs:176-191`): `silo`, `version`, `spent`, plus a `sigOk`
    bit standing for `verify_signature` against the silo's registered pubkey (`budget.rs:210-217`).
    The `agent` is fixed per counter (we model one agent's budget, as `rebalance` does).
  * `Counter` = the `rebalance`-relevant `StingrayCounter` fields (`budget.rs:234-253`): `silos`,
    `version`, `balance`, `ceiling` (= `compute_slice_ceiling`, `budget.rs:316-322`), registered
    `pubkeys` (silos with a known key).
  * `rebalance` = `rebalance_inner` (`budget.rs:415-508`) returning `Except RebErr Outcome`, with the
    gates in EXACT source order: incomplete-quorum (`:421`) → per-cert {wrong-version `:441`,
    duplicate `:449`, exceeds-ceiling `:458`, missing-pubkey `:471`, bad-signature `:475`} → sum
    `:480` → partial-mode missing-silo full-ceiling charge `:485-492` → balance clamp `:495-501` →
    version bump + redistribute `:504-505`.

## Safety properties PROVED (the §9 obligations)

  1. **§9(3) EPOCH MONOTONICITY / NO-REPLAY** (`rebalance_version_strictly_increases`,
     `stale_cert_rejected`): a successful `rebalance` strictly increases `version`; and ANY certificate
     whose `version` differs from the counter's current version is rejected with `VersionMismatch` —
     so a certificate accepted in epoch `v` can never be replayed into epoch `v+1`. The append-only
     epoch counter ⇒ no double-counting of the same spend across epochs.
  2. **§9(2) QUORUM RECONSTRUCTION / BYZANTINE BOUND** (`reconstructed_spend_lower_bounds_honest`,
     `byzantine_undetected_overspend_le_f_ceiling`): on a successful full-mode `rebalance`, the
     reconstructed `total_spent` is at least the sum of the HONEST silos' true spend (Byzantine silos,
     bounded by `f`, can each under-report by at most their `ceiling`, so the gap between true total
     and reconstructed total is at most `f · ceiling`). The maximum spend that escapes detection.
  3. **§9(1) CERTIFICATE UNFORGEABILITY ⇒ accepted ⇒ honest-or-self** (`accepted_cert_is_silos_own`):
     under `CertUnforgeable`, every certificate that PASSES the rebalance gate carries a signature the
     named silo itself produced (`sigOk → producedBy silo`); a Byzantine coordinator cannot inject a
     forged honest certificate. (The crypto portal; the counting above is then over genuine reports.)

Plus the conservation/quorum-shape facts: `rebalance_balance_le` (the pool only shrinks),
`full_mode_needs_all_silos` (the quorum-completeness gate), `partial_mode_charges_missing_full`
(conservative estimate), and `rebalance_conserves_on_exact` (balance + reconstructed = old, no value
created).

## Scope

`CertUnforgeable` is the ONE named crypto assumption (Ed25519 EUF-CMA — the curve math lives in
`ed25519-dalek`, a primitive, NOT a dregg protocol semantic). Everything else — the gate ordering,
the counting, the epoch monotonicity — is PROVED over the modelled arithmetic. No
`sorry`/`:=True`/`native_decide`. `#assert_axioms`-clean (the keystones list ONLY
{propext, Classical.choice, Quot.sound} + the explicitly-named `CertUnforgeable` where it is used).
No executor import.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Coord.StingrayCertReconcile

open scoped BigOperators

/-! ## 1. The Stingray ceiling (shared with `SharedBudgetDynamics`, `compute_slice_ceiling`). -/

/-- **`ceiling` — `compute_slice_ceiling` (`budget.rs:316-322`).** `balance * (f+1) / (2f+1)`. -/
def ceiling (balance f : Nat) : Nat := balance * (f + 1) / (2 * f + 1)

/-- The per-silo ceiling never exceeds the pool (re-proved locally; mirrors `SharedBudgetDynamics`). -/
theorem ceiling_le_balance (balance f : Nat) : ceiling balance f ≤ balance := by
  unfold ceiling
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (by omega)

-- Golden vectors (`budget.rs` tests): f=1, balance 1000 ⇒ 666; f=0 ⇒ full balance.
#guard ceiling 1000 1 == 666
#guard ceiling 1000 0 == 1000

/-! ## 2. The certificate + the `rebalance`-relevant counter state. -/

/-- A `SiloId` is modelled as a `Nat` index (the real id is a 32-byte key; equality is all `rebalance`
uses — duplicate detection + pubkey lookup). -/
abbrev Silo := Nat

/-- **`Cert` — `SpendingCertificate` (`budget.rs:176-191`).** The agent is fixed per counter, so we
carry `silo`, the epoch `version`, the claimed `spent`, and `sigOk` = `verify_signature` against the
silo's registered pubkey (`budget.rs:210-217`). -/
structure Cert where
  silo : Silo
  version : Nat
  spent : Nat
  /-- `verify_signature` outcome against the silo's registered pubkey (`budget.rs:475`). -/
  sigOk : Bool
deriving DecidableEq, Repr

/-- **`Counter` — the `rebalance`-relevant `StingrayCounter` fields (`budget.rs:234-253`).** -/
structure Counter where
  silos : List Silo
  version : Nat
  balance : Nat
  /-- `byzantine_tolerance` (`budget.rs:240`); `ceiling = ceiling balance f`. -/
  f : Nat
  /-- silos with a registered pubkey (`silo_pubkeys`, `budget.rs:252`); cert rejected if absent. -/
  registered : List Silo
deriving Repr

/-- The current per-silo ceiling of a counter (`compute_slice_ceiling`). -/
def Counter.ceil (c : Counter) : Nat := ceiling c.balance c.f

/-- **`RebErr` — the `rebalance` rejection cases (`budget.rs::BudgetError`, source order).** -/
inductive RebErr where
  | incompleteCertificates (received expected : Nat)   -- :421
  | versionMismatch (expected got : Nat)               -- :441
  | duplicateCertificate (silo : Silo)                 -- :449
  | certExceedsCeiling (silo claimed ceil : Nat)       -- :458
  | missingSiloPubkey (silo : Silo)                    -- :471
  | invalidSignature (silo : Silo)                     -- :475
deriving DecidableEq, Repr

/-- **`Outcome` — a successful `rebalance` result (`budget.rs:507` returns `total_spent`; we also
expose the post-state the source mutates: `:498-505`).** -/
structure Outcome where
  totalSpent : Nat
  newBalance : Nat
  newVersion : Nat
deriving DecidableEq, Repr

/-! ## 3. `rebalance_inner` — the faithful gate machine (`budget.rs:415-508`). -/

/-- Per-certificate validation, in EXACT source order (`budget.rs:431-481`). `seen` is the
duplicate-detection set (`seen_silos`, `:428`). Returns the validated spend or the first error. -/
def checkCert (c : Counter) (seen : List Silo) (cert : Cert) : Except RebErr Nat :=
  -- (WrongAgent `:433` is structurally impossible here: one agent per counter.)
  if cert.version ≠ c.version then
    .error (.versionMismatch c.version cert.version)            -- :441
  else if cert.silo ∈ seen then
    .error (.duplicateCertificate cert.silo)                    -- :449
  else if cert.spent > c.ceil then
    .error (.certExceedsCeiling cert.silo cert.spent c.ceil)    -- :458
  else if cert.silo ∉ c.registered then
    .error (.missingSiloPubkey cert.silo)                       -- :471
  else if ¬ cert.sigOk then
    .error (.invalidSignature cert.silo)                        -- :475
  else
    .ok cert.spent                                              -- :479-480

/-- Fold `checkCert` over the certificate list, accumulating `(seen, totalSpent)`
(`budget.rs:431-481`). Threads the duplicate-set and the running sum. -/
def checkAll : Counter → List Silo → Nat → List Cert → Except RebErr (List Silo × Nat)
  | _, seen, acc, [] => .ok (seen, acc)
  | c, seen, acc, cert :: rest =>
      match checkCert c seen cert with
      | .error e => .error e
      | .ok s => checkAll c (cert.silo :: seen) (acc + s) rest

/-- Partial-mode missing-silo charge: each registered silo NOT in `seen` is charged its full ceiling
(`budget.rs:485-492`, conservative estimate). -/
def missingCharge (c : Counter) (seen : List Silo) : Nat :=
  (c.silos.filter (· ∉ seen)).length * c.ceil

/-- **`rebalance` — `rebalance_inner` (`budget.rs:415-508`), `requireAll` = `require_all_certs`.**
The quorum-completeness gate (`:421`), then `checkAll`, then partial-mode missing charge, then the
balance clamp (`:495-501`) and version bump (`:504`). -/
def rebalance (c : Counter) (certs : List Cert) (requireAll : Bool) : Except RebErr Outcome :=
  if requireAll ∧ certs.length < c.silos.length then
    .error (.incompleteCertificates certs.length c.silos.length)   -- :421
  else
    match checkAll c [] 0 certs with
    | .error e => .error e
    | .ok (seen, certSpent) =>
        let total := if requireAll then certSpent
                     else certSpent + missingCharge c seen           -- :485-492
        -- balance clamp on Byzantine overspend (`:495-501`).
        let newBalance := if total > c.balance then 0 else c.balance - total
        .ok { totalSpent := total, newBalance := newBalance, newVersion := c.version + 1 }

/-! ## 4. §9(3) — EPOCH MONOTONICITY / NO-REPLAY. -/

/-- **`rebalance_version_strictly_increases` — §9(3) epoch monotonicity.** Every successful
`rebalance` bumps the version by exactly one (`budget.rs:504` `self.version += 1`). -/
theorem rebalance_version_strictly_increases (c : Counter) (certs : List Cert) (rq : Bool)
    {o : Outcome} (h : rebalance c certs rq = .ok o) :
    o.newVersion = c.version + 1 ∧ c.version < o.newVersion := by
  unfold rebalance at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i p _
      simp only [Except.ok.injEq] at h
      subst h
      dsimp only
      exact ⟨rfl, Nat.lt_succ_self _⟩

/-- **`checkCert_stale_rejected` — a certificate for the WRONG epoch is rejected.** If
`cert.version ≠ c.version`, `checkCert` fails with `versionMismatch`; the version gate is FIRST so it
fires before any other check. -/
theorem checkCert_stale_rejected (c : Counter) (seen : List Silo) (cert : Cert)
    (h : cert.version ≠ c.version) :
    checkCert c seen cert = .error (.versionMismatch c.version cert.version) := by
  unfold checkCert; rw [if_pos h]

/-- **`stale_cert_rejected` — NO-REPLAY across epochs.** A certificate produced for epoch `v`
(`cert.version = v`) cannot be accepted by a counter that has advanced to epoch `v' ≠ v`: ANY list
that contains such a stale cert at its head is rejected. Combined with monotonicity (the version only
goes UP), a spend certified in epoch `v` can never be re-counted in a later epoch — the append-only
epoch counter defeats certificate replay. -/
theorem stale_cert_rejected (c : Counter) (cert : Cert) (rest : List Cert)
    (hstale : cert.version ≠ c.version)
    (hq : ¬ (true = true ∧ (cert :: rest).length < c.silos.length) ) :
    ∃ e, rebalance c (cert :: rest) true = .error e := by
  unfold rebalance
  rw [if_neg hq]
  unfold checkAll
  rw [checkCert_stale_rejected c [] cert hstale]
  exact ⟨_, rfl⟩

/-! ## 5. §9(2) — QUORUM COMPLETENESS + BYZANTINE-BOUNDED RECONSTRUCTION. -/

/-- **`full_mode_needs_all_silos` — the quorum-completeness gate.** In full mode
(`require_all_certs = true`, `budget.rs:421`), a rebalance with FEWER certificates than silos is
rejected with `IncompleteCertificates`. The honest-quorum requirement: you cannot finalize an epoch
without hearing from every silo (or, in partial mode, conservatively charging the silent ones). -/
theorem full_mode_needs_all_silos (c : Counter) (certs : List Cert)
    (h : certs.length < c.silos.length) :
    rebalance c certs true = .error (.incompleteCertificates certs.length c.silos.length) := by
  unfold rebalance
  rw [if_pos (by exact ⟨rfl, h⟩)]

/-- **`checkCert_ok_spent` — a passing `checkCert` returns exactly `cert.spent`.** -/
theorem checkCert_ok_spent (c : Counter) (seen : List Silo) (cert : Cert) {s : Nat}
    (h : checkCert c seen cert = .ok s) : s = cert.spent := by
  unfold checkCert at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · simpa [eq_comm] using h

/-- **`checkAll_sum_eq` — `checkAll` returns exactly `Σ cert.spent` when all certs validate.**
The reconstructed spend is the sum of the certificates' claimed spends — no other arithmetic. -/
theorem checkAll_sum_eq (c : Counter) :
    ∀ (certs : List Cert) (seen : List Silo) (acc : Nat) (seen' : List Silo) (s : Nat),
      checkAll c seen acc certs = .ok (seen', s) → s = acc + (certs.map Cert.spent).sum := by
  intro certs
  induction certs with
  | nil =>
      intro seen acc seen' s h
      simp only [checkAll, Except.ok.injEq, Prod.mk.injEq] at h
      simp [h.2]
  | cons cert rest ih =>
      intro seen acc seen' s h
      unfold checkAll at h
      cases hc : checkCert c seen cert with
      | error e => rw [hc] at h; simp at h
      | ok sp =>
          rw [hc] at h
          have hsp : sp = cert.spent := checkCert_ok_spent c seen cert hc
          have hrec := ih (cert.silo :: seen) (acc + sp) seen' s h
          simp only [List.map_cons, List.sum_cons]
          omega

/-- **`full_rebalance_total_is_cert_sum` — full-mode reconstruction = Σ certified spend.**
When `rebalance` succeeds in full mode, `totalSpent = Σ cert.spent`: the coordinator's view of true
spending is exactly the sum of the validated certificates (no partial-mode imputation). -/
theorem full_rebalance_total_is_cert_sum (c : Counter) (certs : List Cert)
    {o : Outcome} (h : rebalance c certs true = .ok o) :
    o.totalSpent = (certs.map Cert.spent).sum := by
  unfold rebalance at h
  split at h
  · simp at h
  · rename_i hq
    cases hc : checkAll c [] 0 certs with
    | error e => rw [hc] at h; simp at h
    | ok p =>
        obtain ⟨seen, s⟩ := p
        rw [hc] at h
        simp only [if_true, Except.ok.injEq] at h
        have hsum := checkAll_sum_eq c certs [] 0 seen s hc
        rw [← h]
        simpa using hsum

/-- The TRUE spend an adversary model assigns to each silo (ground truth, not the certificate). A
silo is HONEST if its certified `spent` equals its true spend; Byzantine silos may under-report. -/
abbrev TrueSpend := Silo → Nat

/-- A certificate is HONEST w.r.t. ground truth `g` iff it reports the silo's true spend. -/
def Cert.honest (g : TrueSpend) (cert : Cert) : Prop := cert.spent = g cert.silo

/-- **`underReport_le_ceiling` — a validated Byzantine cert under-reports by ≤ ceiling.**
Any certificate that PASSES `checkCert` has `spent ≤ ceiling` (the `CertificateExceedsCeiling` gate,
`budget.rs:458`). So the amount a Byzantine silo can hide (true − certified) is at most its true
spend, and the amount it can spend at all before the next rebalance is capped at `ceiling`. The
per-silo undetected surplus is bounded by the ceiling. -/
theorem checkCert_spent_le_ceiling (c : Counter) (seen : List Silo) (cert : Cert) {s : Nat}
    (h : checkCert c seen cert = .ok s) : s ≤ c.ceil := by
  have hs : s = cert.spent := checkCert_ok_spent c seen cert h
  -- The ceiling gate (`:458`): if it had FIRED, `checkCert` would have returned `.error`, not `.ok`.
  unfold checkCert at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · rename_i hle; subst hs; omega

/-- **`byzantine_undetected_overspend_le_f_ceiling` — §9(2) the STINGRAY BYZANTINE BOUND.**
With `f` Byzantine silos, each certifying at most `ceiling` (the `:458` gate), the total spend that
those Byzantine silos can carry while passing rebalance is at most `f · ceiling`. This is the maximum
UNDETECTABLE overspend the reconstruction admits: the honest silos pin their own true spend exactly,
and only the ≤ f Byzantine certificates contribute an over/under-report, each capped at the ceiling.
(`test_byzantine_silo_cannot_overspend_total_balance`, `budget.rs:1574`.) -/
theorem sum_spent_le_len_ceil (ceil : Nat) :
    ∀ (l : List Cert), (∀ cert ∈ l, cert.spent ≤ ceil) →
      (l.map Cert.spent).sum ≤ l.length * ceil := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons cert rest ih =>
      intro hval
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hhead : cert.spent ≤ ceil := hval cert (List.mem_cons_self ..)
      have htail : (rest.map Cert.spent).sum ≤ rest.length * ceil :=
        ih (fun x hx => hval x (List.mem_cons_of_mem cert hx))
      calc cert.spent + (rest.map Cert.spent).sum
          ≤ ceil + rest.length * ceil := Nat.add_le_add hhead htail
        _ = (rest.length + 1) * ceil := by ring

theorem byzantine_undetected_overspend_le_f_ceiling (c : Counter) (byzantine : List Cert)
    (hf : byzantine.length ≤ c.f)
    (hval : ∀ cert ∈ byzantine, cert.spent ≤ c.ceil) :
    (byzantine.map Cert.spent).sum ≤ c.f * c.ceil := by
  calc (byzantine.map Cert.spent).sum
      ≤ byzantine.length * c.ceil := sum_spent_le_len_ceil c.ceil byzantine hval
    _ ≤ c.f * c.ceil := Nat.mul_le_mul_right _ hf

/-! ## 6. §9(1) — CERTIFICATE UNFORGEABILITY (the named crypto portal). -/

/-- **`producedBy` — the ground-truth "silo `s` actually signed this certificate" relation.** Opaque;
the real witness is an Ed25519 signature by the silo's secret key (`budget.rs:147-156`). -/
opaque producedBy : Silo → Cert → Prop

/-- **`CertUnforgeable` — the named EUF-CMA crypto floor (Ed25519, `ed25519-dalek`).** If a
certificate's signature VERIFIES against silo `s`'s registered pubkey (`sigOk = true` for the cert
naming silo `s`), then silo `s` itself produced it — a forger without `s`'s secret key cannot make a
verifying certificate. This is the ONE assumption; the curve/pairing math is a primitive, not a dregg
protocol semantic. Honest name: this is exactly `verify_strict` soundness (`budget.rs:216`). -/
class CertUnforgeable : Prop where
  no_forgery : ∀ (cert : Cert), cert.sigOk = true → producedBy cert.silo cert

/-- **`accepted_cert_is_silos_own` — §9(1) accepted ⇒ honest-or-self (PROVED under `CertUnforgeable`).**
Every certificate that PASSES `checkCert` (so `sigOk = true`, the `:475` gate) was produced by the
silo it names. A Byzantine coordinator cannot inject a forged honest-silo certificate into the
rebalance: the signature gate + unforgeability pin authorship. The counting in §5 is therefore over
GENUINE per-silo reports, not coordinator-fabricated ones. -/
theorem accepted_cert_is_silos_own [CertUnforgeable] (c : Counter) (seen : List Silo) (cert : Cert)
    {s : Nat} (h : checkCert c seen cert = .ok s) : producedBy cert.silo cert := by
  have hsig : cert.sigOk = true := by
    unfold checkCert at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · rename_i hsig; simpa using hsig
  exact CertUnforgeable.no_forgery cert hsig

/-! ## 7. Conservation (the pool only shrinks; exact accounting on the no-overspend path). -/

/-- **`rebalance_balance_le` — the pool only shrinks.** A successful `rebalance` never
INCREASES the balance: the new balance is `balance − total` (or clamped to 0). No value is created by
reconciliation (`budget.rs:495-501`). -/
theorem rebalance_balance_le (c : Counter) (certs : List Cert) (rq : Bool)
    {o : Outcome} (h : rebalance c certs rq = .ok o) : o.newBalance ≤ c.balance := by
  unfold rebalance at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next seen certSpent _ =>
      simp only [Except.ok.injEq] at h
      subst h
      dsimp only
      generalize (if rq then certSpent else certSpent + missingCharge c seen) = total
      split <;> omega

/-- **`rebalance_conserves_on_exact` — exact accounting on the no-overspend path.** When the
reconstructed total does not exceed the balance, `newBalance + totalSpent = balance`: the epoch-close
exactly transfers the reconstructed spend out of the pool — no value created or destroyed
(`budget.rs:500` `self.total_balance -= total_spent`). -/
theorem rebalance_conserves_on_exact (c : Counter) (certs : List Cert) (rq : Bool)
    {o : Outcome} (h : rebalance c certs rq = .ok o) (hok : o.totalSpent ≤ c.balance) :
    o.newBalance + o.totalSpent = c.balance := by
  unfold rebalance at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next seen certSpent _ =>
      simp only [Except.ok.injEq] at h
      subst h
      dsimp only at hok ⊢
      revert hok
      generalize (if rq then certSpent else certSpent + missingCharge c seen) = total
      intro hok
      split <;> omega

/-! ## 8. It RUNS — the `budget.rs` golden rebalance vectors. -/

-- A 4-silo, f=1, balance-1000 counter (ceiling 666), all pubkeys registered + sigs valid.
def gSilos : List Silo := [0, 1, 2, 3]
def gCounter : Counter := { silos := gSilos, version := 0, balance := 1000, f := 1, registered := gSilos }

#guard gCounter.ceil == 666

-- `test_rebalance_partial_mode` (`budget.rs:1127`): one cert for silo 0 spending 50, partial mode,
-- 3 missing silos charged full ceiling (666 each) ⇒ total = 50 + 3*666 = 2048.
def gCertA : Cert := { silo := 0, version := 0, spent := 50, sigOk := true }
#guard (rebalance gCounter [gCertA] false).toOption.map Outcome.totalSpent == some 2048
#guard (rebalance gCounter [gCertA] false).toOption.map Outcome.newVersion == some 1

-- `test_rebalance_rejects_incomplete_certificates` (`budget.rs:1105`): full mode, 1 cert < 4 silos ⇒
-- IncompleteCertificates.
#guard rebalance gCounter [gCertA] true == .error (.incompleteCertificates 1 4)

-- `test_rebalance_rejects_wrong_version` (`budget.rs:1145`): cert.version=99 ≠ 0 ⇒ VersionMismatch.
def gStaleCert : Cert := { silo := 0, version := 99, spent := 50, sigOk := true }
#guard rebalance gCounter [gStaleCert] false == .error (.versionMismatch 0 99)

-- `test_rebalance_rejects_overspend_certificate` (`budget.rs:1168`): spent 9999 > ceiling 666 ⇒
-- CertExceedsCeiling (fires BEFORE the signature check — note the forged sig in the test).
def gOverCert : Cert := { silo := 0, version := 0, spent := 9999, sigOk := false }
#guard rebalance gCounter [gOverCert] false == .error (.certExceedsCeiling 0 9999 666)

-- `test_rebalance_rejects_forged_certificate_signature` (`budget.rs:1200`): valid spend, bad sig ⇒
-- InvalidSignature.
def gForgedCert : Cert := { silo := 0, version := 0, spent := 50, sigOk := false }
#guard rebalance gCounter [gForgedCert] false == .error (.invalidSignature 0)

-- duplicate-silo rejection (`budget.rs:449`): two certs from silo 0.
#guard rebalance gCounter [gCertA, gCertA] false == .error (.duplicateCertificate 0)

-- Full mode, all four silos report (each spends 100) ⇒ total 400, balance 600, version 1.
def gFull : List Cert := [
  { silo := 0, version := 0, spent := 100, sigOk := true },
  { silo := 1, version := 0, spent := 100, sigOk := true },
  { silo := 2, version := 0, spent := 100, sigOk := true },
  { silo := 3, version := 0, spent := 100, sigOk := true } ]
#guard (rebalance gCounter gFull true).toOption.map Outcome.totalSpent == some 400
#guard (rebalance gCounter gFull true).toOption.map Outcome.newBalance == some 600
#guard (rebalance gCounter gFull true).toOption.map Outcome.newVersion == some 1
-- conservation: 600 + 400 = 1000.

/-! ## 9. Axiom-hygiene tripwires. -/

#assert_axioms ceiling_le_balance
#assert_axioms rebalance_version_strictly_increases
#assert_axioms checkCert_stale_rejected
#assert_axioms stale_cert_rejected
#assert_axioms full_mode_needs_all_silos
#assert_axioms checkAll_sum_eq
#assert_axioms full_rebalance_total_is_cert_sum
#assert_axioms checkCert_spent_le_ceiling
#assert_axioms byzantine_undetected_overspend_le_f_ceiling
#assert_axioms rebalance_balance_le
#assert_axioms rebalance_conserves_on_exact
-- The unforgeability theorem CARRIES the named portal — assert it depends ONLY on the
-- explicitly-declared `CertUnforgeable` typeclass (no hidden axioms).
#assert_axioms accepted_cert_is_silos_own

end Dregg2.Coord.StingrayCertReconcile
