/-
# Market.OracleWeld — THE ORACLE WELD: the lending Mark carried as a GRADED (attested) witness.

**The biggest honest-edge closer in `docs/deos/DREGGFI-VISION.md` §7 (the oracle edge), for the
lending+solvency tower.** `Market/Lending.lean` proves `no_bad_debt` / `lending_sound` **conditional
on the mark**: every statement quantifies `∀ (m : Mark) …` — "GIVEN the price feed, no bad debt".
The `Mark` is an **unbounded assumption**: the guarantee holds for *any* price an adversary picks.
That is the §7 oracle edge, the input-integrity half.

This module welds the mark's **provenance** into the model, composing the deployed integrity lanes
(the ATTESTED lane `tee-verify/src/attested_data.rs` + the zkTLS producer `zkoracle-prove`):
the mark becomes an [`AttestedMark`] — a price that **carries its named source and a trust grade**.
It re-proves NONE of the lending logic; it COMPOSES `no_bad_debt` (PROVED) with the attested mark,
and states the honest composite grade.

## What this weld IS, and precisely what it is NOT

* IT IS: the lending guarantee restated over a mark that carries provenance
  (`no_bad_debt_attested`, `lending_sound_attested`) — the model-level twin of the Rust
  `GradedMark`, which has **no bare-price constructor** (`tee-verify/src/oracle_mark.rs`): the
  lending consumer takes a graded mark, never a free price. So the honest edge moves from
  *"given the mark (unbounded)"* to *"given an ATTESTED mark (named source, graded)."*

* IT IS: the honest grade. A price is an EXTERNAL fact; the best it gets is **ATTESTED** (HW-vendor
  root + side-channel + freshness residual), never PROVED. The composite — attested mark + PROVED
  lending logic — is graded at its **weakest leg**: ATTESTED (`oracle_weld_composite_grade`,
  `mark_leg_not_proved`). This weld does **NOT** make the price "proved true".

* IT IS NOT a narrower LOGICAL quantifier. `∀ (am : AttestedMark)` still ranges over every price
  (an `AttestedMark` can carry any `ℚ`). The real narrowing is **operational**: in the deployed
  system a `GradedMark` is minted ONLY by verifying an attestation over the price (the Rust teeth:
  a forged/unattested price yields no mark). The Lean side's job is (a) to tie the lending `Mark` to
  an attested mark's value and (b) to prove the grade composition — NOT to pretend the price is
  bounded in-logic. Stated plainly so nobody reads more into `∀ am` than is there.

Pure. Composes `Market.Lending`; re-proves none of it.
-/
import Market.Lending

namespace Market

open Dregg2.Verify.StripeReserve Dregg2.Apps.Trustline

/-! ## 1. The trust grade lattice — the OCIP spine (`DREGGFI-VISION.md` §1). -/

/-- **A trust grade.** `PROVED` — a machine-checked theorem about the deployed artifact (the lending
logic). `ATTESTED` — a HW-rooted attestation or zkTLS provenance about an *input* (a price); you
still trust the HW-vendor root + side-channel residual, which is WHY it is not PROVED. `REPLAYABLE`
— a pure re-derivation over public data. Mirrors `tee-verify/src/oracle_mark.rs::Grade`. -/
inductive TrustGrade
  | proved
  | attested
  | replayable
  deriving DecidableEq, Repr

/-- The trust DEMANDED by a grade (lower = stronger): `replayable` trusts only your machine,
`proved` the checker + crypto assumptions, `attested` additionally the HW-vendor root. The
weakest-leg composition orders on this rank. -/
def TrustGrade.rank : TrustGrade → Nat
  | .replayable => 0
  | .proved     => 1
  | .attested   => 2

/-- **The composite grade of two legs = the WEAKEST** (the max-rank, trust-minimization order,
`docs/deos/EFFECTVM-SIDESTRUCTURE-ABI.md` §3.4): a claim is only as strong as its weakest-trusted
input. -/
def TrustGrade.weakest (a b : TrustGrade) : TrustGrade :=
  if a.rank ≥ b.rank then a else b

/-! ## 2. Provenance — the named source that replaces the unbounded `∀ mark`. -/

/-- **The named source** a graded mark's price came from. `teeAttested` — a named enclave (code
identity) produced it (the ATTESTED lane). `zkTlsProvenance` — a named API origin reported it, its
TLS session verified by the zkTLS producer. Either way the mark is NOT anonymous: it names who
reported it. Mirrors `tee-verify/src/oracle_mark.rs::MarkProvenance`. -/
inductive MarkProvenance
  | teeAttested (enclave : String)     -- the named enclave code identity
  | zkTlsProvenance (origin : String)  -- the named CEX / API origin
  deriving DecidableEq, Repr

/-- The human-readable name of the source — the mark is attributable. -/
def MarkProvenance.namedSource : MarkProvenance → String
  | .teeAttested e   => "tee-enclave:" ++ e
  | .zkTlsProvenance o => o

/-! ## 3. The attested mark — a price WITH its provenance + grade. -/

/-- **An ATTESTED MARK** — the lending `Mark` bundled with its provenance and grade. There is no
`Inhabited`-by-a-bare-price path that drops the provenance: the field is REQUIRED, exactly as the
Rust `GradedMark` has no public bare-price constructor. The `grade` is ATTESTED by construction —
a price is external. -/
structure AttestedMark where
  /-- The underlying price/valuation mark the lending logic reads. -/
  mark : Mark
  /-- The named source that reported the price. -/
  provenance : MarkProvenance
  /-- The grade this mark carries — ATTESTED (a price is an external fact; never PROVED). -/
  grade : TrustGrade := TrustGrade.attested
  deriving Repr

/-- Project the underlying `Mark` — what the lending logic consumes. The lending guarantee is
instantiated at THIS value, but the value arrives WITH provenance attached. -/
def AttestedMark.toMark (am : AttestedMark) : Mark := am.mark

/-- **The mark is attributable.** `namedSource` faithfully exposes the underlying source field —
the enclave (tagged `tee-enclave:`) for the TEE lane, the origin host for the zkTLS lane. The mark
is no longer a free `ℚ`; it is a price bound to a specific reporting source. (Structural content of
the weld: the provenance is not droppable — it determines the source string.) -/
theorem attested_mark_names_its_source (e o : String) :
    (MarkProvenance.teeAttested e).namedSource = "tee-enclave:" ++ e ∧
    (MarkProvenance.zkTlsProvenance o).namedSource = o :=
  ⟨rfl, rfl⟩

/-! ## 4. The honest grade — ATTESTED, not PROVED (the whole point). -/

/-- **`oracle_weld_composite_grade` (THE HONEST GRADE):** the composite of the mark leg (ATTESTED)
and the lending arithmetic (PROVED) is graded at the WEAKEST leg = **ATTESTED**. A lending guarantee
that consumes an attested mark is ATTESTED for the input, PROVED for the arithmetic, and therefore
never uniformly PROVED. Mirrors `tee-verify/src/oracle_mark.rs::GradedMark::lending_composite_grade`. -/
theorem oracle_weld_composite_grade :
    TrustGrade.weakest .attested .proved = .attested := by decide

/-- The composition is symmetric — either ordering of the two legs grades ATTESTED. -/
theorem oracle_weld_grade_symm :
    TrustGrade.weakest .proved .attested = .attested := by decide

/-- **`mark_leg_not_proved` (HONESTY):** the mark leg is ATTESTED, and ATTESTED ≠ PROVED. This weld
does NOT make the price proved-true — a price is external. State it as a theorem so the honesty is
machine-checked, not just prose. -/
theorem mark_leg_not_proved : (TrustGrade.attested ≠ TrustGrade.proved) := by decide

/-- An attested mark's grade is ATTESTED by construction (the default), so the composite with the
PROVED lending logic is ATTESTED — the weld cannot silently launder an attested price to PROVED. -/
theorem attested_mark_composite_is_attested (am : AttestedMark) (h : am.grade = .attested) :
    TrustGrade.weakest am.grade .proved = .attested := by
  rw [h]; exact oracle_weld_composite_grade

/-! ## 5. THE GRADED KEYSTONES — the lending guarantee over an attested mark. -/

/-- **`no_bad_debt_attested` (THE GRADED KEYSTONE):** for every ATTESTED mark, the Certora bad-debt
state is unconstructable. This is `Lending.no_bad_debt` (PROVED) composed with the attested mark: the
mark the guarantee is conditional on is no longer an unbounded free price — it carries named-source
provenance and a grade. The guarantee's crypto-strength is the WEAKEST leg: ATTESTED for the mark,
PROVED for the no-bad-debt derivation. -/
theorem no_bad_debt_attested (am : AttestedMark) (r : ℚ) (p : Position) :
    ¬ BadDebt am.toMark r p :=
  no_bad_debt am.toMark r p

/-- Liquidation is still TOTAL when underwater at an attested mark — the total-liquidation keystone
survives the graded instantiation. -/
theorem liquidation_total_attested (am : AttestedMark) (r : ℚ) (p : Position)
    (h : Underwater am.toMark r p) : ∃ p', liquidate am.toMark r p = some p' :=
  liquidation_total_when_underwater am.toMark r p h

/-- **`lending_sound_attested` (THE COMPOSED GRADED KEYSTONE):** given an ATTESTED mark, a lending
system with a solvent reserve over a valid schedule is simultaneously:

  * **(a) NO-BAD-DEBT** — the Certora bad state is unconstructable at the attested mark;
  * **(b) SOLVENT FOREVER** — the reserve is never negative (`pool_solvent_forever`) and its backing
    line is solvent (`stripe_reserve_solvent_forever`);
  * **(c) HONESTLY GRADED** — the composite grade (attested mark + PROVED lending) is ATTESTED, NOT
    PROVED. The price is not proved-true; it is attested from a named source.

This is `Lending.lending_sound` welded to a graded mark: the mark is now an ATTESTED input, not an
unbounded assumption, and the honest grade travels WITH the guarantee. -/
theorem lending_sound_attested (am : AttestedMark) (r : ℚ) (p : Position)
    (p₀ : Pool) (hinit : Pool.solvent p₀) (s : PoolSched) (hs : ScheduleValid p₀ s)
    (R : Nat) (bsched : SSched) (hg : am.grade = .attested) :
    (¬ BadDebt am.toMark r p) ∧
    (∀ n, Pool.solvent (poolTraj p₀ s n)) ∧
    (∀ n, 0 ≤ (trajC .fullReserve (openReserve R) bsched n).escrow) ∧
    (TrustGrade.weakest am.grade .proved = .attested) :=
  ⟨no_bad_debt_attested am r p,
   lending_pool_solvent_forever p₀ hinit s hs,
   lending_backing_solvent_forever R bsched,
   attested_mark_composite_is_attested am hg⟩

/-! ## 6. NON-VACUITY — the demo attested marks, both provenance lanes, across the crash. -/

/-- A TEE-attested healthy mark: the crash-demo `healthyMark` (price 1) reported by a named enclave. -/
def teeHealthyMark : AttestedMark :=
  { mark := healthyMark, provenance := .teeAttested "coinbase-oracle-enclave-v1" }

/-- A zkTLS-provenance crashed mark: the crash-demo `crashMark` (price 0.3) reported by a named CEX
origin (`api.coinbase.com`). -/
def zktlsCrashMark : AttestedMark :=
  { mark := crashMark, provenance := .zkTlsProvenance "api.coinbase.com" }

/-- Both demo marks carry the ATTESTED grade — a price is never PROVED. -/
theorem demo_marks_are_attested :
    teeHealthyMark.grade = .attested ∧ zktlsCrashMark.grade = .attested := ⟨rfl, rfl⟩

/-- **Positive polarity, attested:** at the crash mark reported by the named zkTLS origin, the demo
lending position is NEVER in the bad-debt state — the undercollateralization-impossible claim holds
over an ATTESTED, named-source mark, not just a free assumed price. -/
theorem demo_no_bad_debt_attested_at_crash :
    ¬ BadDebt zktlsCrashMark.toMark liqRatio lendPos :=
  no_bad_debt_attested zktlsCrashMark liqRatio lendPos

/-- The full graded soundness on the demo instance: no bad debt at the attested crash mark, pool
solvent forever, backing solvent forever, AND the composite honestly graded ATTESTED. -/
theorem demo_lending_sound_attested :
    (¬ BadDebt zktlsCrashMark.toMark liqRatio lendPos) ∧
    (∀ n, Pool.solvent (poolTraj demoPool demoSched n)) ∧
    (∀ n, 0 ≤ (trajC .fullReserve (openReserve 100) demoBacking n).escrow) ∧
    (TrustGrade.weakest zktlsCrashMark.grade .proved = .attested) :=
  lending_sound_attested zktlsCrashMark liqRatio lendPos demoPool demoPool_solvent demoSched
    demoSched_valid 100 demoBacking rfl

/-- The crash mark under the graded position IS genuinely underwater (30 < 60) — so
`no_bad_debt_attested` is not vacuous: the only failing bad-debt conjunct is the impossible
`¬ Liquidatable`, exactly as in the ungraded demo, now over the named-source attested mark. -/
theorem demo_attested_crash_underwater : Underwater zktlsCrashMark.toMark liqRatio lendPos :=
  demoPos_underwater_at_crash

/-! ## 7. Axiom hygiene — the oracle-weld keystones pinned kernel-clean. -/

#assert_all_clean [Market.attested_mark_names_its_source, Market.oracle_weld_composite_grade,
  Market.oracle_weld_grade_symm, Market.mark_leg_not_proved,
  Market.attested_mark_composite_is_attested, Market.no_bad_debt_attested,
  Market.liquidation_total_attested, Market.lending_sound_attested, Market.demo_marks_are_attested,
  Market.demo_no_bad_debt_attested_at_crash, Market.demo_lending_sound_attested,
  Market.demo_attested_crash_underwater]

end Market
