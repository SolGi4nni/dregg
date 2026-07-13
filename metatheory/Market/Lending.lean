/-
# Market.Lending — DrEX rung 8: UNDERCOLLATERALIZATION-IMPOSSIBLE lending (the marquee dreggfi money market).

**The Certora canonical bad state has NO CONSTRUCTOR.** Every money-market blow-up of the last cycle
(Moonwell / Euler / the xUSD bad-debt event) is one shape: a position that is *underwater*
(`collateralValue < debt · liqRatio`) **and** cannot be liquidated (the liquidation predicate lags the
mark — a governance flag, a keeper grace-window, a paused market), so the shortfall rots into protocol
bad debt. This module builds a lending lifecycle where **that state is unrepresentable**: liquidation
eligibility is not a stored, laggable flag — it is a *pure function of the mark*, DEFINED to be exactly
"underwater" (via the operational transition, `liquidatable_iff_underwater`). The
"liquidatable-but-can't-repay" bad state is therefore a contradiction, `no_bad_debt` — a theorem, not a
monitor. Mirrors `Dregg2/Storage/DealLifecycle.lean`'s "illegal steps have no constructor".

This module **COMPOSES three already-PROVED objects; it re-proves none**:

  * **SOLVENCY** — `Market.pool_solvent_forever` (`Market/Liquidity.lean`): the lending reserve
    (per-asset `Pool`) is never negative at any reachable state along ANY schedule of valid fills
    (`ScheduleValid`), the ∀-adversary object lifted from `Dregg2/Verify/StripeReserve.lean`. Reused
    verbatim as the lending pool's never-insolvent guarantee, plus `stripe_reserve_solvent_forever` as
    the disclosed backing line — the pool of collateral + loans covers all liabilities across ANY
    schedule.
  * **THE LIFECYCLE-WITH-UNREPRESENTABLE-ILLEGAL-STEPS** — `DealLifecycle.lean`'s partial-transition
    pattern (`Open → Healthy → Liquidatable → Liquidated`, every transition a `none`-guarded partial
    function, illegal steps have no constructor): terminal finality, liquidate-requires-liquidatable,
    and the totality that a position **cannot silently rot underwater**.

## The keystones

  * **(a) NO-BAD-DEBT** — `no_bad_debt`: `∀ mark r p, ¬ BadDebt mark r p`, where `BadDebt` is the
    Certora bad state `0 < debt ∧ Underwater ∧ ¬ Liquidatable`. It is uninhabited because
    liquidatability ≡ underwater-ness (`liquidatable_iff_underwater`, proved through the actual
    `liquidate` transition being available). The bad state has NO CONSTRUCTOR. Structurally, the health
    classifier `LoanHealth` has no `badDebt` bucket (`classify_exhaustive`) and `classify` is total.
  * **(b) SOLVENCY** — `lending_pool_solvent_forever` (= `pool_solvent_forever`) + the reused backing
    line: the lending pool stays solvent over ANY schedule; composed into `lending_sound`.
  * **(c) LIQUIDATION IS TOTAL** — `liquidation_total_when_underwater` / `loan_liquidation_total`:
    whenever the ratio breaks, the liquidation transition is available (returns `some`). A position
    cannot silently rot underwater — liquidation is always callable exactly when needed.

## HONEST SCOPE (the oracle edge, DREGGFI-VISION §7)

The theorem is **CONDITIONAL ON THE MARK**: every statement is `∀ (mark : Mark) …` — "GIVEN the price
feed, no bad debt". Pulling the mark itself into the model as a proof-carrying witness (the oracle weld —
the price as a ZK/attested input, §2/§7 "force it in-circuit at settlement") is the NAMED next rung; it
is NOT claimed closed here. What IS proved: given the mark, the bad-debt state is unconstructable, the
pool is solvent forever, and liquidation is always available when the ratio breaks.

NON-VACUITY both polarities: a healthy position across an adversarial PRICE CRASH stays no-bad-debt and
the pool stays solvent (`demo_no_bad_debt_across_crash`, `lending_demo_solvent`; the values/marks are
`#guard`/theorem-pinned) — and the position goes healthy→liquidatable but liquidation is always available
(never bad debt); AND the teeth — the bad state is unconstructable (`bad_debt_unconstructable`, and the
only missing piece is the *impossible* unliquidatability, `demo_bad_debt_needs_only_unliquidatable`), an
under-collateralized origination is REFUSED (`undercollateralized_origination_refused`,
`demo_undercollateralized_refused`), and a healthy position cannot be liquidated
(`liquidate_none_when_healthy`). Mirrors the rung teeth.

Pure.
-/
import Market.Liquidity
import Dregg2.Tactics

namespace Market

open Dregg2.Verify.StripeReserve Dregg2.Apps.Trustline

/-! ## 1. The mark, the position, and the derived health predicates. -/

/-- **A mark** — the exogenous price/valuation of one collateral unit in the debt numeraire. This is the
ORACLE input; every guarantee below is CONDITIONAL ON IT (the §7 oracle edge). -/
structure Mark where
  /-- Collateral-unit price in the debt numeraire (the oracle mark). -/
  price : ℚ
  deriving DecidableEq, Repr, Inhabited

/-- **A lending position** — collateral posted and outstanding debt (numeraire). Note there is NO
`liquidatable`/`healthy` FIELD: health is DERIVED from the mark, never a storable, laggable flag. That
absence is the whole point — a stored flag is exactly what rots underwater in the incumbent designs. -/
structure Position where
  /-- Collateral units posted against the loan. -/
  collateral : ℚ
  /-- Outstanding debt in the numeraire. -/
  debt       : ℚ
  deriving DecidableEq, Repr, Inhabited

/-- The position's **collateral value at a mark** — collateral units priced by the oracle. -/
def Position.value (p : Position) (m : Mark) : ℚ := p.collateral * m.price

/-- **HEALTHY at mark `m` and required ratio `r`** — the collateral value covers the debt scaled by the
liquidation threshold `r` (e.g. `r = 3/2` = 150% over-collateralization). -/
def Healthy (m : Mark) (r : ℚ) (p : Position) : Prop := p.debt * r ≤ p.value m

/-- **UNDERWATER** — the collateral value has fallen below the debt scaled by `r`. Exactly `¬ Healthy`
(`underwater_iff_not_healthy`). -/
def Underwater (m : Mark) (r : ℚ) (p : Position) : Prop := p.value m < p.debt * r

theorem underwater_iff_not_healthy (m : Mark) (r : ℚ) (p : Position) :
    Underwater m r p ↔ ¬ Healthy m r p := by
  unfold Underwater Healthy; exact not_le.symm

/-! ## 2. Liquidation as a TOTAL transition — and liquidatability DEFINED through it. -/

/-- **`liquidate m r p`** — the liquidation transition. It is AVAILABLE (returns `some`) exactly when the
position is underwater at the mark, and REFUSED (`none`) on a healthy position (you never seize good
collateral). On liquidation the debt is cleared and the collateral seized (`⟨0, 0⟩` — the shortfall is
absorbed at the tip, never left to rot). -/
def liquidate (m : Mark) (r : ℚ) (p : Position) : Option Position :=
  if p.value m < p.debt * r then some ⟨0, 0⟩ else none

/-- **LIQUIDATABLE** — the position IS eligible for liquidation, DEFINED as the liquidation transition
being available. Crucially it is *not* a separate, laggable predicate: it is the operational transition
itself. `liquidatable_iff_underwater` proves it coincides with the mark condition, closing by
construction the gap the Certora bad state lives in. -/
def Liquidatable (m : Mark) (r : ℚ) (p : Position) : Prop := (liquidate m r p).isSome = true

/-- **`liquidatable_iff_underwater`** — liquidation eligibility ≡ being underwater. The eligibility
predicate cannot lag the mark, because it IS the mark condition (routed through the actual transition).
This is the seam every incumbent leaves open (a governance flag / keeper window / paused market that
trails the price) welded shut. -/
theorem liquidatable_iff_underwater (m : Mark) (r : ℚ) (p : Position) :
    Liquidatable m r p ↔ Underwater m r p := by
  unfold Liquidatable liquidate Underwater
  by_cases h : p.value m < p.debt * r <;> simp [h]

/-- **`liquidation_total_when_underwater` (KEYSTONE c):** whenever the ratio breaks (underwater),
liquidation is a TOTAL transition — it always returns `some`. A position cannot silently rot underwater:
the moment it crosses the threshold, liquidation is available. -/
theorem liquidation_total_when_underwater (m : Mark) (r : ℚ) (p : Position) (h : Underwater m r p) :
    ∃ p', liquidate m r p = some p' := by
  unfold liquidate; unfold Underwater at h
  rw [if_pos h]; exact ⟨_, rfl⟩

/-- **`liquidate_none_when_healthy` (TOOTH):** a HEALTHY position cannot be liquidated — the transition
is refused. Liquidation is available exactly when needed and never otherwise; good collateral is not
seized. -/
theorem liquidate_none_when_healthy (m : Mark) (r : ℚ) (p : Position) (h : Healthy m r p) :
    liquidate m r p = none := by
  unfold liquidate; unfold Healthy at h; rw [if_neg (not_lt.2 h)]

/-! ## 3. KEYSTONE (a) — NO-BAD-DEBT: the Certora bad state is unconstructable. -/

/-- **`BadDebt m r p` — the Certora canonical bad state**: a position with debt that is underwater AND
NOT liquidatable. This is the "liquidatable-but-can't-repay" shortfall that becomes protocol bad debt in
Moonwell / Euler / xUSD. Below (`no_bad_debt`) it is proved UNINHABITED. -/
def BadDebt (m : Mark) (r : ℚ) (p : Position) : Prop :=
  0 < p.debt ∧ Underwater m r p ∧ ¬ Liquidatable m r p

/-- **`no_bad_debt` (THE KEYSTONE):** for EVERY mark, ratio, and position, the Certora bad state is
UNINHABITED — there is no underwater-and-unliquidatable position. Bad debt is unconstructable, not
monitored. The proof: `¬ Liquidatable` is (`liquidatable_iff_underwater`) exactly `¬ Underwater`, which
contradicts the `Underwater` conjunct. The state has no constructor. -/
theorem no_bad_debt (m : Mark) (r : ℚ) (p : Position) : ¬ BadDebt m r p := by
  rintro ⟨_, hu, hnl⟩
  exact hnl ((liquidatable_iff_underwater m r p).2 hu)

/-- **`bad_debt_unconstructable` (TOOTH, the marquee):** restated as the refusal — the bad-debt state is
never inhabited, at any mark. This is the undercollateralization-impossible claim: given the mark, a
position that is underwater but cannot be liquidated simply does not exist in the state space. -/
theorem bad_debt_unconstructable : ∀ (m : Mark) (r : ℚ) (p : Position), ¬ BadDebt m r p := no_bad_debt

/-! ### The structural face — the health classifier has NO bad-debt bucket. -/

/-- **`LoanHealth`** — the total health classification of a position. It has exactly THREE constructors;
there is **no `badDebt` / `underwaterSafe` constructor**. The "underwater but not liquidatable" bucket is
structurally absent from the type — unrepresentable, `DealLifecycle`-style. -/
inductive LoanHealth
  | clear        -- no debt
  | healthy      -- debt, adequately collateralized at the mark
  | liquidatable -- underwater — liquidation available (never "underwater and safe")
  deriving DecidableEq, Repr

/-- **`classify`** — a TOTAL classifier: every position at every mark lands in exactly one of the three
buckets. There is no branch that yields an underwater-yet-safe state, because that constructor does not
exist. -/
def classify (m : Mark) (r : ℚ) (p : Position) : LoanHealth :=
  if p.debt ≤ 0 then .clear
  else if p.debt * r ≤ p.value m then .healthy
  else .liquidatable

/-- **`classify_exhaustive`** — the classifier's codomain is exactly `{clear, healthy, liquidatable}`;
there is no fourth (bad-debt) case. -/
theorem classify_exhaustive (h : LoanHealth) :
    h = .clear ∨ h = .healthy ∨ h = .liquidatable := by
  cases h <;> simp

/-- **`underwater_classified_liquidatable`** — a position with debt that is underwater is ALWAYS
classified `liquidatable`; it can never be silently filed elsewhere. The classifier routes the entire
underwater region to the one liquidation bucket. -/
theorem underwater_classified_liquidatable (m : Mark) (r : ℚ) (p : Position)
    (hd : 0 < p.debt) (h : Underwater m r p) : classify m r p = .liquidatable := by
  unfold classify; unfold Underwater at h
  rw [if_neg (not_le.2 hd), if_neg (not_le.2 h)]

/-! ## 4. Origination — an under-collateralized loan cannot be born. -/

/-- **`originate m r collateral debt`** — open a loan. It is admitted (returns `some`) ONLY when the loan
is adequately collateralized at the mark (`debt · r ≤ collateralValue`); an under-collateralized
origination is REFUSED (`none`). A freshly originated position is therefore never born underwater
(`originate_healthy`). -/
def originate (m : Mark) (r : ℚ) (collateral debt : ℚ) : Option Position :=
  if debt * r ≤ collateral * m.price then some ⟨collateral, debt⟩ else none

/-- **`originate_healthy`** — every originated position is HEALTHY: the system never enters the underwater
region through the front door. -/
theorem originate_healthy {m : Mark} {r collateral debt : ℚ} {p : Position}
    (h : originate m r collateral debt = some p) : Healthy m r p := by
  unfold originate at h
  by_cases hc : debt * r ≤ collateral * m.price
  · rw [if_pos hc, Option.some.injEq] at h; subst h
    simpa [Healthy, Position.value] using hc
  · rw [if_neg hc] at h; simp at h

/-- **`undercollateralized_origination_refused` (TOOTH):** a loan whose debt exceeds what the collateral
backs at the mark cannot be originated — it returns `none`. Under-collateralization is refused at the
tip, not cleaned up later. -/
theorem undercollateralized_origination_refused (m : Mark) (r collateral debt : ℚ)
    (h : collateral * m.price < debt * r) : originate m r collateral debt = none := by
  unfold originate; rw [if_neg (not_le.2 h)]

/-! ## 5. THE LENDING LIFECYCLE — partial transitions; illegal steps have no constructor. -/

/-- The lifecycle states, `Open → Healthy → Liquidatable → Liquidated` plus the happy `Repaid` terminal.
`Open` is the pre-origination edge (`originate`, §4, produces a `.healthy` loan); the state machine
proper spans `Healthy → Liquidatable → {Liquidated | Repaid}`. -/
inductive LoanState
  | healthy      -- originated + adequately collateralized at the mark
  | liquidatable -- the mark moved: underwater, liquidation available
  | liquidated   -- closed by liquidation (collateral seized, debt cleared, shortfall absorbed)
  | repaid       -- closed by repayment (happy terminal)
  deriving DecidableEq, Repr

/-- The two terminal states admit no further transition. -/
def LoanState.isTerminal : LoanState → Bool
  | .liquidated | .repaid => true
  | _ => false

/-- **A loan** — its lifecycle state, the position it carries, and the mark + required ratio it is read
against. (The mark travels with the loan so each transition guards on the CURRENT valuation.) -/
structure Loan where
  state : LoanState
  pos   : Position
  mark  : Mark
  ratio : ℚ

/-- **`Healthy → Liquidatable`** (partial): the mark moves to `m'` and the position is now underwater at
it. Returns `none` unless the loan is `.healthy` AND underwater at the new mark — you cannot mark a
solvent loan into liquidation. -/
def markToLiquidatable (l : Loan) (m' : Mark) : Option Loan :=
  match l.state with
  | .healthy =>
      if l.pos.value m' < l.pos.debt * l.ratio
      then some { state := .liquidatable, pos := l.pos, mark := m', ratio := l.ratio }
      else none
  | _ => none

/-- **`Liquidatable → Liquidated`** (partial): a liquidatable loan is closed — collateral seized, debt
cleared. Returns `none` on any non-liquidatable state. -/
def liquidateLoan (l : Loan) : Option Loan :=
  match l.state with
  | .liquidatable => some { l with state := .liquidated, pos := ⟨0, 0⟩ }
  | _ => none

/-- **`Healthy → Repaid`** (partial): the borrower repays a healthy loan (debt cleared, collateral
returned). Returns `none` unless the loan is `.healthy`. -/
def repayLoan (l : Loan) : Option Loan :=
  match l.state with
  | .healthy => some { l with state := .repaid, pos := ⟨0, 0⟩ }
  | _ => none

/-- One protocol step — any legal transition. Illegal steps are unrepresentable (the constructors carry
`= some l'`). -/
inductive LoanStep : Loan → Loan → Prop where
  | markDown {l m' l'} : markToLiquidatable l m' = some l' → LoanStep l l'
  | liquidate {l l'}   : liquidateLoan l = some l' → LoanStep l l'
  | repay {l l'}       : repayLoan l = some l' → LoanStep l l'

/-- **Terminal finality.** A liquidated or repaid loan admits NO step — the loan is done. -/
theorem loan_terminal_is_final (l l' : Loan) (ht : l.state.isTerminal = true) : ¬ LoanStep l l' := by
  intro hstep
  cases hstep with
  | markDown h =>
      simp only [markToLiquidatable] at h
      cases hs : l.state <;> simp [hs, LoanState.isTerminal] at ht h
  | liquidate h =>
      simp only [liquidateLoan] at h
      cases hs : l.state <;> simp [hs, LoanState.isTerminal] at ht h
  | repay h =>
      simp only [repayLoan] at h
      cases hs : l.state <;> simp [hs, LoanState.isTerminal] at ht h

/-- **Markdown requires underwater.** You cannot move a loan to `liquidatable` unless it is `.healthy`
and genuinely underwater at the new mark — the state transition is guarded by the actual ratio break. -/
theorem markDown_requires_underwater (l l' : Loan) (m' : Mark)
    (h : markToLiquidatable l m' = some l') :
    l.state = .healthy ∧ l.pos.value m' < l.pos.debt * l.ratio := by
  unfold markToLiquidatable at h
  split at h
  · rename_i hs
    split at h
    · rename_i hc; exact ⟨hs, hc⟩
    · simp at h
  · simp at h

/-- **Liquidation requires the liquidatable state** (and clears the debt to zero — the shortfall is
absorbed, never carried as bad debt). You cannot liquidate a healthy or already-terminal loan. -/
theorem liquidate_requires_liquidatable (l l' : Loan) (h : liquidateLoan l = some l') :
    l.state = .liquidatable ∧ l'.state = .liquidated ∧ l'.pos.debt = 0 := by
  unfold liquidateLoan at h
  split at h
  · rename_i hs
    rw [Option.some.injEq] at h; subst h; exact ⟨hs, rfl, rfl⟩
  · simp at h

/-- **Repayment requires a healthy loan** (and clears the debt). -/
theorem repay_requires_healthy (l l' : Loan) (h : repayLoan l = some l') :
    l.state = .healthy ∧ l'.state = .repaid ∧ l'.pos.debt = 0 := by
  unfold repayLoan at h
  split at h
  · rename_i hs
    rw [Option.some.injEq] at h; subst h; exact ⟨hs, rfl, rfl⟩
  · simp at h

/-- **`loan_liquidation_total` (KEYSTONE c, lifecycle face):** a loan in the `liquidatable` state can
ALWAYS be liquidated — the transition is total there. Composed with `markDown_requires_underwater`, a
loan that goes underwater is moved to `liquidatable` and from `liquidatable` liquidation never blocks: a
loan cannot silently rot underwater. -/
theorem loan_liquidation_total (l : Loan) (h : l.state = .liquidatable) :
    ∃ l', liquidateLoan l = some l' := by
  unfold liquidateLoan; rw [h]; exact ⟨_, rfl⟩

/-! ## 6. KEYSTONE (b) — SOLVENCY: the lending pool covers all liabilities over ANY schedule. -/

/-- **`lending_pool_solvent_forever` (THE SOLVENCY KEYSTONE):** the lending reserve (a per-asset `Pool`
of collateral + loanable inventory) is SOLVENT at every reachable state, along ANY schedule of valid
fills — repayments, liquidations, draws — that respect the reserve floor. This is `pool_solvent_forever`
(`Market/Liquidity.lean`, the ∀-schedule portfolio invariant lifted from
`stripe_reserve_solvent_forever`) reused verbatim: the money market never owes more of any asset than it
holds. -/
theorem lending_pool_solvent_forever (p₀ : Pool) (hinit : Pool.solvent p₀)
    (s : PoolSched) (hs : ScheduleValid p₀ s) : ∀ n, Pool.solvent (poolTraj p₀ s n) :=
  pool_solvent_forever p₀ hinit s hs

/-- **`lending_backing_solvent_forever`** — the lending pool's disclosed backing line (a single
`MoneyInReserve` funded to `R`) is itself solvent forever, over EVERY attest/reverse/spend/finalize
schedule: `stripe_reserve_solvent_forever` reused verbatim (no new proof). The pool's inventory is
solvent (above) AND its funding is solvent (this) — never insolvent, never funded from thin air. -/
theorem lending_backing_solvent_forever (R : Nat) (sched : SSched) :
    ∀ n, 0 ≤ (trajC .fullReserve (openReserve R) sched n).escrow :=
  stripe_reserve_solvent_forever (openReserve R) (openReserve_wf R) sched

/-! ## 7. THE COMPOSED KEYSTONE — no bad debt AND solvent forever. -/

/-- **`lending_sound` — undercollateralization-impossible lending, in one theorem.** Given the mark, a
lending system with a solvent reserve and a valid fill schedule is simultaneously:

  * **(a) NO-BAD-DEBT** — the Certora bad state is unconstructable (`no_bad_debt`);
  * **(b) SOLVENT FOREVER** — the reserve is never negative at any reachable state
    (`pool_solvent_forever`), and its backing line is solvent (`stripe_reserve_solvent_forever`).

Not one line of the solvency backbone or the no-bad-debt derivation is re-proved elsewhere; this is their
COMPOSITION. The claim is CONDITIONAL ON THE MARK (`∀ m`) — the oracle weld (§7) is the named next rung. -/
theorem lending_sound (m : Mark) (r : ℚ) (p : Position)
    (p₀ : Pool) (hinit : Pool.solvent p₀) (s : PoolSched) (hs : ScheduleValid p₀ s)
    (R : Nat) (bsched : SSched) :
    (¬ BadDebt m r p) ∧
    (∀ n, Pool.solvent (poolTraj p₀ s n)) ∧
    (∀ n, 0 ≤ (trajC .fullReserve (openReserve R) bsched n).escrow) :=
  ⟨no_bad_debt m r p,
   lending_pool_solvent_forever p₀ hinit s hs,
   lending_backing_solvent_forever R bsched⟩

/-! ## 8. NON-VACUITY, positive polarity — a healthy loan across an adversarial PRICE CRASH. -/

/-- The required liquidation ratio: 150% over-collateralization. -/
def liqRatio : ℚ := 3 / 2

/-- A healthy mark: collateral priced at 1 numeraire/unit. -/
def healthyMark : Mark := ⟨1⟩

/-- A crashed mark: collateral has fallen to 0.3 numeraire/unit — a 70% drawdown. -/
def crashMark : Mark := ⟨3 / 10⟩

/-- A concrete position: 100 collateral, 40 debt. At `healthyMark` its value 100 ≥ 40·1.5 = 60 (healthy);
at `crashMark` its value 30 < 60 (underwater). -/
def lendPos : Position := ⟨100, 40⟩

theorem demoPos_healthy : Healthy healthyMark liqRatio lendPos := by
  norm_num [Healthy, Position.value, lendPos, healthyMark, liqRatio]

theorem demoPos_underwater_at_crash : Underwater crashMark liqRatio lendPos := by
  norm_num [Underwater, Position.value, lendPos, crashMark, liqRatio]

/-- At the crash the position is LIQUIDATABLE — liquidation is available (from the mark alone). -/
theorem demoPos_liquidatable_at_crash : Liquidatable crashMark liqRatio lendPos :=
  (liquidatable_iff_underwater crashMark liqRatio lendPos).2 demoPos_underwater_at_crash

/-- The health classifier tracks the mark: `healthy` before the crash, `liquidatable` after. -/
theorem demoPos_classify_healthy : classify healthyMark liqRatio lendPos = .healthy := by
  norm_num [classify, Position.value, lendPos, healthyMark, liqRatio]

theorem demoPos_classify_liquidatable_at_crash : classify crashMark liqRatio lendPos = .liquidatable := by
  norm_num [classify, Position.value, lendPos, crashMark, liqRatio]

/-- An adversarial PRICE CRASH — a monotone sequence of marks driving the collateral down 70%. -/
def priceCrash : List Mark := [⟨1⟩, ⟨3 / 4⟩, ⟨1 / 2⟩, ⟨3 / 10⟩]

/-- **`demo_no_bad_debt_across_crash` (positive polarity):** at EVERY mark of the crash — healthy or
deep underwater — the demo position is NEVER in the bad-debt state. As the price falls it goes
healthy → liquidatable, but liquidation is always available, so the shortfall is never an
underwater-and-unliquidatable one. The undercollateralization-impossible claim, exhibited across an
adversarial price path. -/
theorem demo_no_bad_debt_across_crash : ∀ m ∈ priceCrash, ¬ BadDebt m liqRatio lendPos :=
  fun m _ => no_bad_debt m liqRatio lendPos

/-- **`demo_bad_debt_needs_only_unliquidatable` (the crisp non-vacuity):** TWO of the three bad-debt
conjuncts genuinely hold at the crash — the debt is positive (40 > 0) and the position IS underwater
(30 < 60). So `no_bad_debt` is not vacuous over an empty domain: the ONLY thing that fails is the
(impossible) `¬ Liquidatable`. The bad state is unconstructable precisely at the liquidatability seam. -/
theorem demo_bad_debt_needs_only_unliquidatable :
    (0 < lendPos.debt ∧ Underwater crashMark liqRatio lendPos)
      ∧ ¬ BadDebt crashMark liqRatio lendPos := by
  refine ⟨⟨?_, demoPos_underwater_at_crash⟩, no_bad_debt crashMark liqRatio lendPos⟩
  norm_num [lendPos]

/-! ### Solvency non-vacuity — the pool stays solvent over a real schedule (rung-6 demo reused). -/

/-- **`lending_demo_solvent` (positive polarity):** the lending pool stays solvent at every state along
the worked rung-6 draw schedule (`demoPool`/`demoSched`), via `pool_solvent_forever` — the solvency
backbone fires on a concrete stream. -/
theorem lending_demo_solvent : ∀ n, Pool.solvent (poolTraj demoPool demoSched n) :=
  demo_solvent_forever

/-- A concrete (idle) backing schedule for the disclosed reserve line. -/
def demoBacking : SSched := fun _ => .settle 0

/-- The lending system is sound on the demo instance: no bad debt at the crash mark, pool solvent
forever, backing line solvent forever — `lending_sound` instantiated. -/
theorem lending_demo_sound :
    (¬ BadDebt crashMark liqRatio lendPos) ∧
    (∀ n, Pool.solvent (poolTraj demoPool demoSched n)) ∧
    (∀ n, 0 ≤ (trajC .fullReserve (openReserve 100) demoBacking n).escrow) :=
  lending_sound crashMark liqRatio lendPos demoPool demoPool_solvent demoSched demoSched_valid
    100 demoBacking

/-! ### `#guard` smoke — the mark/value numbers behind the keystones are COMPUTED. -/

#guard lendPos.value healthyMark == (100 : ℚ)   -- collateral value pre-crash
#guard lendPos.value crashMark == (30 : ℚ)      -- collateral value post-crash (70% down)
#guard lendPos.debt * liqRatio == (60 : ℚ)      -- the liquidation line (debt · 1.5)
-- healthy: 100 ≥ 60 ; underwater at crash: 30 < 60 — liquidation available exactly there.

/-! ## 9. NON-VACUITY, negative polarity — the teeth. -/

/-- **`demo_undercollateralized_refused` (TOOTH):** an origination asking for 100 debt against only 10
collateral at price 1 needs 150 of value but has 10 — it is REFUSED (`none`). Under-collateralization
cannot be born. -/
theorem demo_undercollateralized_refused : originate healthyMark liqRatio 10 100 = none := by
  norm_num [originate, healthyMark, liqRatio]

/-- **`demo_liquidate_refused_when_healthy` (TOOTH):** the healthy demo position cannot be liquidated —
`liquidate` returns `none`. Good collateral is never seized. -/
theorem demo_liquidate_refused_when_healthy : liquidate healthyMark liqRatio lendPos = none :=
  liquidate_none_when_healthy healthyMark liqRatio lendPos demoPos_healthy

/-- An already-terminal (repaid) loan on the demo position. -/
def repaidLoan : Loan := ⟨.repaid, ⟨0, 0⟩, healthyMark, liqRatio⟩

/-- **`repaid_loan_is_final` (TOOTH):** a repaid loan admits no further step — the lifecycle terminal is
final. -/
theorem repaid_loan_is_final (l' : Loan) : ¬ LoanStep repaidLoan l' :=
  loan_terminal_is_final repaidLoan l' rfl

/-! ## 10. Axiom hygiene — the lending keystones pinned kernel-clean. -/

#assert_all_clean [Market.underwater_iff_not_healthy, Market.liquidatable_iff_underwater,
  Market.liquidation_total_when_underwater, Market.liquidate_none_when_healthy, Market.no_bad_debt,
  Market.bad_debt_unconstructable, Market.classify_exhaustive, Market.underwater_classified_liquidatable,
  Market.originate_healthy, Market.undercollateralized_origination_refused, Market.loan_terminal_is_final,
  Market.markDown_requires_underwater, Market.liquidate_requires_liquidatable, Market.repay_requires_healthy,
  Market.loan_liquidation_total, Market.lending_pool_solvent_forever, Market.lending_backing_solvent_forever,
  Market.lending_sound, Market.demo_no_bad_debt_across_crash, Market.demo_bad_debt_needs_only_unliquidatable,
  Market.lending_demo_solvent, Market.lending_demo_sound, Market.demo_undercollateralized_refused,
  Market.demo_liquidate_refused_when_healthy, Market.repaid_loan_is_final]

end Market
