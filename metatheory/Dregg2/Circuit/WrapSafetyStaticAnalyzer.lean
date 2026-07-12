/-
# Dregg2.Circuit.WrapSafetyStaticAnalyzer — a DECIDABLE wrap-class linter over the descriptor IR.

`docs/reference/WRAP-CLASS-AUDIT.md` found the **mod-p reconstruction wrap class** by hand: a deployed
gate reconstructs/sums a value whose honest range reaches `p = 2013265921` (BabyBear ≈ 2³¹) while the
AIR only forces it `≡ 0 [ZMOD p]`, so a `p`-shifted witness satisfies the mod-p gate but violates the
true-ℤ relation ⟹ forgery. That audit "should have been a linter". This file IS the linter.

The analysis is INTERVAL ARITHMETIC over ℤ — a few adds/muls per gate, NOT an enumeration. For a
constraint's residual `R = <gate body>` over the trace columns, given the descriptor's range-checks
(`ranges : List VmRange`, each `⟨col, bits⟩` bounding `0 ≤ col < 2^bits`), we compute a STATIC INTERVAL
`[lo, hi]` on `R` and classify:

  * **SAFE** — `hi < p ∧ -p < lo`: the residual lives in `(-p, p)`, so `R ≡ 0 [ZMOD p] ⟺ R = 0`
    (`safe_no_wrap`). SAFE is a THEOREM, not a heuristic: `intervalW_sound` proves the interval is a
    genuine over-approximation, and `exprInterval_safe_no_wrap` chains it to no-wrap.
  * **SUSPECT** — `hi ≥ p ∨ lo ≤ -p`: the residual CAN reach a nonzero multiple of `p` (the vault /
    cap-open / transfer / cross-cell class).
  * **UNRANGED** — a column feeding the residual has no range-check ⟹ the interval is unbounded (the
    task-spec `exprInterval`), OR under the canonical-felt reading the column is only pinned to
    `[0, p-1]` (the `…F` field-aware variant). Transfer's unranged `amount` is exactly this.

Two column-bound oracles share ONE interval engine (`intervalW`) and ONE soundness proof
(`intervalW_sound`):
  * `rangeBound` — a column is bounded IFF it has an explicit `VmRange` (the task-spec `exprInterval`;
    an unranged column ⟹ `none` ⟹ UNRANGED). This is what flags the unranged `amount`.
  * `fieldBound` — every column is a CANONICAL BabyBear felt in `[0, p-1]` (always true of a deployed
    trace), tightened to `[0, 2^bits)` where a range exists (`exprIntervalF`). Under this the deployed
    scan is crisp: passthrough/continuity/binding gates become SAFE, and only the genuine
    value-reconstruction sums stay SUSPECT.

No `sorry`. Imports are read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitBurn

namespace Dregg2.Circuit.WrapSafetyStaticAnalyzer

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2

/-- The BabyBear field modulus the deployed AIR reduces mod (`p = 2013265921 = 15·2²⁷ + 1`). -/
def wrapP : ℤ := 2013265921

/-! ## §1 — Interval multiplication (the 4-corner product) and its soundness. -/

/-- Interval product: `[la,ha]·[lb,hb] = [min of the 4 corner products, max of the 4]`. Sound over
signed intervals (the corners cover every sign combination). -/
def mulI : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ
  | (la, ha), (lb, hb) =>
    let c1 := la * lb; let c2 := la * hb; let c3 := ha * lb; let c4 := ha * hb
    (min (min c1 c2) (min c3 c4), max (max c1 c2) (max c3 c4))

/-- **`mulI` is a sound over-approximation of the product.** For `x ∈ [la,ha]`, `y ∈ [lb,hb]`, the
product `x*y` lies in `mulI (la,ha) (lb,hb)`. Proved by reducing to a single corner via the signs of
`y` and the relevant endpoint (bilinearity: the extremes of a product over a box are at its corners). -/
theorem mulI_sound {la ha lb hb x y : ℤ}
    (hxl : la ≤ x) (hxh : x ≤ ha) (hyl : lb ≤ y) (hyh : y ≤ hb) :
    (mulI (la, ha) (lb, hb)).1 ≤ x * y ∧ x * y ≤ (mulI (la, ha) (lb, hb)).2 := by
  simp only [mulI]
  refine ⟨?_, ?_⟩
  · -- lower bound: min of corners ≤ x*y
    have key : la * lb ≤ x * y ∨ la * hb ≤ x * y ∨ ha * lb ≤ x * y ∨ ha * hb ≤ x * y := by
      rcases le_total 0 y with hy | hy
      · have h1 : la * y ≤ x * y := by nlinarith [mul_nonneg (sub_nonneg.mpr hxl) hy]
        rcases le_total 0 la with hla | hla
        · exact Or.inl (by nlinarith [h1, mul_nonneg hla (sub_nonneg.mpr hyl)])
        · exact Or.inr (Or.inl (by nlinarith [h1, mul_nonneg (neg_nonneg.mpr hla) (sub_nonneg.mpr hyh)]))
      · have h1 : ha * y ≤ x * y := by nlinarith [mul_nonneg (sub_nonneg.mpr hxh) (neg_nonneg.mpr hy)]
        rcases le_total 0 ha with hha | hha
        · exact Or.inr (Or.inr (Or.inl (by nlinarith [h1, mul_nonneg hha (sub_nonneg.mpr hyl)])))
        · exact Or.inr (Or.inr (Or.inr (by nlinarith [h1, mul_nonneg (neg_nonneg.mpr hha) (sub_nonneg.mpr hyh)])))
    rcases key with h | h | h | h
    · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) h
    · exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) h
    · exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) h
    · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) h
  · -- upper bound: x*y ≤ max of corners
    have key : x * y ≤ la * lb ∨ x * y ≤ la * hb ∨ x * y ≤ ha * lb ∨ x * y ≤ ha * hb := by
      rcases le_total 0 y with hy | hy
      · have h1 : x * y ≤ ha * y := by nlinarith [mul_nonneg (sub_nonneg.mpr hxh) hy]
        rcases le_total 0 ha with hha | hha
        · exact Or.inr (Or.inr (Or.inr (by nlinarith [h1, mul_nonneg hha (sub_nonneg.mpr hyh)])))
        · exact Or.inr (Or.inr (Or.inl (by nlinarith [h1, mul_nonneg (neg_nonneg.mpr hha) (sub_nonneg.mpr hyl)])))
      · have h1 : x * y ≤ la * y := by nlinarith [mul_nonneg (sub_nonneg.mpr hxl) (neg_nonneg.mpr hy)]
        rcases le_total 0 la with hla | hla
        · exact Or.inr (Or.inl (by nlinarith [h1, mul_nonneg hla (sub_nonneg.mpr hyh)]))
        · exact Or.inl (by nlinarith [h1, mul_nonneg (neg_nonneg.mpr hla) (sub_nonneg.mpr hyl)])
    rcases key with h | h | h | h
    · exact le_trans h (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact le_trans h (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact le_trans h (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans h (le_trans (le_max_right _ _) (le_max_right _ _))

/-! ## §2 — The interval engine, parametric in a column-bound ORACLE. -/

/-- `intervalW colBound e` — a static interval over-approximation of `e.eval a`, given a per-column
bound oracle (`colBound c = some (lo,hi)` ⟹ `a c ∈ [lo,hi]`; `none` ⟹ column unbounded). `none`
propagates: any unbounded column that FEEDS the residual makes the whole interval unbounded. -/
def intervalW (colBound : Nat → Option (ℤ × ℤ)) : EmittedExpr → Option (ℤ × ℤ)
  | .const k => some (k, k)
  | .var c   => colBound c
  | .add a b =>
    match intervalW colBound a, intervalW colBound b with
    | some (la, ha), some (lb, hb) => some (la + lb, ha + hb)
    | _, _ => none
  | .mul a b =>
    match intervalW colBound a, intervalW colBound b with
    | some ia, some ib => some (mulI ia ib)
    | _, _ => none

/-- **The interval engine is SOUND.** If every column obeys its oracle bound on `a`, then a `some`
interval from `intervalW` genuinely brackets `e.eval a`. This is what makes a SAFE verdict a theorem. -/
theorem intervalW_sound (colBound : Nat → Option (ℤ × ℤ)) (a : Assignment)
    (hC : ∀ c lo hi, colBound c = some (lo, hi) → lo ≤ a c ∧ a c ≤ hi) (e : EmittedExpr) :
    ∀ lo hi, intervalW colBound e = some (lo, hi) → lo ≤ e.eval a ∧ e.eval a ≤ hi := by
  induction e with
  | const k =>
    intro lo hi h
    simp only [intervalW, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨le_of_eq rfl, le_of_eq rfl⟩
  | var c =>
    intro lo hi h
    simp only [intervalW] at h
    have := hC c lo hi h
    simpa [EmittedExpr.eval] using this
  | add x y ihx ihy =>
    intro lo hi h
    rcases hx : intervalW colBound x with _ | ⟨lax, hax⟩
    · simp [intervalW, hx] at h
    · rcases hy : intervalW colBound y with _ | ⟨lby, hby⟩
      · simp [intervalW, hx, hy] at h
      · simp only [intervalW, hx, hy, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have Hx := ihx _ _ hx
        have Hy := ihy _ _ hy
        simp only [EmittedExpr.eval]
        exact ⟨add_le_add Hx.1 Hy.1, add_le_add Hx.2 Hy.2⟩
  | mul x y ihx ihy =>
    intro lo hi h
    rcases hx : intervalW colBound x with _ | ⟨lax, hax⟩
    · simp [intervalW, hx] at h
    · rcases hy : intervalW colBound y with _ | ⟨lby, hby⟩
      · simp [intervalW, hx, hy] at h
      · simp only [intervalW, hx, hy, mulI, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have Hx := ihx _ _ hx
        have Hy := ihy _ _ hy
        have hm := mulI_sound Hx.1 Hx.2 Hy.1 Hy.2
        simp only [mulI] at hm
        simpa only [EmittedExpr.eval] using hm

/-! ## §3 — The two oracles: explicit-range (task-spec) and canonical-felt (field-aware). -/

/-- The range bits for a column, if it carries an explicit `VmRange` tooth. -/
def rangeBits (ranges : List VmRange) (c : Nat) : Option Nat :=
  (ranges.find? (fun r => r.wire == c)).map (·.bits)

/-- The explicit-range bound: `[0, 2^bits)` iff `c` is range-checked, else `none` (UNBOUNDED). -/
def rangeBound (ranges : List VmRange) (c : Nat) : Option (ℤ × ℤ) :=
  (rangeBits ranges c).map (fun b => (0, (2 : ℤ) ^ b - 1))

/-- The canonical-felt bound: `[0, 2^bits)` where a range exists (tighter), else `[0, p-1]` — every
trace column is a canonical BabyBear element. Always `some` (no column is truly unbounded on a
deployed trace). -/
def fieldBound (ranges : List VmRange) (c : Nat) : Option (ℤ × ℤ) :=
  some ((rangeBound ranges c).getD (0, wrapP - 1))

/-- **`exprInterval` — the task-spec analyzer**: interval of a gate body under the explicit
range-checks (unranged column ⟹ `none`). -/
def exprInterval (ranges : List VmRange) (e : EmittedExpr) : Option (ℤ × ℤ) :=
  intervalW (rangeBound ranges) e

/-- **`exprIntervalF` — the field-aware analyzer**: interval under the canonical-felt bound, tightened
by explicit ranges. Never `none` (every column is a felt). -/
def exprIntervalF (ranges : List VmRange) (e : EmittedExpr) : Option (ℤ × ℤ) :=
  intervalW (fieldBound ranges) e

/-- The explicit-range oracle is sound whenever the range teeth `hold` on the assignment. -/
theorem rangeBound_hyp (ranges : List VmRange) (a : Assignment)
    (hR : ∀ r ∈ ranges, 0 ≤ a r.wire ∧ a r.wire < (2 : ℤ) ^ r.bits) :
    ∀ c lo hi, rangeBound ranges c = some (lo, hi) → lo ≤ a c ∧ a c ≤ hi := by
  intro c lo hi h
  simp only [rangeBound, rangeBits] at h
  rcases hfind : ranges.find? (fun r => r.wire == c) with _ | r
  · rw [hfind] at h; simp at h
  · rw [hfind] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hmem : r ∈ ranges := List.mem_of_find?_eq_some hfind
    have hwire : r.wire = c := by
      have := List.find?_some hfind
      simpa using this
    obtain ⟨hlo, hhi⟩ := hR r hmem
    rw [hwire] at hlo hhi
    exact ⟨hlo, by omega⟩

/-- The canonical-felt oracle is sound whenever the range teeth hold AND every column is a canonical
felt (`0 ≤ a c ≤ p-1`) — the standing invariant of a deployed BabyBear trace. -/
theorem fieldBound_hyp (ranges : List VmRange) (a : Assignment)
    (hR : ∀ r ∈ ranges, 0 ≤ a r.wire ∧ a r.wire < (2 : ℤ) ^ r.bits)
    (hCanon : ∀ c, 0 ≤ a c ∧ a c ≤ wrapP - 1) :
    ∀ c lo hi, fieldBound ranges c = some (lo, hi) → lo ≤ a c ∧ a c ≤ hi := by
  intro c lo hi h
  simp only [fieldBound, Option.some.injEq] at h
  rcases hrb : rangeBound ranges c with _ | ⟨rlo, rhi⟩
  · rw [hrb] at h
    simp only [Option.getD_none, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hCanon c
  · rw [hrb] at h
    simp only [Option.getD_some, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact rangeBound_hyp ranges a hR c rlo rhi hrb

/-- **`exprInterval_sound` — the task-named soundness**: if the explicit range teeth hold on `a`, a
`some (lo,hi)` from `exprInterval` genuinely brackets the gate body's value. (A thin corollary of the
oracle-generic `intervalW_sound` at the `rangeBound` oracle.) -/
theorem exprInterval_sound (ranges : List VmRange) (a : Assignment)
    (hR : ∀ r ∈ ranges, 0 ≤ a r.wire ∧ a r.wire < (2 : ℤ) ^ r.bits)
    (e : EmittedExpr) (lo hi : ℤ) (hI : exprInterval ranges e = some (lo, hi)) :
    lo ≤ e.eval a ∧ e.eval a ≤ hi :=
  intervalW_sound (rangeBound ranges) a (rangeBound_hyp ranges a hR) e lo hi hI

/-! ## §4 — The no-wrap keystone and the analyzer soundness. -/

/-- **The wrap-freedom fact.** A residual bracketed in `(-p, p)` and `≡ 0 [ZMOD p]` is EXACTLY `0`:
`p ∣ R` with `|R| < p` forces `R = 0`. This is why SAFE ⟹ "no `p`-shifted forgery". -/
theorem safe_no_wrap {lo hi R : ℤ} (hlo : -wrapP < lo) (hhi : hi < wrapP)
    (h1 : lo ≤ R) (h2 : R ≤ hi) (hmod : R ≡ 0 [ZMOD wrapP]) : R = 0 := by
  have hdvd : (wrapP : ℤ) ∣ R := Int.modEq_zero_iff_dvd.1 hmod
  obtain ⟨k, hk⟩ := hdvd
  have hR1 : -wrapP < R := lt_of_lt_of_le hlo h1
  have hR2 : R < wrapP := lt_of_le_of_lt h2 hhi
  rw [hk] at hR1 hR2
  have hk0 : k = 0 := by unfold wrapP at hR1 hR2; omega
  rw [hk, hk0, mul_zero]

/-- **SAFE is a THEOREM (explicit-range).** If `exprInterval` returns `[lo,hi] ⊂ (-p,p)` and the range
teeth hold, then the gate body cannot wrap: `body ≡ 0 [ZMOD p] ⟹ body = 0` over ℤ. No heuristic. -/
theorem exprInterval_safe_no_wrap (ranges : List VmRange) (a : Assignment)
    (hR : ∀ r ∈ ranges, 0 ≤ a r.wire ∧ a r.wire < (2 : ℤ) ^ r.bits)
    (e : EmittedExpr) (lo hi : ℤ)
    (hI : exprInterval ranges e = some (lo, hi))
    (hsafe : hi < wrapP ∧ -wrapP < lo)
    (hmod : e.eval a ≡ 0 [ZMOD wrapP]) : e.eval a = 0 := by
  obtain ⟨hb1, hb2⟩ := intervalW_sound (rangeBound ranges) a (rangeBound_hyp ranges a hR) e lo hi hI
  exact safe_no_wrap hsafe.2 hsafe.1 hb1 hb2 hmod

/-- **SAFE is a THEOREM (field-aware).** The canonical-felt companion: under the standing felt
invariant, a `[lo,hi] ⊂ (-p,p)` from `exprIntervalF` proves no wrap. -/
theorem exprIntervalF_safe_no_wrap (ranges : List VmRange) (a : Assignment)
    (hR : ∀ r ∈ ranges, 0 ≤ a r.wire ∧ a r.wire < (2 : ℤ) ^ r.bits)
    (hCanon : ∀ c, 0 ≤ a c ∧ a c ≤ wrapP - 1)
    (e : EmittedExpr) (lo hi : ℤ)
    (hI : exprIntervalF ranges e = some (lo, hi))
    (hsafe : hi < wrapP ∧ -wrapP < lo)
    (hmod : e.eval a ≡ 0 [ZMOD wrapP]) : e.eval a = 0 := by
  obtain ⟨hb1, hb2⟩ :=
    intervalW_sound (fieldBound ranges) a (fieldBound_hyp ranges a hR hCanon) e lo hi hI
  exact safe_no_wrap hsafe.2 hsafe.1 hb1 hb2 hmod

/-! ## §5 — Verdicts and the per-descriptor scan. -/

/-- The wrap verdict for a gate. -/
inductive WrapVerdict where
  /-- Residual `⊂ (-p,p)`: `≡0 mod p ⟺ =0`. A THEOREM (`…_safe_no_wrap`). -/
  | safe
  /-- Residual can reach a nonzero multiple of `p` (the reconstruction/sum wrap class). -/
  | suspect
  /-- A column feeding the residual is unbounded (no range) ⟹ interval unbounded. -/
  | unranged
  /-- Not a single-row arithmetic gate (transition / PI-binding / interaction-bus / two-row window):
  outside this analyzer's single-row-reconstruction scope. -/
  | notGate
  deriving Repr, DecidableEq

/-- Classify an interval: `none` ⟹ UNRANGED, `⊂(-p,p)` ⟹ SAFE, else SUSPECT. -/
def intervalVerdict : Option (ℤ × ℤ) → WrapVerdict
  | none => .unranged
  | some (lo, hi) => if hi < wrapP ∧ -wrapP < lo then .safe else .suspect

/-- The residual EXPRESSION of a v1 constraint, if it is a single-row arithmetic gate. `transition`
and `piBinding` are column-continuity / PI equalities (a difference of two individually-pinned felts,
not a value reconstruction) — outside scope, `none`. -/
def residualExpr : VmConstraint → Option EmittedExpr
  | .gate body       => some body
  | .boundary _ body => some body
  | .transition _ _  => none
  | .piBinding _ _ _ => none

/-- **`gateWrapSafe` — the task-spec per-gate verdict** (explicit-range). -/
def gateWrapSafe (d : EffectVmDescriptor2) (c : VmConstraint) : WrapVerdict :=
  match residualExpr c with
  | none => .notGate
  | some e => intervalVerdict (exprInterval d.ranges e)

/-- The field-aware per-gate verdict (canonical-felt oracle). -/
def gateWrapSafeF (d : EffectVmDescriptor2) (c : VmConstraint) : WrapVerdict :=
  match residualExpr c with
  | none => .notGate
  | some e => intervalVerdict (exprIntervalF d.ranges e)

/-- **A SAFE verdict from `gateWrapSafe` is a proof of no-wrap** for the gate body. -/
theorem gateWrapSafe_sound (d : EffectVmDescriptor2) (body : EmittedExpr) (a : Assignment)
    (hR : ∀ r ∈ d.ranges, 0 ≤ a r.wire ∧ a r.wire < (2 : ℤ) ^ r.bits)
    (hsafe : gateWrapSafe d (.gate body) = .safe)
    (hmod : body.eval a ≡ 0 [ZMOD wrapP]) : body.eval a = 0 := by
  simp only [gateWrapSafe, residualExpr] at hsafe
  rcases hI : exprInterval d.ranges body with _ | ⟨lo, hi⟩
  · rw [hI] at hsafe; simp [intervalVerdict] at hsafe
  · rw [hI] at hsafe
    simp only [intervalVerdict] at hsafe
    by_cases hc : hi < wrapP ∧ -wrapP < lo
    · exact exprInterval_safe_no_wrap d.ranges a hR body lo hi hI hc hmod
    · rw [if_neg hc] at hsafe; exact absurd hsafe (by decide)

/-- Classify one v2 constraint (explicit-range). Interaction-bus and two-row window kinds are outside
the single-row-gate scope (`arithResidual = 0` for the bus kinds; window is a two-row primitive). -/
def constraintVerdict (ranges : List VmRange) : VmConstraint2 → WrapVerdict
  | .base c       => match residualExpr c with
                     | none => .notGate
                     | some e => intervalVerdict (exprInterval ranges e)
  | .windowGate _ => .notGate
  | .lookup _     => .notGate
  | .memOp _      => .notGate
  | .mapOp _      => .notGate
  | .umemOp _     => .notGate
  | .proofBind _  => .notGate

/-- Field-aware v2 classifier. -/
def constraintVerdictF (ranges : List VmRange) : VmConstraint2 → WrapVerdict
  | .base c       => match residualExpr c with
                     | none => .notGate
                     | some e => intervalVerdict (exprIntervalF ranges e)
  | _             => .notGate

/-- **`descriptorWrapReport` — the per-descriptor scan** (explicit-range): `(constraint-index, verdict)`. -/
def descriptorWrapReport (d : EffectVmDescriptor2) : List (Nat × WrapVerdict) :=
  d.constraints.mapIdx (fun i c => (i, constraintVerdict d.ranges c))

/-- The field-aware scan. -/
def descriptorWrapReportF (d : EffectVmDescriptor2) : List (Nat × WrapVerdict) :=
  d.constraints.mapIdx (fun i c => (i, constraintVerdictF d.ranges c))

/-- Findings only: drop the SAFE / not-a-gate rows (field-aware — the crisp security view). -/
def wrapFindingsF (d : EffectVmDescriptor2) : List (Nat × WrapVerdict) :=
  (descriptorWrapReportF d).filter (fun p => p.2 == .suspect || p.2 == .unranged)

/-- Count `(safe, suspect, unranged, notGate)` over a report. -/
def wrapSummary (rep : List (Nat × WrapVerdict)) : Nat × Nat × Nat × Nat :=
  rep.foldl (fun (acc : Nat × Nat × Nat × Nat) p =>
    match p.2 with
    | .safe     => (acc.1 + 1, acc.2.1, acc.2.2.1, acc.2.2.2)
    | .suspect  => (acc.1, acc.2.1 + 1, acc.2.2.1, acc.2.2.2)
    | .unranged => (acc.1, acc.2.1, acc.2.2.1 + 1, acc.2.2.2)
    | .notGate  => (acc.1, acc.2.1, acc.2.2.1, acc.2.2.2 + 1)) (0, 0, 0, 0)

/-! ## §6 — GROUND-TRUTH VALIDATION (`#guard` = the analyzer AGREES with the hand audit). -/

/-- Gap #4 minimal repro (PRE-FIX shape): the debit residual `after − before − amount`
(`after = var 0` ranged 30-bit, `before = var 1`, `amount = var 2` UNRANGED). The exact `gBalLo`
shape the audit flagged (`WRAP-CLASS-AUDIT.md §4`). -/
def gap4Body : EmittedExpr :=
  .add (.var 0) (.add (.mul (.const (-1)) (.var 1)) (.mul (.const (-1)) (.var 2)))
def gap4Ranges : List VmRange := [⟨0, 30⟩]

-- Explicit-range analyzer: unranged `before`/`amount` ⟹ UNRANGED (the audit's "amount not ranged").
#guard exprInterval gap4Ranges gap4Body == none
#guard intervalVerdict (exprInterval gap4Ranges gap4Body) == .unranged
-- Field-aware: canonical felts, sum of 3 felts reaches `2p` ⟹ SUSPECT (the wrap forgery exists).
#guard intervalVerdict (exprIntervalF gap4Ranges gap4Body) == .suspect

/-- FIXED local shape (audit fix option (a)): range-check `after`/`before`/`amount` to ≤ 29 bits, so
`after − before − amount ∈ (−2³⁰, 2²⁹) ⊂ (−p, p)` — `0` the only multiple of `p`. -/
def fixedRanges : List VmRange := [⟨0, 29⟩, ⟨1, 29⟩, ⟨2, 29⟩]
#guard intervalVerdict (exprInterval fixedRanges gap4Body) == .safe
#guard intervalVerdict (exprIntervalF fixedRanges gap4Body) == .safe

/-- Boolean gate `x·(x−1)` with `x` ranged 1-bit (`x ∈ {0,1}`) ⟹ residual `∈ [−1,0] ⊂ (−p,p)` ⟹ SAFE. -/
def boolBody : EmittedExpr := .mul (.var 0) (.add (.var 0) (.const (-1)))
def boolRanges : List VmRange := [⟨0, 1⟩]
#guard intervalVerdict (exprInterval boolRanges boolBody) == .safe

/-- Multiplicative reconstruction `(a+b)·c` with 30-bit ranges: `≈ 2⁶¹ ≫ p` ⟹ SUSPECT. -/
def mulBigBody : EmittedExpr := .mul (.add (.var 0) (.var 1)) (.var 2)
def mulBigRanges : List VmRange := [⟨0, 30⟩, ⟨1, 30⟩, ⟨2, 30⟩]
#guard intervalVerdict (exprInterval mulBigRanges mulBigBody) == .suspect

/-! ## §7 — ★ THE DEPLOYED SCAN — run the analyzer across real effect descriptors. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor transferVmDescriptorAvail)
open Dregg2.Circuit.Emit.EffectVmEmitBurn (burnVmDescriptor)

/-- The deployed transfer descriptor (gap #4 lives in `gBalLo`, constraint index 0). -/
def dTransfer : EffectVmDescriptor2 := embedV1 transferVmDescriptor
/-- The hardened transfer descriptor (borrow/carry availability weld appended). -/
def dTransferAvail : EffectVmDescriptor2 := embedV1 transferVmDescriptorAvail
/-- The deployed burn descriptor (debit rides the same `bal_lo` shape). -/
def dBurn : EffectVmDescriptor2 := embedV1 burnVmDescriptor

-- Field-aware findings (SUSPECT/UNRANGED only) — the security payoff view:
#eval wrapFindingsF dTransfer
#eval wrapFindingsF dTransferAvail
#eval wrapFindingsF dBurn

-- Summaries `(safe, suspect, unranged, notGate)`:
#eval wrapSummary (descriptorWrapReportF dTransfer)
#eval wrapSummary (descriptorWrapReportF dTransferAvail)
#eval wrapSummary (descriptorWrapReportF dBurn)

-- Explicit-range (task-spec) full reports:
#eval descriptorWrapReport dTransfer
#eval descriptorWrapReport dBurn

/-! ## §8 — Axiom hygiene: the analyzer soundness rests on nothing but the Lean/Mathlib core. -/

#assert_axioms mulI_sound
#assert_axioms intervalW_sound
#assert_axioms exprInterval_sound
#assert_axioms safe_no_wrap
#assert_axioms exprInterval_safe_no_wrap
#assert_axioms exprIntervalF_safe_no_wrap
#assert_axioms gateWrapSafe_sound

end Dregg2.Circuit.WrapSafetyStaticAnalyzer
