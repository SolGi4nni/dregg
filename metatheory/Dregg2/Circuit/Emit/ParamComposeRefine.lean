/-
# Dregg2.Circuit.Emit.ParamComposeRefine — the SAT ⟹ SEM bridge for the Lean-authored
parameter-composition AIR (`ParamComposeEmit.paramComposeDesc`).

## What Rung-0 already gave (in `ParamComposeEmit.lean`)

A shape-parametric descriptor whose wire bytes are pinned at `pcMin` (and, in `ParamComposeGolden`,
at the deployed `pcRealistic`). What was MISSING — and what the Rust AIR it replaces could NEVER
have, because there is no formal semantics of Rust — is a machine-checked theorem relating the
EMITTED OBJECT to the composition law. `param-compose/src/reference.rs` calls its Rust twin
"translation validation"; it is not. A Rust `air_accepts` over a co-built witness row is a unit test.

## What THIS file proves

Let `p = 2013265921` (BabyBear). On any TRANSITION row of any trace satisfying the descriptor:

* **THE LAW (`paramCompose_refines_law`)** — the keystone:

      outcome ≡ Σ_{t<l} coeff_t · val_t  +  Σ_{t<k} coeff_t · valA_t · valB_t   [ZMOD p]

  composed from the outcome gate, the `l` linear-contribution gates and the `k` knot gates. The
  second sum is the DEGREE-3 term — the product of two subjects' state values, precisely what the
  linear `AffineLe`/`AffineEq` vocabulary cannot express and the whole reason a Custom VK exists.

* **THE FETCH (`fetch_resolves`)** — a satisfying trace's fetched value is not the prover's choice.
  Under a one-hot selection at `(j, q)` the emitted gates force ALL FIVE of: the read value is
  `params[j][q]`; subject `j`'s role tag equals the term's ADDRESSED role; subject `j` is ACTIVE;
  the param index `q` equals the term's addressed param slot; and slot `q` is within `param_count`.
  That is the anti-malleability content of "resolution BY ROLE, never by slot index".

* **THE ONE-HOT IS FORCED (`sel_oneHot_of_sat` / `selP_oneHot_of_sat`)** — the envelope above is not
  assumed: the emitted boolean pins plus the `Σ sel = term_active` gate FORCE it, over ℤ, from the
  deployed range-check canonicality (`Canon`) and BabyBear primality. `boolSum_one_unique` is the
  combinatorial core. The side condition is the honest one — `S.n < p` / `S.p < p`, satisfied by
  every realizable shape by a factor of ~10^8.

* **A ROLE IS A KEY (`role_key_of_sat`)** — two DISTINCT ACTIVE subject slots cannot carry the same
  role tag. With `fetch_resolves` this is what makes `role ↦ subject` a FUNCTION, so the outcome is
  not prover-malleable.

* **THE KNOT IS LOAD-BEARING (`knot_neuter_rejected`)** — a trace that zeroes a knot contribution
  while its factors are nonzero has NO satisfying witness. This is the in-circuit twin of the Rust
  `Forgery::neuter_knots` canary, as a THEOREM rather than a test case.

## Honest coverage boundary (read this before deleting anything)

COVERED by a proven theorem here (each with `#assert_axioms`): the outcome gate (`outcome_is_sum`),
both contribution forms (`lContrib_eq` / `kContrib_eq`), the composed law
(`paramCompose_refines_law`), the two subject/param one-hot forcings (`sel_oneHot_of_sat` /
`selP_oneHot_of_sat`), all five conclusions of the fetch (`fetch_resolves`, which consumes the F2/F3
role+activity gates, the F5/F6 index+range gates and the F7 degree-3 read), the role-key tooth
(`role_key_of_sat`, which consumes all three gates of a pair), and the knot canary
(`knot_neuter_rejected`).

EMITTED but NOT yet refined here (named, not laundered):

  1. **The digest chains.** The four `node8` Merkle–Damgård chains are EMITTED (§11 of the emit
     file, one wide chip lookup per 8-felt block) and the lever they consume
     (`chip_lookup_sound_N`) is already proven in `DescriptorIR2`. The chained induction
     "root = fold of the stream" — the `MultiStepChainRefine.acc_chain` shape — is NOT assembled
     here. So `subjects_root`/`ruleset_root`/`outcome_commitment`/`explanation_root` are bound to
     PIs by emitted constraints, but this file does not yet prove they are the genuine digests.
  2. **The ordering tooth's non-vacuity.** `forcedGe0` is emitted with the range gadget and the
     `forcedGe0Term_eval` branch lemmas are proven in `AirBuilder`; the ℤ-level argument that
     `id[i+1] > id[i]` follows (which is where the `identity_bits ≤ 28` margin is consumed) is NOT
     assembled here.
  3. **The subject-activity prefix / count pins and the three param/subject inactive⇒zero pins.**
     Emitted (§4/§5 of the emit file); the "active is a prefix of length `subject_count`" and
     "absence is committed as zero" corollaries are not stated here.
  4. **A concrete `Satisfied2` WITNESS.** §7 checks, by evaluation on a concrete honest row, that all
     86 emitted algebraic gates vanish and all 37 PI bindings close — so the gate set is genuinely
     SATISFIABLE and none of the theorems below is vacuous-by-contradiction. What is NOT here is the
     assembled `Satisfied2` term of the `MultiStepChainRefine.wTrace_satisfied2` kind (it needs a
     per-form bulk lemma, because `VmConstraint2.holdsAt`'s `mapOp` arm blocks a plain `decide`).

## Axiom hygiene

`#assert_axioms` on every keystone. The only carriers are `propext`/`Classical.choice`/`Quot.sound`;
the sole imported field fact is the BabyBear primality `pPrimeInt`
(`EffectVmEmitTransfer`), used exactly where a booleanity gate is lifted from mod-`p` to ℤ.
NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.ParamComposeEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.ParamComposeRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (Satisfied2 VmTrace TraceFamily VmConstraint2 EffectVmDescriptor2 envAt zeroAsg)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.ParamComposeEmit

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §0 — Field glue.

Gates bind CONGRUENCES mod the BabyBear prime; that is the faithful field semantics (the Rust host
twin maps every value through `fb : i128 → BabyBear`, a ring homomorphism), so the LAW is stated
mod `p` and needs no lift. Only the BOOLEANITY of a selector needs ℤ, and it is recovered from the
deployed range-check canonicality plus primality. -/

/-- The deployed range-check invariant on a stored field cell. -/
def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- A booleanity gate that vanishes mod `p` on a CANONICAL cell pins it to `0` or `1` over ℤ. -/
theorem bin_of_gate {a : Assignment} {c : Nat}
    (h : (gBin c).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) : a c = 0 ∨ a c = 1 := by
  simp only [gBin, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + (-1)) := Int.modEq_zero_iff_dvd.mp h
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- Pointwise congruence lifts to the sums. -/
theorem sum_modEq {α : Type} (xs : List α) (f g : α → ℤ)
    (h : ∀ x ∈ xs, f x ≡ g x [ZMOD 2013265921]) :
    (xs.map f).sum ≡ (xs.map g).sum [ZMOD 2013265921] := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Int.ModEq.add (h a (List.mem_cons_self)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## §1 — Gate extraction from `Satisfied2`. -/

section Extraction
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace}

/-- The row assignment at index `i`. -/
def rowOf (t : VmTrace) (i : Nat) : Assignment := (envAt t i).loc

/-- **Any emitted `Head` gate forces its head to vanish mod `p` on a transition row.** This is the
one place the lowering is unfolded; every theorem below is stated on `evalH`. -/
theorem pcGate {S : ComposeShape}
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {h : Head}
    (hm : cgH h ∈ (paramComposeDesc S).constraints) :
    evalH h (rowOf t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [cgH, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  rwa [headToExpr_eval] at hb

/-- The booleanity form of `pcGate`. -/
theorem pcBin {S : ComposeShape}
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {c : Nat}
    (hm : binGate c ∈ (paramComposeDesc S).constraints) (hcan : Canon (rowOf t i c)) :
    rowOf t i c = 0 ∨ rowOf t i c = 1 := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (gBin c).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [binGate, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  exact bin_of_gate hb hcan

end Extraction

/-! ## §2 — Membership: each gate family sits inside the emitted constraint list.

`paramComposeConstraints` is a left-associated chain of `++`; `List.mem_append` turns membership into
a nested disjunction and `tauto` places the family. Each lemma below is the ONLY place the emission
order is relied on, so a re-ordering of §13 breaks these and nothing else. -/

section Membership
variable (S : ComposeShape) {x : VmConstraint2}

theorem mem_subject {i : Nat} (hi : i < S.n) (hx : x ∈ subjectGates S i) :
    x ∈ (paramComposeDesc S).constraints := by
  have h1 : x ∈ (List.range S.n).flatMap (fun i => subjectGates S i) :=
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hx⟩
  simp only [paramComposeDesc, paramComposeConstraints, List.mem_append]
  tauto

theorem mem_roleKey {τ : Nat} {ij : Nat × Nat} (hτ : (ij, τ) ∈ S.pairList.zipIdx)
    (hx : x ∈ roleKeyGates S τ ij.1 ij.2) : x ∈ (paramComposeDesc S).constraints := by
  have h1 : x ∈ S.pairList.zipIdx.flatMap
      (fun (e : (Nat × Nat) × Nat) => roleKeyGates S e.2 e.1.1 e.1.2) :=
    List.mem_flatMap.mpr ⟨(ij, τ), hτ, hx⟩
  simp only [paramComposeDesc, paramComposeConstraints, List.mem_append]
  tauto

theorem mem_linear {τ : Nat} (hτ : τ < S.l) (hx : x ∈ linearGates S τ) :
    x ∈ (paramComposeDesc S).constraints := by
  have h1 : x ∈ (List.range S.l).flatMap (fun τ => linearGates S τ) :=
    List.mem_flatMap.mpr ⟨τ, List.mem_range.mpr hτ, hx⟩
  simp only [paramComposeDesc, paramComposeConstraints, List.mem_append]
  tauto

theorem mem_knot {τ : Nat} (hτ : τ < S.k) (hx : x ∈ knotGates S τ) :
    x ∈ (paramComposeDesc S).constraints := by
  have h1 : x ∈ (List.range S.k).flatMap (fun τ => knotGates S τ) :=
    List.mem_flatMap.mpr ⟨τ, List.mem_range.mpr hτ, hx⟩
  simp only [paramComposeDesc, paramComposeConstraints, List.mem_append]
  tauto

theorem mem_law : lawGate S ∈ (paramComposeDesc S).constraints := by
  have h1 : lawGate S ∈ [lawGate S] := List.mem_singleton_self _
  simp only [paramComposeDesc, paramComposeConstraints, List.mem_append]
  tauto

end Membership

/-! ### The individual gates, inside their family lists. -/

/-- The linear contribution head `−contrib + coeff · value`. -/
def lContribHead (S : ComposeShape) (τ : Nat) : Head :=
  (Head.lin (-1) (S.lContrib τ)).addProd 1 [S.lCoeff τ, S.fVal (S.lFet τ)]

/-- The knot contribution head `contrib − coeff · valA · valB` — THE NONLINEARITY. -/
def kContribHead (S : ComposeShape) (τ : Nat) : Head :=
  (Head.lin 1 (S.kContrib τ)).addProd (-1)
    [S.kCoeff τ, S.fVal (S.kFetA τ), S.fVal (S.kFetB τ)]

theorem lContrib_in_family (S : ComposeShape) (τ : Nat) :
    cgH (lContribHead S τ) ∈ linearGates S τ :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem kContrib_in_family (S : ComposeShape) (τ : Nat) :
    cgH (kContribHead S τ) ∈ knotGates S τ :=
  List.mem_append_right _ (List.mem_singleton_self _)

/-! ## §3 — THE LAW. -/

section Law
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {S : ComposeShape}

/-- The outcome column is the SUM of the committed per-term contributions. -/
theorem outcome_is_sum
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) :
    rowOf t i S.cOut
      ≡ ((List.range S.l).map (fun τ => rowOf t i (S.lContrib τ))).sum
      + ((List.range S.k).map (fun τ => rowOf t i (S.kContrib τ))).sum [ZMOD 2013265921] := by
  have hg := pcGate hsat i hi (mem_law S)
  have hval : evalH (lawHead S) (rowOf t i)
      = rowOf t i S.cOut
        - ((List.range S.l).map (fun τ => rowOf t i (S.lContrib τ))).sum
        - ((List.range S.k).map (fun τ => rowOf t i (S.kContrib τ))).sum := by
    simp only [lawHead, evalH_foldl_addLinF, evalH_lin]
    ring
  rw [hval] at hg
  have hd := Int.modEq_iff_dvd.mp hg
  refine Int.modEq_iff_dvd.mpr ?_
  have hrw : (((List.range S.l).map (fun τ => rowOf t i (S.lContrib τ))).sum
        + ((List.range S.k).map (fun τ => rowOf t i (S.kContrib τ))).sum)
      - rowOf t i S.cOut
      = 0 - (rowOf t i S.cOut
        - ((List.range S.l).map (fun τ => rowOf t i (S.lContrib τ))).sum
        - ((List.range S.k).map (fun τ => rowOf t i (S.kContrib τ))).sum) := by ring
  rw [hrw]
  exact hd

/-- A linear term's contribution IS `coeff · value`. -/
theorem lContrib_eq
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {τ : Nat} (hτ : τ < S.l) :
    rowOf t i (S.lContrib τ)
      ≡ rowOf t i (S.lCoeff τ) * rowOf t i (S.fVal (S.lFet τ)) [ZMOD 2013265921] := by
  have hg := pcGate hsat i hi (mem_linear S hτ (lContrib_in_family S τ))
  simp only [lContribHead, evalH_addProd, evalH_lin, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil] at hg
  have := Int.ModEq.add_right (rowOf t i (S.lContrib τ)) hg
  simp only [rowOf] at *
  have h2 : -1 * (envAt t i).loc (S.lContrib τ)
      + 1 * ((envAt t i).loc (S.lCoeff τ) * ((envAt t i).loc (S.fVal (S.lFet τ)) * 1))
      + (envAt t i).loc (S.lContrib τ)
      = (envAt t i).loc (S.lCoeff τ) * (envAt t i).loc (S.fVal (S.lFet τ)) := by ring
  rw [h2, zero_add] at this
  exact this.symm

/-- **THE KNOT.** A knot's contribution IS `coeff · valA · valB` — the degree-3 product of two
subjects' state values. -/
theorem kContrib_eq
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {τ : Nat} (hτ : τ < S.k) :
    rowOf t i (S.kContrib τ)
      ≡ rowOf t i (S.kCoeff τ) * rowOf t i (S.fVal (S.kFetA τ))
        * rowOf t i (S.fVal (S.kFetB τ)) [ZMOD 2013265921] := by
  have hg := pcGate hsat i hi (mem_knot S hτ (kContrib_in_family S τ))
  simp only [kContribHead, evalH_addProd, evalH_lin, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil] at hg
  have := Int.ModEq.add_right
    (rowOf t i (S.kCoeff τ) * rowOf t i (S.fVal (S.kFetA τ)) * rowOf t i (S.fVal (S.kFetB τ))) hg
  simp only [rowOf] at *
  have h2 : (1 : ℤ) * (envAt t i).loc (S.kContrib τ)
      + -1 * ((envAt t i).loc (S.kCoeff τ) * ((envAt t i).loc (S.fVal (S.kFetA τ))
          * ((envAt t i).loc (S.fVal (S.kFetB τ)) * 1)))
      + (envAt t i).loc (S.kCoeff τ) * (envAt t i).loc (S.fVal (S.kFetA τ))
        * (envAt t i).loc (S.fVal (S.kFetB τ))
      = (envAt t i).loc (S.kContrib τ) := by ring
  rw [h2, zero_add] at this
  exact this

/-- **THE KEYSTONE — `paramCompose_refines_law`.** A trace satisfying the emitted descriptor has its
outcome column equal, mod the BabyBear prime, to the composition the ruleset licenses: the sum of the
linear terms' `coeff · value` plus the sum of the knots' `coeff · valueA · valueB`. The knot sum is
the DEGREE-3 part — the product of two subjects' state values, which no linear `StateConstraint`
vocabulary can express, and the entire reason this Custom VK exists.

This composes the outcome gate with all `l` linear-contribution gates and all `k` knot gates. It is
the statement the hand-written Rust AIR could never carry: `air_accepts` evaluates ONE co-built row,
and a Rust case test proves nothing about all inputs. -/
theorem paramCompose_refines_law
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) :
    rowOf t i S.cOut
      ≡ ((List.range S.l).map
            (fun τ => rowOf t i (S.lCoeff τ) * rowOf t i (S.fVal (S.lFet τ)))).sum
      + ((List.range S.k).map
            (fun τ => rowOf t i (S.kCoeff τ) * rowOf t i (S.fVal (S.kFetA τ))
                      * rowOf t i (S.fVal (S.kFetB τ)))).sum [ZMOD 2013265921] := by
  refine (outcome_is_sum hsat i hi).trans (Int.ModEq.add ?_ ?_)
  · exact sum_modEq _ _ _ fun τ hτ => lContrib_eq hsat i hi (List.mem_range.mp hτ)
  · exact sum_modEq _ _ _ fun τ hτ => kContrib_eq hsat i hi (List.mem_range.mp hτ)

end Law

/-! ## §4 — Selector combinatorics: what a boolean one-hot forces. -/

/-- A sum of terms that vanish off index `j` IS the `j`-th term. -/
theorem sum_zero_of_all (F : Nat → ℤ) :
    ∀ n, (∀ j, j < n → F j = 0) → ((List.range n).map F).sum = 0 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro h
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ih (fun j hj => h j (by omega)), h m (by omega)]
    ring

theorem sum_index (F : Nat → ℤ) (j : Nat) :
    ∀ n, j < n → (∀ j', j' < n → j' ≠ j → F j' = 0) → ((List.range n).map F).sum = F j := by
  intro n
  induction n with
  | zero => intro hj; omega
  | succ m ih =>
    intro hj h
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    by_cases hjm : j = m
    · subst hjm
      rw [sum_zero_of_all F j (fun j' hj' => h j' (by omega) (by omega))]
      ring
    · have hjlt : j < m := by omega
      rw [ih hjlt (fun j' hj' hne => h j' (by omega) hne), h m (by omega) (by omega)]
      ring

/-- **A gated one-hot READS**: `Σ_j sel_j · g j = g j₀` when `sel` is the indicator of `j₀`. -/
theorem sum_oneHot (sel g : Nat → ℤ) (j n : Nat) (hj : j < n)
    (h : ∀ j', j' < n → sel j' = if j' = j then 1 else 0) :
    ((List.range n).map (fun j' => sel j' * g j')).sum = g j := by
  rw [sum_index (fun j' => sel j' * g j') j n hj
        (fun j' hj' hne => by
          show sel j' * g j' = 0
          rw [h j' hj', if_neg hne]; ring)]
  show sel j * g j = g j
  rw [h j hj, if_pos rfl]; ring

/-- Booleans sum to a NON-NEGATIVE integer. -/
theorem boolSum_nonneg (f : Nat → ℤ) :
    ∀ n, (∀ j, j < n → f j = 0 ∨ f j = 1) → 0 ≤ ((List.range n).map f).sum := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro hb
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    have h1 := ih (fun j hj => hb j (by omega))
    have h2 : 0 ≤ f m := by rcases hb m (by omega) with h | h <;> omega
    omega

/-- Booleans sum to at most the slot count. -/
theorem boolSum_le (f : Nat → ℤ) :
    ∀ n, (∀ j, j < n → f j = 0 ∨ f j = 1) → ((List.range n).map f).sum ≤ (n : ℤ) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro hb
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    have h1 := ih (fun j hj => hb j (by omega))
    have h2 : f m ≤ 1 := by rcases hb m (by omega) with h | h <;> omega
    push_cast
    omega

/-- Booleans summing to `0` are ALL zero. -/
theorem boolSum_zero_all (f : Nat → ℤ) :
    ∀ n, (∀ j, j < n → f j = 0 ∨ f j = 1) → ((List.range n).map f).sum = 0 →
      ∀ j, j < n → f j = 0 := by
  intro n
  induction n with
  | zero => intro _ _ j hj; omega
  | succ m ih =>
    intro hb hs
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at hs
    have h1 := boolSum_nonneg f m (fun j hj => hb j (by omega))
    have h2 : 0 ≤ f m := by rcases hb m (by omega) with h | h <;> omega
    have hm : f m = 0 := by omega
    have hsm : ((List.range m).map f).sum = 0 := by omega
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact ih (fun j' hj' => hb j' (by omega)) hsm j h
    · subst h; exact hm

/-- **THE ONE-HOT CORE.** Boolean selectors summing to `1` are the indicator of a UNIQUE index. This
is what turns "the prover witnessed some selectors" into "the prover selected exactly one slot". -/
theorem boolSum_one_unique (f : Nat → ℤ) :
    ∀ n, (∀ j, j < n → f j = 0 ∨ f j = 1) → ((List.range n).map f).sum = 1 →
      ∃ j, j < n ∧ ∀ j', j' < n → f j' = if j' = j then 1 else 0 := by
  intro n
  induction n with
  | zero => intro _ hs; simp at hs
  | succ m ih =>
    intro hb hs
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at hs
    rcases hb m (by omega) with hm | hm
    · have hsm : ((List.range m).map f).sum = 1 := by omega
      obtain ⟨j, hj, hall⟩ := ih (fun j' hj' => hb j' (by omega)) hsm
      refine ⟨j, by omega, ?_⟩
      intro j' hj'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
      · exact hall j' h
      · subst h; rw [hm, if_neg (by omega)]
    · have hsm : ((List.range m).map f).sum = 0 := by omega
      have hall := boolSum_zero_all f m (fun j' hj' => hb j' (by omega)) hsm
      refine ⟨m, by omega, ?_⟩
      intro j' hj'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
      · rw [hall j' h, if_neg (by omega)]
      · subst h; rw [hm, if_pos rfl]

/-- Two canonical field cells congruent mod `p` are EQUAL over ℤ. -/
theorem eq_of_modEq_canon {a b : ℤ} (ha : Canon a) (hb : Canon b)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨kk, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

/-- A residual that vanishes mod `p` IS a congruence. -/
theorem modEq_of_sub_zero {a b : ℤ} (h : a - b ≡ 0 [ZMOD 2013265921]) :
    a ≡ b [ZMOD 2013265921] := by
  have h2 := Int.ModEq.add_right b h
  simpa using h2

/-! ## §5 — THE FETCH: resolution BY ROLE is forced, not chosen. -/

/-- The nine gate families of one fetch block are all present in the emitted descriptor. -/
def FetchEmitted (S : ComposeShape) (fb ta rc pc : Nat) : Prop :=
  (∀ j, j < S.n → binGate (S.fSel fb j) ∈ (paramComposeDesc S).constraints)
  ∧ (∀ q, q < S.p → binGate (S.fSelP fb q) ∈ (paramComposeDesc S).constraints)
  ∧ cgH (fSumHead S fb ta) ∈ (paramComposeDesc S).constraints
  ∧ cgH (fRoleHead S fb ta rc) ∈ (paramComposeDesc S).constraints
  ∧ cgH (fActiveHead S fb ta) ∈ (paramComposeDesc S).constraints
  ∧ cgH (fpSumHead S fb ta) ∈ (paramComposeDesc S).constraints
  ∧ cgH (fpIdxHead S fb ta pc) ∈ (paramComposeDesc S).constraints
  ∧ cgH (fpActiveHead S fb ta) ∈ (paramComposeDesc S).constraints
  ∧ cgH (fReadHead S fb) ∈ (paramComposeDesc S).constraints

section FetchMem
variable (S : ComposeShape) (fb ta rc pc : Nat)

theorem selBin_in {j : Nat} (hj : j < S.n) :
    binGate (S.fSel fb j) ∈ fetchGates S fb ta rc pc := by
  have h1 : binGate (S.fSel fb j) ∈ (List.range S.n).map (fun j => binGate (S.fSel fb j)) :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [fetchGates, List.mem_append]
  tauto

theorem selPBin_in {q : Nat} (hq : q < S.p) :
    binGate (S.fSelP fb q) ∈ fetchGates S fb ta rc pc := by
  have h1 : binGate (S.fSelP fb q) ∈ (List.range S.p).map (fun q => binGate (S.fSelP fb q)) :=
    List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩
  simp only [fetchGates, List.mem_append]
  tauto

theorem fetchHeads_in :
    cgH (fSumHead S fb ta) ∈ fetchGates S fb ta rc pc
    ∧ cgH (fRoleHead S fb ta rc) ∈ fetchGates S fb ta rc pc
    ∧ cgH (fActiveHead S fb ta) ∈ fetchGates S fb ta rc pc
    ∧ cgH (fpSumHead S fb ta) ∈ fetchGates S fb ta rc pc
    ∧ cgH (fpIdxHead S fb ta pc) ∈ fetchGates S fb ta rc pc
    ∧ cgH (fpActiveHead S fb ta) ∈ fetchGates S fb ta rc pc
    ∧ cgH (fReadHead S fb) ∈ fetchGates S fb ta rc pc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fetchGates, List.mem_append, List.mem_cons, List.mem_singleton]; tauto)

/-- Every fetch gate of a block whose family sits in the descriptor is itself in the descriptor. -/
theorem fetchEmitted_of_sub
    (hsub : ∀ x ∈ fetchGates S fb ta rc pc, x ∈ (paramComposeDesc S).constraints) :
    FetchEmitted S fb ta rc pc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := fetchHeads_in S fb ta rc pc
  exact ⟨fun j hj => hsub _ (selBin_in S fb ta rc pc hj),
         fun q hq => hsub _ (selPBin_in S fb ta rc pc hq),
         hsub _ h1, hsub _ h2, hsub _ h3, hsub _ h4, hsub _ h5, hsub _ h6, hsub _ h7⟩

end FetchMem

/-- A LINEAR term's fetch block is emitted. -/
theorem linear_fetchEmitted (S : ComposeShape) {τ : Nat} (hτ : τ < S.l) :
    FetchEmitted S (S.lFet τ) (S.laCol τ) (S.lRole τ) (S.lParam τ) :=
  fetchEmitted_of_sub S _ _ _ _ fun _ hx =>
    mem_linear S hτ (List.mem_append_left _ (List.mem_append_right _ hx))

/-- A KNOT's LEFT fetch block is emitted. -/
theorem knotA_fetchEmitted (S : ComposeShape) {τ : Nat} (hτ : τ < S.k) :
    FetchEmitted S (S.kFetA τ) (S.kaCol τ) (S.kRoleA τ) (S.kParA τ) :=
  fetchEmitted_of_sub S _ _ _ _ fun _ hx =>
    mem_knot S hτ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx)))

/-- A KNOT's RIGHT fetch block is emitted. -/
theorem knotB_fetchEmitted (S : ComposeShape) {τ : Nat} (hτ : τ < S.k) :
    FetchEmitted S (S.kFetB τ) (S.kaCol τ) (S.kRoleB τ) (S.kParB τ) :=
  fetchEmitted_of_sub S _ _ _ _ fun _ hx =>
    mem_knot S hτ (List.mem_append_left _ (List.mem_append_right _ hx))

section Fetch
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {S : ComposeShape}

/-- The subject selectors of block `fb` are the indicator of slot `j`. -/
def SelOneHot (t : VmTrace) (i : Nat) (S : ComposeShape) (fb j : Nat) : Prop :=
  j < S.n ∧ ∀ j', j' < S.n → rowOf t i (S.fSel fb j') = if j' = j then 1 else 0

/-- The param selectors of block `fb` are the indicator of slot `q`. -/
def SelPOneHot (t : VmTrace) (i : Nat) (S : ComposeShape) (fb q : Nat) : Prop :=
  q < S.p ∧ ∀ q', q' < S.p → rowOf t i (S.fSelP fb q') = if q' = q then 1 else 0

/-- The deployed range-check envelope on a fetch block's selector columns. -/
def FetchCanon (t : VmTrace) (i : Nat) (S : ComposeShape) (fb : Nat) : Prop :=
  (∀ j, j < S.n → Canon (rowOf t i (S.fSel fb j)))
  ∧ (∀ q, q < S.p → Canon (rowOf t i (S.fSelP fb q)))

/-- **The subject one-hot is FORCED** (not assumed): the emitted boolean pins plus the
`Σ_j sel_j = term_active` gate pin the selectors to the indicator of a unique slot, whenever the term
is active. The `S.n < p` side condition is the honest one — a shape with more subject slots than the
field has elements could wrap the sum; every realizable shape is far below it. -/
theorem sel_oneHot_of_sat {fb ta rc pc : Nat}
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) (hE : FetchEmitted S fb ta rc pc)
    (hcan : FetchCanon t i S fb) (hn : (S.n : ℤ) < 2013265921)
    (hta : rowOf t i ta = 1) :
    ∃ j, SelOneHot t i S fb j := by
  have hbool : ∀ j, j < S.n → rowOf t i (S.fSel fb j) = 0 ∨ rowOf t i (S.fSel fb j) = 1 :=
    fun j hj => pcBin hsat i hi (hE.1 j hj) (hcan.1 j hj)
  have hg := pcGate hsat i hi hE.2.2.1
  have hval : evalH (fSumHead S fb ta) (rowOf t i)
      = -rowOf t i ta + ((List.range S.n).map (fun j => rowOf t i (S.fSel fb j))).sum := by
    simp only [fSumHead, evalH_foldl_addLinF, evalH_lin]; ring
  rw [hval, hta] at hg
  have hmod : ((List.range S.n).map (fun j => rowOf t i (S.fSel fb j))).sum
      ≡ 1 [ZMOD 2013265921] := by
    have hd := Int.modEq_iff_dvd.mp hg
    refine Int.modEq_iff_dvd.mpr ?_
    have hrw : (1 : ℤ) - ((List.range S.n).map (fun j => rowOf t i (S.fSel fb j))).sum
        = 0 - (-1 + ((List.range S.n).map (fun j => rowOf t i (S.fSel fb j))).sum) := by ring
    rw [hrw]; exact hd
  have hlo := boolSum_nonneg (fun j => rowOf t i (S.fSel fb j)) S.n hbool
  have hhi := boolSum_le (fun j => rowOf t i (S.fSel fb j)) S.n hbool
  have hsum : ((List.range S.n).map (fun j => rowOf t i (S.fSel fb j))).sum = 1 :=
    eq_of_modEq_canon ⟨hlo, by omega⟩ ⟨by norm_num, by norm_num⟩ hmod
  obtain ⟨j, hj, hall⟩ := boolSum_one_unique _ S.n hbool hsum
  exact ⟨j, hj, hall⟩

/-- **The param one-hot is FORCED**, by the same argument on `Σ_q selp_q = term_active`. -/
theorem selP_oneHot_of_sat {fb ta rc pc : Nat}
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) (hE : FetchEmitted S fb ta rc pc)
    (hcan : FetchCanon t i S fb) (hp : (S.p : ℤ) < 2013265921)
    (hta : rowOf t i ta = 1) :
    ∃ q, SelPOneHot t i S fb q := by
  have hbool : ∀ q, q < S.p → rowOf t i (S.fSelP fb q) = 0 ∨ rowOf t i (S.fSelP fb q) = 1 :=
    fun q hq => pcBin hsat i hi (hE.2.1 q hq) (hcan.2 q hq)
  have hg := pcGate hsat i hi hE.2.2.2.2.2.1
  have hval : evalH (fpSumHead S fb ta) (rowOf t i)
      = -rowOf t i ta + ((List.range S.p).map (fun q => rowOf t i (S.fSelP fb q))).sum := by
    simp only [fpSumHead, evalH_foldl_addLinF, evalH_lin]; ring
  rw [hval, hta] at hg
  have hmod : ((List.range S.p).map (fun q => rowOf t i (S.fSelP fb q))).sum
      ≡ 1 [ZMOD 2013265921] := by
    have hd := Int.modEq_iff_dvd.mp hg
    refine Int.modEq_iff_dvd.mpr ?_
    have hrw : (1 : ℤ) - ((List.range S.p).map (fun q => rowOf t i (S.fSelP fb q))).sum
        = 0 - (-1 + ((List.range S.p).map (fun q => rowOf t i (S.fSelP fb q))).sum) := by ring
    rw [hrw]; exact hd
  have hlo := boolSum_nonneg (fun q => rowOf t i (S.fSelP fb q)) S.p hbool
  have hhi := boolSum_le (fun q => rowOf t i (S.fSelP fb q)) S.p hbool
  have hsum : ((List.range S.p).map (fun q => rowOf t i (S.fSelP fb q))).sum = 1 :=
    eq_of_modEq_canon ⟨hlo, by omega⟩ ⟨by norm_num, by norm_num⟩ hmod
  obtain ⟨q, hq, hall⟩ := boolSum_one_unique _ S.p hbool hsum
  exact ⟨q, hq, hall⟩

/-- **`fetch_resolves` — THE ANTI-MALLEABILITY KEYSTONE.** For an ACTIVE rule term, the emitted fetch
gates force ALL FIVE of:

  1. the value read IS `params[j][q]` of the selected subject slot;
  2. that subject's ROLE TAG equals the term's ADDRESSED role (resolution is BY ROLE, never by slot
     index — slot order is an identity-sort artifact a ruleset author cannot predict);
  3. that subject is ACTIVE (a role no active subject occupies is UNRESOLVABLE, fail-closed);
  4. the param index equals the term's ADDRESSED param slot;
  5. that param slot is within `param_count` (a slot at or past the schema width is REFUSED).

Together with `role_key_of_sat` (a role is a KEY, so `j` is unique) this is what makes the composed
outcome a FUNCTION of the committed subject list and the committed ruleset, rather than something the
prover gets to choose. -/
theorem fetch_resolves {fb ta rc pc j q : Nat}
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) (hE : FetchEmitted S fb ta rc pc)
    (hj : SelOneHot t i S fb j) (hq : SelPOneHot t i S fb q)
    (hta : rowOf t i ta = 1) :
    rowOf t i (S.fVal fb) ≡ rowOf t i (S.sParam j q) [ZMOD 2013265921]
    ∧ rowOf t i (S.sRole j) ≡ rowOf t i rc [ZMOD 2013265921]
    ∧ rowOf t i (S.sActive j) ≡ 1 [ZMOD 2013265921]
    ∧ (q : ℤ) ≡ rowOf t i pc [ZMOD 2013265921]
    ∧ rowOf t i (S.paCol q) ≡ 1 [ZMOD 2013265921] := by
  obtain ⟨hjlt, hjsel⟩ := hj
  obtain ⟨hqlt, hqsel⟩ := hq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- (1) THE READ: the value is the SELECTED subject's param at the SELECTED slot.
  · have hg := pcGate hsat i hi hE.2.2.2.2.2.2.2.2
    have hinner : ∀ j', j' < S.n →
        ((List.range S.p).map (fun q' =>
            rowOf t i (S.fSel fb j') * (rowOf t i (S.fSelP fb q') *
              (rowOf t i (S.sParam j' q') * 1)))).sum
        = rowOf t i (S.fSel fb j') * rowOf t i (S.sParam j' q) := by
      intro j' _
      calc ((List.range S.p).map (fun q' =>
              rowOf t i (S.fSel fb j') * (rowOf t i (S.fSelP fb q') *
                (rowOf t i (S.sParam j' q') * 1)))).sum
          = ((List.range S.p).map (fun q' =>
              rowOf t i (S.fSelP fb q') *
                (rowOf t i (S.fSel fb j') * rowOf t i (S.sParam j' q')))).sum := by
            congr 1; apply List.map_congr_left; intro q' _; ring
        _ = rowOf t i (S.fSel fb j') * rowOf t i (S.sParam j' q) :=
            sum_oneHot (fun q' => rowOf t i (S.fSelP fb q'))
              (fun q' => rowOf t i (S.fSel fb j') * rowOf t i (S.sParam j' q')) q S.p hqlt hqsel
    have houter : ((List.range S.n).map (fun j' =>
          ((List.range S.p).map (fun q' =>
            rowOf t i (S.fSel fb j') * (rowOf t i (S.fSelP fb q') *
              (rowOf t i (S.sParam j' q') * 1)))).sum)).sum
        = rowOf t i (S.sParam j q) := by
      rw [sum_index _ j S.n hjlt (fun j' hj' hne => by
        show ((List.range S.p).map (fun q' =>
            rowOf t i (S.fSel fb j') * (rowOf t i (S.fSelP fb q') *
              (rowOf t i (S.sParam j' q') * 1)))).sum = 0
        rw [hinner j' hj', hjsel j' hj', if_neg hne]; ring)]
      show ((List.range S.p).map (fun q' =>
          rowOf t i (S.fSel fb j) * (rowOf t i (S.fSelP fb q') *
            (rowOf t i (S.sParam j q') * 1)))).sum = rowOf t i (S.sParam j q)
      rw [hinner j hjlt, hjsel j hjlt, if_pos rfl]; ring
    have hval : evalH (fReadHead S fb) (rowOf t i)
        = ((List.range S.n).map (fun j' =>
            ((List.range S.p).map (fun q' =>
              rowOf t i (S.fSel fb j') * (rowOf t i (S.fSelP fb q') *
                (rowOf t i (S.sParam j' q') * 1)))).sum)).sum
          - rowOf t i (S.fVal fb) := by
      simp only [fReadHead, evalH_addLin, evalH_foldl_nested, evalH_zero, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil]
      ring
    rw [hval, houter] at hg
    exact (modEq_of_sub_zero hg).symm
  -- (2) the ROLE pin: the selected subject's role IS the term's addressed role.
  · have hg := pcGate hsat i hi hE.2.2.2.1
    have hval : evalH (fRoleHead S fb ta rc) (rowOf t i)
        = -(rowOf t i ta * rowOf t i rc)
          + ((List.range S.n).map (fun j' =>
              rowOf t i (S.fSel fb j') * rowOf t i (S.sRole j'))).sum := by
      simp only [fRoleHead, evalH_foldl_addProdF, evalH_addProd, evalH_zero, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil]
      ring
    rw [hval, hta, sum_oneHot _ _ j S.n hjlt hjsel] at hg
    refine modEq_of_sub_zero ?_
    have heq : rowOf t i (S.sRole j) - rowOf t i rc
        = -(1 * rowOf t i rc) + rowOf t i (S.sRole j) := by ring
    rw [heq]; exact hg
  -- (3) the selected subject is ACTIVE.
  · have hg := pcGate hsat i hi hE.2.2.2.2.1
    have hval : evalH (fActiveHead S fb ta) (rowOf t i)
        = -rowOf t i ta
          + ((List.range S.n).map (fun j' =>
              rowOf t i (S.fSel fb j') * rowOf t i (S.sActive j'))).sum := by
      simp only [fActiveHead, evalH_foldl_addProdF, evalH_lin, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil]
      ring
    rw [hval, hta, sum_oneHot _ _ j S.n hjlt hjsel] at hg
    refine modEq_of_sub_zero ?_
    have heq : rowOf t i (S.sActive j) - 1 = -1 + rowOf t i (S.sActive j) := by ring
    rw [heq]; exact hg
  -- (4) the PARAM-INDEX pin: the selected slot IS the term's addressed param slot.
  · have hg := pcGate hsat i hi hE.2.2.2.2.2.2.1
    have hval : evalH (fpIdxHead S fb ta pc) (rowOf t i)
        = -(rowOf t i ta * rowOf t i pc)
          + ((List.range S.p).map (fun (q' : Nat) =>
              rowOf t i (S.fSelP fb q') * (q' : ℤ))).sum := by
      simp only [fpIdxHead, evalH_foldl_addLinG, evalH_addProd, evalH_zero, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil]
      have hcomm : ((List.range S.p).map (fun (q' : Nat) => (q' : ℤ) * rowOf t i (S.fSelP fb q'))).sum
          = ((List.range S.p).map (fun (q' : Nat) => rowOf t i (S.fSelP fb q') * (q' : ℤ))).sum := by
        congr 1; apply List.map_congr_left; intro q' _; ring
      rw [hcomm]; ring
    rw [hval, hta, sum_oneHot (fun (q' : Nat) => rowOf t i (S.fSelP fb q'))
      (fun (q' : Nat) => (q' : ℤ)) q S.p hqlt hqsel] at hg
    refine modEq_of_sub_zero ?_
    have heq : (q : ℤ) - rowOf t i pc = -(1 * rowOf t i pc) + (q : ℤ) := by ring
    rw [heq]; exact hg
  -- (5) the addressed param slot is WITHIN `param_count`.
  · have hg := pcGate hsat i hi hE.2.2.2.2.2.2.2.1
    have hval : evalH (fpActiveHead S fb ta) (rowOf t i)
        = -rowOf t i ta
          + ((List.range S.p).map (fun q' =>
              rowOf t i (S.fSelP fb q') * rowOf t i (S.paCol q'))).sum := by
      simp only [fpActiveHead, evalH_foldl_addProdF, evalH_lin, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil]
      ring
    rw [hval, hta, sum_oneHot _ _ q S.p hqlt hqsel] at hg
    refine modEq_of_sub_zero ?_
    have heq : rowOf t i (S.paCol q) - 1 = -1 + rowOf t i (S.paCol q) := by ring
    rw [heq]; exact hg

end Fetch

/-! ## §6 — A ROLE IS A KEY, and THE KNOT IS LOAD-BEARING. -/

section Teeth
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {S : ComposeShape}

/-- **`role_key_of_sat` — a role is a KEY.** Two DISTINCT subject slots that are both ACTIVE cannot
carry the same role tag. This is what makes `role ↦ subject` a FUNCTION: with `fetch_resolves` (which
pins the selected subject's role to the term's ADDRESSED role and forces it ACTIVE), uniqueness means
the prover cannot choose WHICH subject a rule term reads, so the composed outcome is not malleable.

The pair hypothesis is the emitted sweep's own indexing (`S.pairList.zipIdx`); the `#guard`s below
exhibit it inhabited at the minimal shape (`pcMin.pairList.zipIdx = [((0,1), 0)]`). -/
theorem role_key_of_sat {i j τ : Nat}
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (r : Nat)
    (hr : r + 1 < t.rows.length)
    (hpair : ((i, j), τ) ∈ S.pairList.zipIdx)
    (hai : rowOf t r (S.sActive i) = 1) (haj : rowOf t r (S.sActive j) = 1) :
    ¬ (rowOf t r (S.sRole i) ≡ rowOf t r (S.sRole j) [ZMOD 2013265921]) := by
  intro hsame
  -- The three emitted gates of this pair, named explicitly (so each `pcGate` picks its own head).
  have m1 : cgH (ruBothHead S τ i j) ∈ (paramComposeDesc S).constraints :=
    mem_roleKey S hpair List.mem_cons_self
  have m2 : cgH (ruDiffHead S τ i j) ∈ (paramComposeDesc S).constraints :=
    mem_roleKey S hpair (List.mem_cons_of_mem _ List.mem_cons_self)
  have m3 : cgH (condNonzeroHead (S.ruBoth τ) (S.ruDiff τ) (S.ruInv τ))
      ∈ (paramComposeDesc S).constraints :=
    mem_roleKey S hpair (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  -- K1: the joint-activity column is 1 when BOTH slots are active.
  have hg1 := pcGate hsat r hr m1
  have hboth : rowOf t r (S.ruBoth τ) ≡ 1 [ZMOD 2013265921] := by
    have hval : evalH (ruBothHead S τ i j) (rowOf t r)
        = -rowOf t r (S.ruBoth τ) + rowOf t r (S.sActive i) * rowOf t r (S.sActive j) := by
      simp only [ruBothHead, evalH_addProd, evalH_lin, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil]
      ring
    rw [hval, hai, haj] at hg1
    have hneg := Int.ModEq.neg hg1
    refine modEq_of_sub_zero ?_
    have heq : rowOf t r (S.ruBoth τ) - 1 = -(-rowOf t r (S.ruBoth τ) + 1 * 1) := by ring
    rw [heq]
    simpa using hneg
  -- K2: the difference column IS the role difference, hence ≡ 0 under the assumed collision.
  have hg2 := pcGate hsat r hr m2
  have hdiff : rowOf t r (S.ruDiff τ) ≡ 0 [ZMOD 2013265921] := by
    have hval : evalH (ruDiffHead S τ i j) (rowOf t r)
        = rowOf t r (S.sRole i) - rowOf t r (S.sRole j) - rowOf t r (S.ruDiff τ) := by
      simp only [ruDiffHead, evalH_addLin, evalH_lin]; ring
    rw [hval] at hg2
    have h0 : rowOf t r (S.sRole i) - rowOf t r (S.sRole j) ≡ 0 [ZMOD 2013265921] := by
      have hs := Int.ModEq.sub hsame (Int.ModEq.refl (rowOf t r (S.sRole j)))
      simpa using hs
    have hz := Int.ModEq.sub h0 hg2
    simpa using hz
  -- K3: the conditional-nonzero gate then demands `1 ≡ 0`, which the prime forbids.
  have hg3 := pcGate hsat r hr m3
  have hval : evalH (condNonzeroHead (S.ruBoth τ) (S.ruDiff τ) (S.ruInv τ)) (rowOf t r)
      = rowOf t r (S.ruBoth τ)
        - rowOf t r (S.ruBoth τ) * rowOf t r (S.ruDiff τ) * rowOf t r (S.ruInv τ) := by
    simp only [condNonzeroHead, evalH_addProd, evalH_lin, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil]
    ring
  rw [hval] at hg3
  have hprod : rowOf t r (S.ruBoth τ) * rowOf t r (S.ruDiff τ) * rowOf t r (S.ruInv τ)
      ≡ 0 [ZMOD 2013265921] := by
    have h1 : rowOf t r (S.ruBoth τ) * rowOf t r (S.ruDiff τ)
        ≡ rowOf t r (S.ruBoth τ) * 0 [ZMOD 2013265921] :=
      Int.ModEq.mul_left _ hdiff
    have h2 := Int.ModEq.mul_right (rowOf t r (S.ruInv τ)) h1
    simpa using h2
  have hone : (1 : ℤ) ≡ 0 [ZMOD 2013265921] :=
    hboth.symm.trans ((modEq_of_sub_zero hg3).trans hprod)
  have hdvd : (2013265921 : ℤ) ∣ 1 := by
    have hd := Int.modEq_iff_dvd.mp hone
    simpa using hd
  omega

/-- **`knot_neuter_rejected` — THE KNOT IS LOAD-BEARING.** The in-circuit twin of the Rust
`Forgery::neuter_knots` canary, as a THEOREM: no satisfying trace can publish a ZERO knot
contribution while all three of its factors — the coefficient and both fetched param values — are
nonzero. Delete the nonlinearity and the trace stops satisfying the descriptor; compositions that
differ only in their products therefore cannot be made to agree. -/
theorem knot_neuter_rejected {τ : Nat}
    (hsat : Satisfied2 hash (paramComposeDesc S) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) (hτ : τ < S.k)
    (hzero : rowOf t i (S.kContrib τ) ≡ 0 [ZMOD 2013265921])
    (hc : ¬ (rowOf t i (S.kCoeff τ) ≡ 0 [ZMOD 2013265921]))
    (ha : ¬ (rowOf t i (S.fVal (S.kFetA τ)) ≡ 0 [ZMOD 2013265921]))
    (hb : ¬ (rowOf t i (S.fVal (S.kFetB τ)) ≡ 0 [ZMOD 2013265921])) : False := by
  have hk := kContrib_eq hsat i hi hτ
  have hprod : rowOf t i (S.kCoeff τ) * rowOf t i (S.fVal (S.kFetA τ))
      * rowOf t i (S.fVal (S.kFetB τ)) ≡ 0 [ZMOD 2013265921] := hk.symm.trans hzero
  have hd : (2013265921 : ℤ) ∣ rowOf t i (S.kCoeff τ) * rowOf t i (S.fVal (S.kFetA τ))
      * rowOf t i (S.fVal (S.kFetB τ)) := Int.modEq_zero_iff_dvd.mp hprod
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · rcases pPrimeInt.dvd_mul.mp hx with hy | hy
    · exact hc (Int.modEq_zero_iff_dvd.mpr hy)
    · exact ha (Int.modEq_zero_iff_dvd.mpr hy)
  · exact hb (Int.modEq_zero_iff_dvd.mpr hx)

end Teeth

-- The role-key pair hypothesis is genuinely INHABITED: at the minimal shape the sweep is exactly the
-- one distinct pair `(0, 1)`, so `((0,1), 0) ∈ pcMin.pairList.zipIdx` holds. Checked by evaluation.
#guard pcMin.pairList == [(0, 1)]
#guard pcMin.pairList.zipIdx == [((0, 1), 0)]
#guard pcRealistic.pairList.length == 6

/-! ## §7 — Non-vacuity: the emitted gates genuinely CLOSE on an honest row.

The theorems above are conditional on `Satisfied2`. The full concrete witness (of the
`MultiStepChainRefine.wTrace_satisfied2` kind) is a NAMED RESIDUAL — assembling it needs a
`Decidable` route through `VmConstraint2.holdsAt`, whose `mapOp` arm is genuinely undecidable, so it
takes a per-form bulk lemma rather than one `decide`.

What IS checked here, by evaluation on a CONCRETE honest row, is the numeric content that witness
would carry: for the EMPTY composition at `pcMin` (no active subjects, no active rule terms, outcome
`0`, only the committed ABI-version column nonzero),

  * EVERY emitted algebraic gate evaluates to exactly `0` — all 86 of them, including the
    `forced_ge0` ordering comparison (whose `ge` bit is `0` and whose range term is `−d−1 = 0`), the
    conditional-nonzero role and role-key gates, both fetch one-hot families, the degree-3 read, the
    knot product, and THE LAW; and
  * EVERY one of the 37 PI bindings closes against the matching public-input row.

So the gate set is SATISFIABLE, not accidentally contradictory — the failure mode where a refinement
theorem is technically true because nothing can ever satisfy its hypothesis. The two REFUTATION
theorems (`role_key_of_sat`, `knot_neuter_rejected`) close the other side: the gates also genuinely
REJECT. -/

/-- The honest EMPTY composition row at `pcMin`: everything zero except the committed ABI version. -/
def wRow : Dregg2.Circuit.Assignment := fun c => if c = C_ABI then 1 else 0

/-- Its public inputs: the ABI version at `APP_BASE`, every count and root lane zero. -/
def wPub : Dregg2.Circuit.Assignment := fun k => if k = APP_BASE then 1 else 0

-- Every emitted algebraic gate VANISHES on the honest row (the list of non-vanishing gates is empty).
#guard ((paramComposeDesc pcMin).constraints.filterMap (fun c =>
  match c with
  | .base (.gate b) => if b.eval wRow == 0 then none else some (b.eval wRow)
  | _ => none)) == []

-- ...and there are genuinely 86 of them, so the check above is not passing on an empty list.
#guard ((paramComposeDesc pcMin).constraints.filter (fun c =>
  match c with | .base (.gate _) => true | _ => false)).length == 86

-- Every PI binding CLOSES against the honest public inputs.
#guard ((paramComposeDesc pcMin).constraints.filterMap (fun c =>
  match c with
  | .base (.piBinding _ col k) => if wRow col == wPub k then none else some (col, k)
  | _ => none)) == []

#assert_axioms paramCompose_refines_law
#assert_axioms outcome_is_sum
#assert_axioms lContrib_eq
#assert_axioms kContrib_eq
#assert_axioms boolSum_one_unique
#assert_axioms sel_oneHot_of_sat
#assert_axioms selP_oneHot_of_sat
#assert_axioms fetch_resolves
#assert_axioms role_key_of_sat
#assert_axioms knot_neuter_rejected

end Dregg2.Circuit.Emit.ParamComposeRefine
