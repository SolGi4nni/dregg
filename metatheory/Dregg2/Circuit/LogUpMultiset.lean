/-
# `Dregg2.Circuit.LogUpMultiset` — the higher-order-pole MULTISET Schwartz–Zippel extension.

DISCHARGES the second §8 residual of `LogUpSoundness.lean` (`:473-477`): the repeated-value
multiplicity case. `LogUpSoundness.busBalance_forces_membership` forces every looked-up value into
the table only for a `Nodup` lookup list — but memory logs REPEAT addresses, so the deployed A side
is a genuine multiset. This file proves the same support containment with NO `Nodup` hypothesis.

## The math (the residue at the higher-order pole)

A value `c` looked up with multiplicity `k ≥ 1` contributes the order-`k` pole `k/(X + c)` to the
lookup side of the bus. Clearing denominators: with `P = replicate k c ++ A` (`c ∉ A`),

  `prodLin P = (X + C c)^k · prodLin A`, and (since `sumSkip = derivative ∘ prodLin`)
  `sumSkip P = k·(X + C c)^(k−1) · prodLin A + (X + C c)^k · sumSkip A`,

so the whole numerator FACTORS (`busNum_replicate_factor`):

  `busNum P B = (X + C c)^(k−1) · G`,  `G = (k·prodLin A + (X+C c)·sumSkip A)·prodLin B − (X+C c)·sumSkip B·prodLin A`

— an order-(k−1) zero at `−c` whose RESIDUE is `G(−c) = k · prodLin A(−c) · prodLin B(−c)`, NONZERO
whenever `c ∉ B` and `k ≠ 0` in `F` (`k ≤ |A| ≪ char F = 2013265921` always — no wrap). Hence
`busNum ≠ 0` (`busNum_ne_zero_of_forged_multiset`), the pole order is EXACTLY `k−1`
(`busNum_forged_rootMultiplicity`, the `Polynomial.rootMultiplicity` bookkeeping), and the same
`card_roots'` route gives ε ≤ (|A|+|B|)/|F| with the exceptional set named. NO new assumption: the
only hypothesis beyond `LogUpSoundness`'s is the no-wrap side condition `(count : F) ≠ 0`, which is
DISCHARGED for any trace shorter than the characteristic (`…_of_charP`, instantiated at BabyBear).

`busBalance_forces_membership_multiset` SUBSUMES the `Nodup` theorem: `busBalance_forces_membership`
is re-derived as the multiplicity-1 specialization (`busBalance_forces_membership_of_nodup`), and
§5's `busNum_ne_zero_of_forged` is the `k = 1` case (`busNum_ne_zero_of_forged_via_multiset`).
-/
import Mathlib.Algebra.Polynomial.RingDivision
import Dregg2.Circuit.LogUpSoundness

namespace Dregg2.Circuit.LogUpMultiset

open Polynomial Dregg2.Circuit.LogUpSoundness

variable {F : Type*} [Field F]

/-! ## §1 — `prodLin`/`sumSkip` over a replicated head: the `(X + C c)^k` factor. -/

theorem prodLin_append (A A' : List F) : prodLin (A ++ A') = prodLin A * prodLin A' := by
  unfold prodLin
  rw [List.map_append, List.prod_append]

theorem prodLin_replicate (k : ℕ) (c : F) :
    prodLin (List.replicate k c) = (X + C c) ^ k := by
  unfold prodLin
  rw [List.map_replicate, List.prod_replicate]

/-- The numerator over a multiplicity-`k` head: differentiating `(X+C c)^k · prodLin A` peels the
`k·(X+C c)^(k−1)` factor — the derivative form of `sumSkip` doing the higher-order-pole bookkeeping. -/
theorem sumSkip_replicate_append (k : ℕ) (c : F) (A : List F) :
    sumSkip (List.replicate k c ++ A)
      = C (k : F) * (X + C c) ^ (k - 1) * prodLin A + (X + C c) ^ k * sumSkip A := by
  rw [sumSkip_eq_derivative, prodLin_append, prodLin_replicate, derivative_mul, derivative_pow,
    derivative_add, derivative_X, derivative_C, add_zero, mul_one, ← sumSkip_eq_derivative]

/-! ## §2 — The factorization `busNum = (X + C c)^(k−1) · busCofactor` and its residue. -/

/-- **The cofactor `G`** in `busNum (replicate k c ++ A) B = (X + C c)^(k−1) · G`. Its value at `−c`
is the residue `k · prodLin A(−c) · prodLin B(−c)` (`busCofactor_eval_neg`) — nonzero for a forgery. -/
noncomputable def busCofactor (k : ℕ) (c : F) (A B : List F) : F[X] :=
  (C (k : F) * prodLin A + (X + C c) * sumSkip A) * prodLin B
    - (X + C c) * (sumSkip B * prodLin A)

/-- **The factorization.** A value of multiplicity `k ≥ 1` factors exactly `(X + C c)^(k−1)` out of
the bus numerator — the order-(k−1) zero matching the order-k pole of the rational bus. -/
theorem busNum_replicate_factor {k : ℕ} (hk : k ≠ 0) (c : F) (A B : List F) :
    busNum (List.replicate k c ++ A) B = (X + C c) ^ (k - 1) * busCofactor k c A B := by
  cases k with
  | zero => exact absurd rfl hk
  | succ n =>
    unfold busNum busCofactor
    rw [sumSkip_replicate_append, prodLin_append, prodLin_replicate, Nat.add_sub_cancel]
    ring

/-- **The residue at `−c`.** The cofactor evaluates at `−c` to `k · prodLin A(−c) · prodLin B(−c)` —
the `(k−1)`-st derivative content of the numerator, with NO enumeration (all factors symbolic). -/
theorem busCofactor_eval_neg (k : ℕ) (c : F) (A B : List F) :
    (busCofactor k c A B).eval (-c)
      = (k : F) * ((prodLin A).eval (-c) * (prodLin B).eval (-c)) := by
  have h0 : (X + C c).eval (-c) = 0 := by
    rw [eval_add, eval_X, eval_C, neg_add_cancel]
  unfold busCofactor
  rw [eval_sub, eval_mul, eval_add, eval_mul, eval_mul, eval_mul, h0, eval_C]
  ring

/-- `prodLin A` does not vanish at `−c` when `c ∉ A` (the factor form of pole-avoidance). -/
theorem prodLin_eval_neg_ne_zero {c : F} {A : List F} (hcA : c ∉ A) :
    (prodLin A).eval (-c) ≠ 0 := by
  refine prodLin_eval_ne_zero fun a ha hz => hcA ?_
  have hac : a = c := by linear_combination hz
  rwa [hac] at ha

/-! ## §3 — The multiset forged tooth: repeated forgery still makes `busNum ≠ 0`. -/

/-- **A forged value of ANY multiplicity `k` (with `k ≠ 0` in `F`) makes the numerator NONZERO.**
The §8 (`LogUpSoundness.lean:473-477`) extension of `busNum_ne_zero_of_forged`: `c ∉ B` looked up
`k ≥ 1` times gives `busNum = (X+C c)^(k−1) · G` with `G(−c) = k·prodLin A(−c)·prodLin B(−c) ≠ 0`,
so both factors are nonzero polynomials. The side condition `(k : F) ≠ 0` is the ONLY new
hypothesis — the no-wrap fact, automatic for `k <` the characteristic (see `…_of_charP`). -/
theorem busNum_ne_zero_of_forged_multiset {A B : List F} {c : F} {k : ℕ}
    (hkF : (k : F) ≠ 0) (hcA : c ∉ A) (hcB : c ∉ B) :
    busNum (List.replicate k c ++ A) B ≠ 0 := by
  have hk : k ≠ 0 := by rintro rfl; exact hkF Nat.cast_zero
  have hG : (busCofactor k c A B).eval (-c) ≠ 0 := by
    rw [busCofactor_eval_neg]
    exact mul_ne_zero hkF
      (mul_ne_zero (prodLin_eval_neg_ne_zero hcA) (prodLin_eval_neg_ne_zero hcB))
  have hGne : busCofactor k c A B ≠ 0 := fun h => hG (by rw [h, eval_zero])
  rw [busNum_replicate_factor hk]
  exact mul_ne_zero (pow_ne_zero _ (X_add_C_ne_zero c)) hGne

/-- **The pole-order bookkeeping is EXACT**: the forged numerator's root multiplicity at `−c` is
precisely `k − 1` (`Polynomial.rootMultiplicity`) — the order-(k−1) zero matching the order-k pole,
with the nonzero residue certifying it grows no further. -/
theorem busNum_forged_rootMultiplicity {A B : List F} {c : F} {k : ℕ}
    (hkF : (k : F) ≠ 0) (hcA : c ∉ A) (hcB : c ∉ B) :
    (busNum (List.replicate k c ++ A) B).rootMultiplicity (-c) = k - 1 := by
  have hk : k ≠ 0 := by rintro rfl; exact hkF Nat.cast_zero
  have hG : (busCofactor k c A B).eval (-c) ≠ 0 := by
    rw [busCofactor_eval_neg]
    exact mul_ne_zero hkF
      (mul_ne_zero (prodLin_eval_neg_ne_zero hcA) (prodLin_eval_neg_ne_zero hcB))
  have hGne : busCofactor k c A B ≠ 0 := fun h => hG (by rw [h, eval_zero])
  have hXC : (X + C c : F[X]) = X - C (-c) := by rw [map_neg, sub_neg_eq_add]
  rw [busNum_replicate_factor hk, mul_comm, hXC, rootMultiplicity_mul_X_sub_C_pow hGne,
    rootMultiplicity_eq_zero hG, zero_add]

/-- **§5 SUBSUMED**: `busNum_ne_zero_of_forged` is the `k = 1` case of the multiset tooth. -/
theorem busNum_ne_zero_of_forged_via_multiset {A B : List F} {c : F}
    (hcA : c ∉ A) (hcB : c ∉ B) : busNum (c :: A) B ≠ 0 := by
  have h1 : ((1 : ℕ) : F) ≠ 0 := by rw [Nat.cast_one]; exact one_ne_zero
  have := busNum_ne_zero_of_forged_multiset (k := 1) h1 hcA hcB
  rwa [show List.replicate 1 c ++ A = c :: A from rfl] at this

/-! ## §4 — The SZ soundness form and the membership bridge, multiset. -/

section Membership

variable [DecidableEq F]

/-- **LogUp soundness, forged-multiset form (ε named).** A value `c ∉ B` looked up `k` times that
still balances the bus at `α` (off the poles) forces `α` into the exceptional set of size
`< |A| + |B|` — ε ≤ (|A|+|B|)/|F| under a uniform challenge, the same SZ frame as
`logup_forged_lookup_sound`, now at the higher-order pole. -/
theorem logup_forged_multiset_sound {A B : List F} {c α : F} {k : ℕ}
    (hkF : (k : F) ≠ 0) (hcA : c ∉ A) (hcB : c ∉ B)
    (hpA : ∀ x ∈ List.replicate k c ++ A, α + x ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α (List.replicate k c ++ A) = logupSum α B) :
    α ∈ exceptionalSet (List.replicate k c ++ A) B ∧
      (exceptionalSet (List.replicate k c ++ A) B).card
        < (List.replicate k c ++ A).length + B.length := by
  have hne := busNum_ne_zero_of_forged_multiset hkF hcA hcB
  refine ⟨?_, exceptionalSet_card_lt hne⟩
  rw [exceptionalSet, Multiset.mem_toFinset, mem_roots hne]
  exact (bus_zero_iff_busNum hpA hpB).mp hbal

/-- Any element decomposes its list as `count`-many copies ++ a remainder free of it. -/
theorem exists_perm_replicate_count {β : Type*} [DecidableEq β] {A : List β} {c : β}
    (hc : c ∈ A) :
    ∃ A', c ∉ A' ∧ A.Perm (List.replicate (A.count c) c ++ A') := by
  induction A with
  | nil => exact absurd hc (List.not_mem_nil)
  | cons a A ih =>
    by_cases hac : a = c
    · subst hac
      by_cases hmem : a ∈ A
      · obtain ⟨A', hnA', hp⟩ := ih hmem
        refine ⟨A', hnA', ?_⟩
        rw [List.count_cons_self, List.replicate_succ, List.cons_append]
        exact hp.cons a
      · refine ⟨A, hmem, ?_⟩
        rw [List.count_cons_self, List.count_eq_zero.mpr hmem, List.replicate_succ,
          List.replicate_zero, List.cons_append, List.nil_append]
    · have hmem : c ∈ A := by
        rcases List.mem_cons.mp hc with h | h
        · exact absurd h.symm hac
        · exact h
      obtain ⟨A', hnA', hp⟩ := ih hmem
      refine ⟨a :: A', ?_, ?_⟩
      · intro hmm
        rcases List.mem_cons.mp hmm with h | h
        · exact hac h.symm
        · exact hnA' h
      · rw [List.count_cons_of_ne hac]
        exact (hp.cons a).trans List.perm_middle.symm

/-- **The per-value multiset membership bridge.** A balancing bus at a non-exceptional challenge
forces any looked-up `c` into the table, whatever its multiplicity — the only side condition is
no-wrap: `(A.count c : F) ≠ 0`. Replaces `busBalance_forces_membership_single`'s `count = 1`. -/
theorem busBalance_forces_membership_count {A B : List F} {α c : F}
    (hpA : ∀ a ∈ A, α + a ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α A = logupSum α B)
    (hnonexc : α ∉ exceptionalSet A B)
    (hc : c ∈ A) (hcount : (A.count c : F) ≠ 0) : c ∈ B := by
  by_contra hcB
  obtain ⟨A', hcA', hperm⟩ := exists_perm_replicate_count hc
  have hne : busNum (List.replicate (A.count c) c ++ A') B ≠ 0 :=
    busNum_ne_zero_of_forged_multiset hcount hcA' hcB
  have hbal' : logupSum α (List.replicate (A.count c) c ++ A') = logupSum α B := by
    rw [← logupSum_perm α hperm]; exact hbal
  have hnonexc' : α ∉ exceptionalSet (List.replicate (A.count c) c ++ A') B := by
    rwa [exceptionalSet_perm_left hperm B] at hnonexc
  have hpA' : ∀ x ∈ List.replicate (A.count c) c ++ A', α + x ≠ 0 :=
    fun x hx => hpA x (hperm.mem_iff.mpr hx)
  have hroot : (busNum (List.replicate (A.count c) c ++ A') B).eval α = 0 :=
    (bus_zero_iff_busNum hpA' hpB).mp hbal'
  exact hnonexc' (by rw [exceptionalSet, Multiset.mem_toFinset, mem_roots hne]; exact hroot)

/-- **`busBalance_forces_membership_multiset` — support containment for a MULTISET lookup side.**
The §8 residual DISCHARGED: a balancing bus at a non-exceptional challenge (ε ≤ (|A|+|B|)/|F| by
`exceptionalSet_card_lt`) forces `∀ c ∈ A, c ∈ B` with NO `Nodup` hypothesis — memory logs may
repeat addresses freely. The `hchar` side condition is the no-wrap fact (multiplicities below the
characteristic), discharged wholesale by `…_of_charP` below. -/
theorem busBalance_forces_membership_multiset {A B : List F} {α : F}
    (hpA : ∀ a ∈ A, α + a ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α A = logupSum α B)
    (hnonexc : α ∉ exceptionalSet A B)
    (hchar : ∀ c ∈ A, (A.count c : F) ≠ 0) :
    ∀ c ∈ A, c ∈ B :=
  fun c hc => busBalance_forces_membership_count hpA hpB hbal hnonexc hc (hchar c hc)

/-- The distinct-support (`toFinset`) reading of the multiset containment. -/
theorem busBalance_forces_membership_multiset_toFinset {A B : List F} {α : F}
    (hpA : ∀ a ∈ A, α + a ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α A = logupSum α B)
    (hnonexc : α ∉ exceptionalSet A B)
    (hchar : ∀ c ∈ A, (A.count c : F) ≠ 0) :
    ∀ c ∈ A.toFinset, c ∈ B :=
  fun c hc =>
    busBalance_forces_membership_multiset hpA hpB hbal hnonexc hchar c (List.mem_toFinset.mp hc)

/-- **No-wrap discharged by the characteristic**: any lookup list SHORTER than `char F` satisfies
the multiplicity side condition outright (`count ≤ length < p`, and `p ∤ count` for `0 < count < p`).
This is the form the deployed prover meets — traces are ≪ 2·10⁹ rows. -/
theorem busBalance_forces_membership_multiset_of_charP (p : ℕ) [CharP F p]
    {A B : List F} {α : F} (hlen : A.length < p)
    (hpA : ∀ a ∈ A, α + a ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α A = logupSum α B)
    (hnonexc : α ∉ exceptionalSet A B) :
    ∀ c ∈ A, c ∈ B := by
  refine busBalance_forces_membership_multiset hpA hpB hbal hnonexc fun c hc => ?_
  rw [Ne, CharP.cast_eq_zero_iff F p]
  intro hdvd
  have h1 : 0 < A.count c := List.count_pos_iff.mpr hc
  have h2 : A.count c ≤ A.length := List.count_le_length
  have := Nat.le_of_dvd h1 hdvd
  omega

/-- **SUBSUMPTION**: `LogUpSoundness.busBalance_forces_membership` (the `Nodup` case) is the
multiplicity-1 specialization of the multiset theorem — re-derived here without its original proof:
`Nodup` gives `count = 1` and `(1 : F) ≠ 0` needs no characteristic side condition. -/
theorem busBalance_forces_membership_of_nodup {A B : List F} {α : F}
    (hpA : ∀ a ∈ A, α + a ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α A = logupSum α B)
    (hnonexc : α ∉ exceptionalSet A B)
    (hnodup : A.Nodup) : ∀ c ∈ A, c ∈ B :=
  busBalance_forces_membership_multiset hpA hpB hbal hnonexc fun c hc => by
    rw [List.count_eq_one_of_mem hnodup hc, Nat.cast_one]
    exact one_ne_zero

end Membership

#assert_axioms prodLin_append
#assert_axioms sumSkip_replicate_append
#assert_axioms busNum_replicate_factor
#assert_axioms busCofactor_eval_neg
#assert_axioms busNum_ne_zero_of_forged_multiset
#assert_axioms busNum_forged_rootMultiplicity
#assert_axioms busNum_ne_zero_of_forged_via_multiset
#assert_axioms logup_forged_multiset_sound
#assert_axioms busBalance_forces_membership_count
#assert_axioms busBalance_forces_membership_multiset
#assert_axioms busBalance_forces_membership_multiset_of_charP
#assert_axioms busBalance_forces_membership_of_nodup

/-! ## §5 — BabyBear instantiation + NON-VACUITY TEETH (both polarities, `decide`-free).

BabyBear facts here go through `CharP.cast_eq_zero_iff` + `norm_num` — never `decide` over the
2·10⁹-element field, never enumeration; multiplicities and lengths are small `ℕ`s. -/

section BabyBear

open Dregg2.Circuit.BabyBearFriField

/-- A nonzero natural below the characteristic is nonzero in BabyBear — the no-wrap floor fact. -/
theorem babybear_natCast_ne_zero {n : ℕ} (h0 : n ≠ 0) (hlt : n < babyBearP) :
    ((n : ℕ) : BabyBear) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff BabyBear babyBearP]
  intro hdvd
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd
  omega

/-- Distinct small naturals stay distinct in BabyBear (via the characteristic, not `decide`). -/
theorem babybear_natCast_ne {a b : ℕ} (hab : a < b) (hb : b < babyBearP) :
    ((a : ℕ) : BabyBear) ≠ ((b : ℕ) : BabyBear) := by
  intro h
  have hd : ((b - a : ℕ) : BabyBear) = 0 := by
    rw [Nat.cast_sub hab.le, ← h, sub_self]
  have hdvd := (CharP.cast_eq_zero_iff BabyBear babyBearP _).mp hd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- **BabyBear multiset membership** — every trace the deployed prover can commit (length below the
field size) gets the full multiset support containment, no `Nodup`, no extra hypothesis. -/
theorem busBalance_forces_membership_multiset_babybear {A B : List BabyBear} {α : BabyBear}
    (hlen : A.length < babyBearP)
    (hpA : ∀ a ∈ A, α + a ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α A = logupSum α B)
    (hnonexc : α ∉ exceptionalSet A B) :
    ∀ c ∈ A, c ∈ B :=
  busBalance_forces_membership_multiset_of_charP babyBearP hlen hpA hpB hbal hnonexc

/-- `7 ∉ tbl3` — proved through the characteristic (`decide`-free companion to §7's tooth). -/
theorem seven_not_mem_tbl3 : (7 : BabyBear) ∉ tbl3 := by
  intro hmem
  simp only [tbl3, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h
  · exact babybear_natCast_ne (a := 7) (b := 10) (by norm_num) (by norm_num) (by exact_mod_cast h)
  · exact babybear_natCast_ne (a := 7) (b := 20) (by norm_num) (by norm_num) (by exact_mod_cast h)
  · exact babybear_natCast_ne (a := 7) (b := 30) (by norm_num) (by norm_num) (by exact_mod_cast h)

/-- FORGED-REPEATED TOOTH (bites): `7 ∉ tbl3` looked up TWICE still makes `busNum` a nonzero
polynomial — the order-2 pole leaves the nonzero residue `2·∏(−7+bᵢ)`; the repeated forgery is
UNSAT for all but `< |[7,7]| + |tbl3| = 5` of the 2·10⁹ challenges. -/
theorem forged_repeated_lookup_bites : busNum ([7, 7] : List BabyBear) tbl3 ≠ 0 := by
  have h2 : ((2 : ℕ) : BabyBear) ≠ 0 := babybear_natCast_ne_zero (by norm_num) (by norm_num)
  have key := busNum_ne_zero_of_forged_multiset (k := 2) (c := (7 : BabyBear))
    (A := ([] : List BabyBear)) (B := tbl3) h2 (List.not_mem_nil) seven_not_mem_tbl3
  rwa [show List.replicate 2 (7 : BabyBear) ++ [] = [7, 7] from rfl] at key

/-- …and its exceptional set is genuinely small: `< 5` of the `2013265921` field elements. -/
theorem forged_repeated_exceptional_small :
    (exceptionalSet ([7, 7] : List BabyBear) tbl3).card < 2 + tbl3.length :=
  exceptionalSet_card_lt forged_repeated_lookup_bites

/-- POLE-ORDER TOOTH (exact): the doubled forgery's numerator has root multiplicity EXACTLY `1`
at `−7` — the `rootMultiplicity` bookkeeping is real on concrete BabyBear values, not just an
upper bound. -/
theorem forged_repeated_pole_order :
    (busNum ([7, 7] : List BabyBear) tbl3).rootMultiplicity (-7) = 1 := by
  have h2 : ((2 : ℕ) : BabyBear) ≠ 0 := babybear_natCast_ne_zero (by norm_num) (by norm_num)
  have key := busNum_forged_rootMultiplicity (k := 2) (c := (7 : BabyBear))
    (A := ([] : List BabyBear)) (B := tbl3) h2 (List.not_mem_nil) seven_not_mem_tbl3
  rwa [show List.replicate 2 (7 : BabyBear) ++ [] = [7, 7] from rfl] at key

/-- REPEATED-MEMBERSHIP TOOTH (fires): the honest bus `[20, 20]` (a value looked up TWICE — the
expansion of table row `(20, 2)`) balances at the non-exceptional `α = 0`, and the MULTISET bridge
derives `20 ∈ B` where the `Nodup` theorem cannot even be stated. The whole
accept ⟹ membership path runs on a genuinely repeated value. -/
theorem repeated_membership_bridge_fires :
    (20 : BabyBear) ∈ ([20, 20] : List BabyBear) := by
  have h20 : ∀ a ∈ ([20, 20] : List BabyBear), (0 : BabyBear) + a ≠ 0 := by
    intro a ha
    have ha' : a = 20 := by simpa using ha
    subst ha'
    rw [zero_add]
    have := babybear_natCast_ne_zero (n := 20) (by norm_num) (by norm_num)
    simpa using this
  refine busBalance_forces_membership_multiset_babybear (A := [20, 20]) (B := [20, 20])
    (α := 0) (by norm_num) h20 h20 rfl ?_ 20 (by simp)
  rw [exceptionalSet, busNum_self, roots_zero]
  simp

end BabyBear

#assert_axioms babybear_natCast_ne_zero
#assert_axioms babybear_natCast_ne
#assert_axioms busBalance_forces_membership_multiset_babybear
#assert_axioms seven_not_mem_tbl3
#assert_axioms forged_repeated_lookup_bites
#assert_axioms forged_repeated_exceptional_small
#assert_axioms forged_repeated_pole_order
#assert_axioms repeated_membership_bridge_fires

#check @busBalance_forces_membership_multiset
#check @busNum_forged_rootMultiplicity

end Dregg2.Circuit.LogUpMultiset
