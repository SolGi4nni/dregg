/-
# `Dregg2.Circuit.AlgoStarkSoundFanoutSetField` — the LAST per-effect kernel STARK-soundness
instance: `algoStarkSound_setFieldDyn` (+ the LIVE `setFieldDynForcedV3` variant), the sole
`.memOp` effect — the one whose `MemCheck` leg load-bears the higher-order-pole LogUp extension,
because a dynamic-setField memory log REPEATS its address (the write and the read-back both land
on `param[SLOT]`), so no `Nodup` hypothesis is available anywhere on the bus's lookup side.

## HONEST SCOPE (first sentence)

Per effect, the residual `Prop` hypotheses of `algoStarkSound_setFieldDyn` are EXACTLY

  1. `Poseidon2SpongeCR sponge` — the ONE shared commitment-binding hash floor (NOTE: unlike the
     7 mapOp effects, SetFieldDyn needs NO second CR instance — its memory argument is Blum's
     multiset balance, zero hashing);
  2. `FriLdtExtract … <descriptor>` — the ∀-d FRI-LDT-@-deployed extraction bundle
     (`AlgoStarkSoundGeneral`);
  3. `BusModelFamily … <descriptor>` — the per-used-table LogUp bus models (chip/range lookups);
  4. `MemBusDisciplineFamily … <descriptor>` — NAMED (NEW here, the Species-C carried bundle,
     MEMORY-LEGS-SCOPE §3(C)/§4): per accepting batch, a declared memory boundary
     (`minit`/`mfin`/`maddrs`) with (i) `maddrs.Nodup` + address closure + `Disciplined` — the
     memory table's PER-ROW discipline gates, currently UNMODELED in Lean (the memory AIR has no
     `LogUpColumnLayout`-style twin; MEMORY-LEGS-SCOPE §4(iii)) — carried NAMED, not laundered;
     and (ii) `MemBusModelOk` — the EXTRACTED memory-table LogUp bus (pole-freeness, the
     gate-forced balance, challenge non-exceptionality, fingerprint faithfulness on the
     participating entries, the no-wrap trace-length bound) — the memory-table analog of
     `BusModelOk`, carried because the memory-bus cumsum columns are likewise unmodeled
     (§4(i)). What is then DERIVED — NOT carried — is the whole `MemCheck` multiset EQUALITY.
  5. `MemTableAssembly … <descriptor>` — NAMED (the Species-B carried fact, the exact analog of
     `AlgoStarkSoundFanoutMemory.MapTableAssembly`): the committed memory table IS the gathered
     `memLog` (now CONTENT-BEARING — 2 rows on an active trace) and the committed mapOps table
     IS the (empty — `mapOpsOf = []` is DERIVED from the shape) gathered `mapLog`.

## ★ THE MULTISET-EQUALITY SZ EXTENSION (the real content of this file)

MEMORY-LEGS-SCOPE §4(ii) names the crux: `MemCheck` is a multiset EQUALITY
(`initSet + writeSet = readSet + finalSet`), while the proved LogUp crown — even the multiset
`busBalance_forces_membership_multiset` — is one-directional support CONTAINMENT, and containment
both ways still does not pin multiplicities (`[a,a,b]` vs `[a,b,b]`). So the membership lemma
alone CANNOT discharge `MemCheck`; this file proves the strictly stronger extension on top of the
same `LogUpMultiset` higher-order-pole machinery:

  `busNum_zero_forces_perm` — a vanishing bus NUMERATOR forces the two sides EQUAL AS MULTISETS
  (`List.Perm`), under the no-wrap length bound (both sides shorter than `char F`). The math is
  partial-fractions uniqueness: peeling one shared value `c` of multiplicities `k`,`j` factors
  `busNum = (X + C c)^(k+j−1) · [(C k − C j)·∏A·∏B + (X + C c)·busNum A' B']`
  (`busNum_replicate_both_factor`), and the residue at `−c` reads off `(k : F) = (j : F)` — the
  multiplicities MATCH below the characteristic — leaving the stripped numerator zero; recurse.

  `busBalance_forces_perm` — a balancing bus at a non-exceptional challenge (ε < (|A|+|B|)/|F|,
  the same `exceptionalSet` frame) forces the multiset equality outright.

`memCheck_of_memBusModel` then DERIVES the full `MemCheck` from the extracted memory bus:
fingerprint-list perm (SZ) → entry-list perm (fingerprint faithfulness, `perm_of_map_perm`) →
the multiset equation (`memCheck_iff_perm`). The prompt-named lever
`busBalance_forces_membership_multiset(_of_charP)` is consumed literally as the MEMBERSHIP
reading (`memBus_membership_of_model`) — honest report: membership is REAL but WEAKER than
`MemCheck`; the equality form proved here is what closes the leg.

Everything else is DERIVED, ∀ d, with NO per-effect proof work: `MainAirAcceptF`/`hood` (the OOD
modeler inside `algoStarkSound_of_memoryLegs`), the `.lookup` arm (the LogUp bus modeler), the
`.memOp` row arm (row-locally `True` — its content is EXACTLY the global legs above,
`DescriptorIR2.lean:575-597`), `mapOpsOf = []`/`mapLog = []` (from the shape lemma), and the
graduated column shape (`rfl`).

## Discipline

Sorry-free; no carrier props beyond the two NAMED residual bundles above; no `decide`/`Fintype`
over `|F|`-sized objects; BabyBear arithmetic never computed (BabyBear facts ride
`CharP.cast_eq_zero_iff` + `norm_num`); teeth in both polarities, including the multiplicity
mismatch (`busNum [7,7] [7] ≠ 0`) that NO membership theorem can see. NEW file; imports
read-only; builds targeted (`lake build Dregg2.Circuit.AlgoStarkSoundFanoutSetField`).
-/
import Dregg2.Circuit.AlgoStarkSoundGeneral
import Dregg2.Circuit.LogUpMultiset
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.AlgoStarkSoundFanoutSetField

open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriCore FieldArith fullChecks)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.AlgoStarkSoundGeneral
  (AcceptsFull FriLdtExtract BusModelFamily MemoryLegs algoStarkSound_of_memoryLegs)
open Dregg2.Circuit.Emit.EffectVmEmit (EffectVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitV2
  (graduateV1 constraints_graduateV1_shapes fieldWriteOp fieldReadbackOp)
open Dregg2.Circuit.Emit
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.LogUpSoundness
open Dregg2.Circuit.LogUpMultiset
open Dregg2.Crypto
open Polynomial

set_option autoImplicit false

/-! ## §0 — THE MULTISET-EQUALITY SZ EXTENSION: `busNum = 0` forces `List.Perm`.

The higher-order-pole factorization of `LogUpMultiset` (`busNum_replicate_factor`), extended to
BOTH sides sharing a value: the residue at the shared pole reads off equal multiplicities. -/

section MultisetEquality

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- `busNum` is permutation-invariant in the TABLE side too (mirror of `busNum_perm_left`). -/
theorem busNum_perm_right (A : List F) {B B' : List F} (h : B.Perm B') :
    busNum A B = busNum A B' := by
  unfold busNum
  rw [prodLin_perm h, sumSkip_perm h]

omit [DecidableEq F] in
/-- A nonzero natural below the characteristic is nonzero in `F` — the ∀-field no-wrap fact
(`CharP.cast_eq_zero_iff`, never `decide`). -/
theorem natCast_ne_zero_of_lt_charP (p : ℕ) [CharP F p] {n : ℕ} (h0 : n ≠ 0) (hlt : n < p) :
    ((n : ℕ) : F) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff F p]
  intro hdvd
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd
  omega

/-- `sumSkip` of a NONEMPTY list below the characteristic is a NONZERO polynomial: peel any
member `c` of multiplicity `j ≥ 1`; the cofactor's value at `−c` is `j · ∏(−c + b') ≠ 0`. -/
theorem sumSkip_ne_zero_of_ne_nil (p : ℕ) [CharP F p] {B : List F}
    (hne : B ≠ []) (hBp : B.length < p) : sumSkip B ≠ 0 := by
  intro hz
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil B hne
  obtain ⟨B', hcB', hperm⟩ := exists_perm_replicate_count hc
  have hj0 : B.count c ≠ 0 := by
    have := List.count_pos_iff.mpr hc
    omega
  have hjle : B.count c ≤ B.length := List.count_le_length
  obtain ⟨j', hj'⟩ : ∃ j', B.count c = j' + 1 := ⟨B.count c - 1, by omega⟩
  rw [hj'] at hperm
  rw [sumSkip_perm hperm, sumSkip_replicate_append, Nat.add_sub_cancel] at hz
  have hfac : (X + C c) ^ j'
      * (C ((j' + 1 : ℕ) : F) * prodLin B' + (X + C c) * sumSkip B') = 0 := by
    rw [← hz]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact pow_ne_zero _ (X_add_C_ne_zero c) h
  · have hev := congrArg (Polynomial.eval (-c)) h
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_zero] at hev
    rw [neg_add_cancel, zero_mul, add_zero] at hev
    rcases mul_eq_zero.mp hev with h1 | h2
    · exact natCast_ne_zero_of_lt_charP p (by omega) (by omega) h1
    · exact prodLin_eval_neg_ne_zero hcB' h2

/-- Against an EMPTY lookup side, a vanishing numerator forces the table side empty (the
degenerate boundary of the perm theorem). -/
theorem eq_nil_of_busNum_nil_eq_zero (p : ℕ) [CharP F p] {B : List F}
    (hBp : B.length < p) (hz : busNum ([] : List F) B = 0) : B = [] := by
  have hs : sumSkip B = 0 := by
    have hnil : busNum ([] : List F) B = -sumSkip B := by
      unfold busNum; simp
    rw [hnil, neg_eq_zero] at hz
    exact hz
  by_contra hne
  exact sumSkip_ne_zero_of_ne_nil p hne hBp hs

/-- **The two-sided cofactor**: `busNum (c^k ++ A) (c^j ++ B)` factors through
`(X + C c)^(k+j−1)` times this bracket (at `x := (k:F)`, `y := (j:F)`), whose value at `−c` is
the residue `((k:F) − (j:F)) · ∏A(−c) · ∏B(−c)` — the multiplicity DIFFERENCE at the shared
pole. -/
noncomputable def busDiffBracket (x y c : F) (A B : List F) : F[X] :=
  (C x - C y) * (prodLin A * prodLin B) + (X + C c) * busNum A B

omit [DecidableEq F] in
/-- **The two-sided factorization** (the `busNum_replicate_factor` extension): a value shared
with multiplicities `k, j ≥ 1` factors exactly `(X + C c)^(k+j−1)` out of the numerator, leaving
the difference bracket. -/
theorem busNum_replicate_both_factor {k j : ℕ} (hk : k ≠ 0) (hj : j ≠ 0) (c : F)
    (A B : List F) :
    busNum (List.replicate k c ++ A) (List.replicate j c ++ B)
      = (X + C c) ^ (k + j - 1) * busDiffBracket ((k : ℕ) : F) ((j : ℕ) : F) c A B := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hexp : k' + 1 + (j' + 1) - 1 = k' + j' + 1 := by omega
  unfold busDiffBracket busNum
  rw [hexp, sumSkip_replicate_append, sumSkip_replicate_append, prodLin_append, prodLin_append,
    prodLin_replicate, prodLin_replicate, Nat.add_sub_cancel, Nat.add_sub_cancel]
  generalize ((k' + 1 : ℕ) : F) = x
  generalize ((j' + 1 : ℕ) : F) = y
  ring

omit [DecidableEq F] in
/-- **The residue reads off EQUAL MULTIPLICITIES and strips the shared value**: a vanishing
two-sided numerator forces `(k : F) = (j : F)` AND the stripped numerator zero. -/
theorem busNum_zero_replicate_both {k j : ℕ} {c : F} {A B : List F}
    (hk : k ≠ 0) (hj : j ≠ 0) (hcA : c ∉ A) (hcB : c ∉ B)
    (hz : busNum (List.replicate k c ++ A) (List.replicate j c ++ B) = 0) :
    ((k : ℕ) : F) = ((j : ℕ) : F) ∧ busNum A B = 0 := by
  rw [busNum_replicate_both_factor hk hj] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h (pow_ne_zero _ (X_add_C_ne_zero c))
  · have hev := congrArg (Polynomial.eval (-c)) h
    simp only [busDiffBracket, eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_zero] at hev
    rw [neg_add_cancel, zero_mul, add_zero] at hev
    have hkj : ((k : ℕ) : F) = ((j : ℕ) : F) := by
      rcases mul_eq_zero.mp hev with h1 | h2
      · exact sub_eq_zero.mp h1
      · rcases mul_eq_zero.mp h2 with h3 | h4
        · exact absurd h3 (prodLin_eval_neg_ne_zero hcA)
        · exact absurd h4 (prodLin_eval_neg_ne_zero hcB)
    refine ⟨hkj, ?_⟩
    have hbr : (X + C c) * busNum A B = 0 := by
      have hrw : busDiffBracket ((k : ℕ) : F) ((j : ℕ) : F) c A B
          = (X + C c) * busNum A B := by
        unfold busDiffBracket
        rw [hkj]
        ring
      rw [← hrw]
      exact h
    rcases mul_eq_zero.mp hbr with h5 | h6
    · exact absurd h5 (X_add_C_ne_zero c)
    · exact h6

private theorem perm_of_busNum_zero_aux (p : ℕ) [CharP F p] :
    ∀ (n : ℕ) (A B : List F), A.length ≤ n → A.length < p → B.length < p →
      busNum A B = 0 → A.Perm B := by
  intro n
  induction n with
  | zero =>
    intro A B hlen hAp hBp hz
    cases A with
    | nil =>
      have hB := eq_nil_of_busNum_nil_eq_zero p hBp hz
      subst hB
      exact List.Perm.refl _
    | cons a A₀ => simp at hlen
  | succ n ih =>
    intro A B hlen hAp hBp hz
    cases A with
    | nil =>
      have hB := eq_nil_of_busNum_nil_eq_zero p hBp hz
      subst hB
      exact List.Perm.refl _
    | cons a A₀ =>
      have hc : a ∈ a :: A₀ := List.mem_cons_self ..
      obtain ⟨A', hcA', hpermA⟩ := exists_perm_replicate_count hc
      have hk0 : (a :: A₀).count a ≠ 0 := by
        have := List.count_pos_iff.mpr hc
        omega
      have hkle : (a :: A₀).count a ≤ (a :: A₀).length := List.count_le_length
      have hkF : (((a :: A₀).count a : ℕ) : F) ≠ 0 :=
        natCast_ne_zero_of_lt_charP p hk0 (by omega)
      have hz' : busNum (List.replicate ((a :: A₀).count a) a ++ A') B = 0 := by
        rw [← busNum_perm_left hpermA B]
        exact hz
      have hcB : a ∈ B := by
        by_contra hnB
        exact busNum_ne_zero_of_forged_multiset hkF hcA' hnB hz'
      obtain ⟨B', hcB', hpermB⟩ := exists_perm_replicate_count hcB
      have hj0 : B.count a ≠ 0 := by
        have := List.count_pos_iff.mpr hcB
        omega
      have hjle : B.count a ≤ B.length := List.count_le_length
      have hz'' : busNum (List.replicate ((a :: A₀).count a) a ++ A')
          (List.replicate (B.count a) a ++ B') = 0 := by
        rw [← busNum_perm_right _ hpermB]
        exact hz'
      obtain ⟨hkj, hzAB⟩ := busNum_zero_replicate_both hk0 hj0 hcA' hcB' hz''
      have hkeq : (a :: A₀).count a = B.count a :=
        CharP.natCast_injOn_Iio F p (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) hkj
      have hlenA : (a :: A₀).length = (a :: A₀).count a + A'.length := by
        rw [hpermA.length_eq, List.length_append, List.length_replicate]
      have hlenB : B.length = B.count a + B'.length := by
        rw [hpermB.length_eq, List.length_append, List.length_replicate]
      have hAB' : A'.Perm B' := by
        refine ih A' B' ?_ ?_ ?_ hzAB
        · have hlc : (a :: A₀).length ≤ n + 1 := hlen
          omega
        · omega
        · omega
      have hmid : (List.replicate ((a :: A₀).count a) a ++ A').Perm
          (List.replicate (B.count a) a ++ B') := by
        rw [hkeq]
        exact List.Perm.append_left _ hAB'
      exact hpermA.trans (hmid.trans hpermB.symm)

/-- **★ `busNum_zero_forces_perm` — the multiset-EQUALITY SZ extension** (MEMORY-LEGS-SCOPE
§4(ii), previously named-open): a vanishing bus numerator forces the two sides EQUAL AS
MULTISETS, with NO `Nodup` anywhere — the only side condition is no-wrap (both lengths below the
characteristic, which every committable trace meets). Partial-fractions uniqueness, made
constructive by the two-sided pole factorization. -/
theorem busNum_zero_forces_perm (p : ℕ) [CharP F p] {A B : List F}
    (hA : A.length < p) (hB : B.length < p) (hz : busNum A B = 0) : A.Perm B :=
  perm_of_busNum_zero_aux p A.length A B le_rfl hA hB hz

/-- **The bus form**: a balancing bus at a NON-EXCEPTIONAL challenge (the same ε-form
`exceptionalSet`, `< (|A|+|B|)/|F|` by `exceptionalSet_card_lt`) forces multiset EQUALITY of the
two sides — the statement `MemCheck` needs, strictly stronger than every membership theorem. -/
theorem busBalance_forces_perm (p : ℕ) [CharP F p] {A B : List F} {α : F}
    (hA : A.length < p) (hB : B.length < p)
    (hpA : ∀ a ∈ A, α + a ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α A = logupSum α B)
    (hnonexc : α ∉ exceptionalSet A B) : A.Perm B := by
  refine busNum_zero_forces_perm p hA hB ?_
  by_contra hne
  exact hnonexc (by
    rw [exceptionalSet, Multiset.mem_toFinset, mem_roots hne]
    exact (bus_zero_iff_busNum hpA hpB).mp hbal)

end MultisetEquality

/-! ## §1 — the `MemCheck ⟺ List.Perm` bridge: the four instrumentation multisets as entry
LISTS, so the bus theorem can bite. -/

section MemCheckBridge

/-- The init-boundary entry list (`initSet` as a list). -/
def initEntries (minit : ℤ → ℤ) (maddrs : List ℤ) : List (MemoryChecking.Entry ℤ ℤ) :=
  maddrs.map (MemoryChecking.initEntry minit)

/-- The final-boundary entry list (`finalSet` as a list). -/
def finEntries (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) : List (MemoryChecking.Entry ℤ ℤ) :=
  maddrs.map (MemoryChecking.finEntry mfin)

/-- The read entry list (`readSet` as a list). -/
def readEntries (log : List MemTraceOp) : List (MemoryChecking.Entry ℤ ℤ) :=
  log.map MemoryChecking.readEntry

/-- The write entry list with serials from `n` (`writeSetFrom` as a list). -/
def writeEntriesFrom : Nat → List MemTraceOp → List (MemoryChecking.Entry ℤ ℤ)
  | _, [] => []
  | n, op :: log => MemoryChecking.writeEntry op n :: writeEntriesFrom (n + 1) log

/-- The whole A side (init + writes) of the memory bus, as entries. -/
def memEntriesA (minit : ℤ → ℤ) (maddrs : List ℤ) (log : List MemTraceOp) :
    List (MemoryChecking.Entry ℤ ℤ) :=
  initEntries minit maddrs ++ writeEntriesFrom 0 log

/-- The whole B side (reads + final) of the memory bus, as entries. -/
def memEntriesB (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (log : List MemTraceOp) :
    List (MemoryChecking.Entry ℤ ℤ) :=
  readEntries log ++ finEntries mfin maddrs

theorem boundarySet_eq_coe (g : ℤ → MemoryChecking.Entry ℤ ℤ) (as : List ℤ) :
    MemoryChecking.boundarySet g as = ↑(as.map g) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [MemoryChecking.boundarySet_cons, ih, List.map_cons, Multiset.cons_coe]

theorem readSet_eq_coe (log : List MemTraceOp) :
    MemoryChecking.readSet log = ↑(readEntries log) := by
  induction log with
  | nil => rfl
  | cons op log ih =>
    rw [MemoryChecking.readSet_cons, ih]
    rfl

theorem writeSetFrom_eq_coe (log : List MemTraceOp) :
    ∀ n, MemoryChecking.writeSetFrom n log = ↑(writeEntriesFrom n log) := by
  induction log with
  | nil => intro n; rfl
  | cons op log ih =>
    intro n
    rw [MemoryChecking.writeSetFrom_cons, ih (n + 1)]
    rfl

/-- **`MemCheck` IS a list permutation** of the two bus sides — the form the SZ theorem hits. -/
theorem memCheck_iff_perm (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (log : List MemTraceOp) :
    MemoryChecking.MemCheck minit mfin maddrs log ↔
      (memEntriesA minit maddrs log).Perm (memEntriesB mfin maddrs log) := by
  show MemoryChecking.initSet minit maddrs + MemoryChecking.writeSetFrom 0 log
      = MemoryChecking.readSet log + MemoryChecking.finalSet mfin maddrs ↔ _
  rw [MemoryChecking.initSet, MemoryChecking.finalSet, boundarySet_eq_coe, boundarySet_eq_coe,
    readSet_eq_coe, writeSetFrom_eq_coe, Multiset.coe_add, Multiset.coe_add,
    Multiset.coe_eq_coe]
  exact Iff.rfl

end MemCheckBridge

/-! ## §2 — the fingerprint transfer: a perm of FINGERPRINTS is a perm of ENTRIES, under
faithfulness (injectivity ON the participating entries — never a global idealization). -/

section FingerprintTransfer

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem count_map_eq_count (f : α → β) (l : List α) (x : α)
    (hinj : ∀ y ∈ l, f y = f x → y = x) :
    (l.map f).count (f x) = l.count x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hinj' : ∀ y ∈ l, f y = f x → y = x := fun y hy => hinj y (List.mem_cons_of_mem _ hy)
    by_cases hax : a = x
    · subst hax
      rw [List.map_cons, List.count_cons_self, List.count_cons_self, ih hinj']
    · have hfa : f a ≠ f x := fun h => hax (hinj a (List.mem_cons_self ..) h)
      rw [List.map_cons, List.count_cons_of_ne hfa, List.count_cons_of_ne hax, ih hinj']

/-- A permutation of images is a permutation of sources, given injectivity on the union of the
participating elements (the faithfulness form a fingerprint actually provides). -/
theorem perm_of_map_perm {f : α → β} {l₁ l₂ : List α}
    (hinj : ∀ x, (x ∈ l₁ ∨ x ∈ l₂) → ∀ y, (y ∈ l₁ ∨ y ∈ l₂) → f x = f y → x = y)
    (h : (l₁.map f).Perm (l₂.map f)) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro x
  by_cases hx : x ∈ l₁ ∨ x ∈ l₂
  · have h₁ : (l₁.map f).count (f x) = l₁.count x :=
      count_map_eq_count f l₁ x (fun y hy hfy => hinj y (Or.inl hy) x hx hfy)
    have h₂ : (l₂.map f).count (f x) = l₂.count x :=
      count_map_eq_count f l₂ x (fun y hy hfy => hinj y (Or.inr hy) x hx hfy)
    rw [← h₁, ← h₂, h.count_eq]
  · rw [List.count_eq_zero.mpr (fun h => hx (Or.inl h)),
      List.count_eq_zero.mpr (fun h => hx (Or.inr h))]

end FingerprintTransfer

/-! ## §3 — the extracted memory bus (`MemBusModelOk`) and ★ the `MemCheck` DERIVATION. -/

section MemBus

variable {F : Type*} [Field F] [DecidableEq F]

/-- The fingerprinted A side (init + writes) of the memory-table LogUp bus. -/
def memBusA (fp : MemoryChecking.Entry ℤ ℤ → F) (minit : ℤ → ℤ) (maddrs : List ℤ)
    (log : List MemTraceOp) : List F :=
  (memEntriesA minit maddrs log).map fp

/-- The fingerprinted B side (reads + final) of the memory-table LogUp bus. -/
def memBusB (fp : MemoryChecking.Entry ℤ ℤ → F) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (log : List MemTraceOp) : List F :=
  (memEntriesB mfin maddrs log).map fp

/-- **`MemBusModelOk`** — the extracted memory-table LogUp bus at one boundary/log: pole-freeness
of both sides, the gate-forced balance, challenge non-exceptionality, fingerprint faithfulness ON
the participating entries, and the no-wrap length bounds (trace ≪ char). The memory-table analog
of `LogUpColumnLayout.BusModelOk` — CARRIED by the per-effect family below because the deployed
memory AIR's cumsum columns have no Lean layout twin yet (MEMORY-LEGS-SCOPE §4(i)); what it
yields (`memCheck_of_memBusModel`) is DERIVED, not carried. -/
def MemBusModelOk (p : ℕ) (fp : MemoryChecking.Entry ℤ ℤ → F) (α : F)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (log : List MemTraceOp) : Prop :=
  (∀ a ∈ memBusA fp minit maddrs log, α + a ≠ 0) ∧
  (∀ b ∈ memBusB fp mfin maddrs log, α + b ≠ 0) ∧
  logupSum α (memBusA fp minit maddrs log) = logupSum α (memBusB fp mfin maddrs log) ∧
  α ∉ exceptionalSet (memBusA fp minit maddrs log) (memBusB fp mfin maddrs log) ∧
  (∀ e₁, (e₁ ∈ memEntriesA minit maddrs log ∨ e₁ ∈ memEntriesB mfin maddrs log) →
    ∀ e₂, (e₂ ∈ memEntriesA minit maddrs log ∨ e₂ ∈ memEntriesB mfin maddrs log) →
      fp e₁ = fp e₂ → e₁ = e₂) ∧
  (memEntriesA minit maddrs log).length < p ∧
  (memEntriesB mfin maddrs log).length < p

/-- **★ `MemCheck` DERIVED from the extracted bus** — the repeated-address multiset balance,
closed by the equality-form SZ extension: fingerprint-perm (`busBalance_forces_perm`, no `Nodup`
anywhere) → entry-perm (faithfulness) → the `MemCheck` multiset equation. -/
theorem memCheck_of_memBusModel (p : ℕ) [CharP F p] (fp : MemoryChecking.Entry ℤ ℤ → F)
    (α : F) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (log : List MemTraceOp)
    (h : MemBusModelOk p fp α minit mfin maddrs log) :
    MemoryChecking.MemCheck minit mfin maddrs log := by
  obtain ⟨hpA, hpB, hbal, hnonexc, hinj, hlA, hlB⟩ := h
  have hmap : ((memEntriesA minit maddrs log).map fp).Perm
      ((memEntriesB mfin maddrs log).map fp) :=
    busBalance_forces_perm p
      (by simpa [memBusA] using hlA) (by simpa [memBusB] using hlB)
      hpA hpB hbal hnonexc
  exact (memCheck_iff_perm minit mfin maddrs log).mpr (perm_of_map_perm hinj hmap)

/-- The MEMBERSHIP reading of the same bus — `busBalance_forces_membership_multiset_of_charP`
(the §8-residual lever) consumed literally at the repeated-address memory bus: every init/write
fingerprint IS on the read/final side. Honest note: this containment is strictly WEAKER than
`MemCheck` (it cannot see multiplicities — `[a,a,b]` vs `[a,b,b]`); the equality form above is
what the leg needs. Kept as the explicit bridge to the named lever. -/
theorem memBus_membership_of_model (p : ℕ) [CharP F p] (fp : MemoryChecking.Entry ℤ ℤ → F)
    (α : F) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (log : List MemTraceOp)
    (h : MemBusModelOk p fp α minit mfin maddrs log) :
    ∀ x ∈ memBusA fp minit maddrs log, x ∈ memBusB fp mfin maddrs log := by
  obtain ⟨hpA, hpB, hbal, hnonexc, -, hlA, -⟩ := h
  exact busBalance_forces_membership_multiset_of_charP p
    (by simpa [memBusA] using hlA) hpA hpB hbal hnonexc

end MemBus

/-! ## §4 — THE TWO NAMED PER-EFFECT RESIDUAL BUNDLES (over the Skolemized extracted trace,
exactly the `AlgoStarkSoundGeneral` §1 / `AlgoStarkSoundFanoutMemory` §0 style). -/

/-- **`MemBusDisciplineFamily d`** — NAMED per-effect deployed-modeling premise (the Species-C
bundle, MEMORY-LEGS-SCOPE §3(C)/§4): per accepting batch, a declared memory boundary
(`minit`/`mfin`/`maddrs`) and a challenge with (i) `maddrs.Nodup` + address closure +
`MemoryChecking.Disciplined` — the memory table's PER-ROW discipline gates (claimed-prior-serial
in the past; a read returns its claimed value), currently UNMODELED in Lean (§4(iii)): carried
NAMED, never derived-by-fiat — and (ii) the extracted memory-table LogUp bus (`MemBusModelOk`,
§4(i)). `MemCheck` is NOT here: it is DERIVED (`memCheck_of_memBusModel`). The `.memOp` analog
of `MapReconcileFamily`. -/
def MemBusDisciplineFamily {F : Type*} [Field F] [DecidableEq F]
    (p : ℕ) (fp : MemoryChecking.Entry ℤ ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (α : F),
      maddrs.Nodup ∧
      (∀ op ∈ memLog d (tr pi π), op.addr ∈ maddrs) ∧
      MemoryChecking.Disciplined (memLog d (tr pi π)) ∧
      MemBusModelOk p fp α minit mfin maddrs (memLog d (tr pi π))

/-- **`MemTableAssembly d`** — the NAMED Species-B carried fact (the `.memOp`-effect analog of
`AlgoStarkSoundFanoutMemory.MapTableAssembly`, same epistemic classification as
`AirLegsDischarged.lean:30-35`): per accepting batch, (i) the committed memory table IS the
gathered `memLog` (CONTENT-BEARING here — the dynamic write + read-back rows) and (ii) the
committed mapOps table IS the gathered `mapLog` (EMPTY for SetFieldDyn — `mapOpsOf = []` is
derived from the shape, see the receipt). A table-ASSEMBLY fact about the deployed trace
commitment, not an AIR arithmetic consequence; carried NAMED, never laundered. -/
def MemTableAssembly
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    (tr pi π).tf .memory = (memLog d (tr pi π)).map opRow ∧
      (tr pi π).tf .mapOps = mapLog d (tr pi π)

/-! ## §5 — THE SHAPE HELPERS and THE MEMORY-LEGS ASSEMBLER for the `.memOp` shape. -/

/-- Shape of `{graduateV1 d0 with constraints ++ ms.map .memOp}`: graduated constraints are
`.base` (arith) or `.lookup`; the appends are `.memOp`s. (The `.memOp` twin of
`AlgoStarkSoundFanoutMemory.shape_of_graduated_append`.) -/
theorem shape_of_graduated_append_mem (d2 : EffectVmDescriptor2)
    (d0 : EffectVmDescriptor) (ms : List MemOp)
    (heq : d2.constraints
      = (graduateV1 d0).constraints ++ ms.map VmConstraint2.memOp) :
    ∀ c ∈ d2.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MemOp, c = VmConstraint2.memOp m) := by
  intro c hc hA
  rw [heq] at hc
  rcases List.mem_append.mp hc with hbase | happ
  · rcases constraints_graduateV1_shapes _ c hbase with ⟨c₀, rfl⟩ | ⟨l, rfl⟩
    · exact absurd (show isArith (VmConstraint2.base c₀) from trivial) hA
    · exact Or.inl ⟨l, rfl⟩
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp happ
    exact Or.inr ⟨m, rfl⟩

/-- Under the lookup-or-memOp shape a descriptor declares NO map ops — `mapOpsOf = []` is
DERIVED from the shape, never asserted per effect. -/
theorem mapOpsOf_eq_nil_of_memShape (d : EffectVmDescriptor2)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MemOp, c = VmConstraint2.memOp m)) :
    mapOpsOf d = [] := by
  unfold mapOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  cases c with
  | mapOp m =>
    rcases hshape _ hc (fun h => h) with ⟨l, hl⟩ | ⟨m', hm⟩
    · exact absurd hl (fun h => nomatch h)
    · exact absurd hm (fun h => nomatch h)
  | base c₀ => rfl
  | windowGate w => rfl
  | lookup l => rfl
  | memOp m => rfl
  | umemOp m => rfl
  | proofBind m => rfl

/-- The map log of a mapOp-free descriptor is empty on EVERY trace. -/
theorem mapLog_nil_of_no_mapOps (d : EffectVmDescriptor2) (t : VmTrace)
    (h : mapOpsOf d = []) : mapLog d t = [] := by
  unfold mapLog
  rw [h]
  simp

/-- **`memoryLegs_of_memShape`** — for any descriptor of the lookup-or-memOp shape, the whole
`MemoryLegs` input of the general assembler is built from {the two NAMED bundles + the multiset
SZ}: the non-lookup non-arith arm IS the `.memOp` row denotation (row-locally `True` — its
content is exactly the global legs), the boundary/closure/`Disciplined` legs are the named
row-discipline carried facts, `MemCheck` is DERIVED from the extracted bus by
`memCheck_of_memBusModel` (the repeated-address case — the whole point of SetFieldDyn), and the
two faithfulness legs are the named assembly conjuncts. -/
theorem memoryLegs_of_memShape {F : Type*} [Field F] [DecidableEq F]
    (p : ℕ) [CharP F p] (fp : MemoryChecking.Entry ℤ ℤ → F)
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MemOp, c = VmConstraint2.memOp m))
    (hlegs : MemBusDisciplineFamily p fp perm RATE toNat params vk core A initState logN view
      tr d)
    (hasm : MemTableAssembly perm RATE toNat params vk core A initState logN view tr d) :
    MemoryLegs hash perm RATE toNat params vk core A initState logN view tr d := by
  intro pi π hacc
  obtain ⟨hMemTF, hMapTF⟩ := hasm pi π hacc
  obtain ⟨minit, mfin, maddrs, α, hNodup, hClosed, hDisc, hbus⟩ := hlegs pi π hacc
  refine ⟨minit, mfin, maddrs, ?_, hNodup, hClosed, hDisc,
    memCheck_of_memBusModel p fp α minit mfin maddrs _ hbus, hMemTF, hMapTF⟩
  intro i hi c hc hA hne
  rcases hshape c hc hA with ⟨l, rfl⟩ | ⟨m, rfl⟩
  · exact absurd rfl (hne l)
  · trivial

/-! ## §6 — THE ∀-d ASSEMBLER at the `.memOp` shape, then ★ THE INSTANCES. -/

/-- **`algoStarkSound_of_memShape`** — the general assembler at the SetFieldDyn shape:
`algoStarkSound_of_memoryLegs` with its `MemoryLegs` input assembled by
`memoryLegs_of_memShape`. Residual = {the named floor, `FriLdtExtract d`, `BusModelFamily d`,
`MemBusDisciplineFamily d`, `MemTableAssembly d`}. -/
theorem algoStarkSound_of_memShape {F : Type*} [Field F] [DecidableEq F]
    (p : ℕ) [CharP F p]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ)
    (fp : List ℤ → F) (embed : ℤ → F) (fpMem : MemoryChecking.Entry ℤ ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MemOp, c = VmConstraint2.memOp m))
    (hsites : d.hashSites = []) (hranges : d.ranges = [])
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr d)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr d)
    (hlegs : MemBusDisciplineFamily p fpMem perm RATE toNat params vk core A initState logN
      view tr d)
    (hasm : MemTableAssembly perm RATE toNat params vk core A initState logN view tr d) :
    AlgoStarkSound hash (fun _ => d) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_memoryLegs d sponge hCR hash fp embed perm RATE toNat params vk core A
    initState logN view tr hsites hranges hfri hbusF
    (memoryLegs_of_memShape p fpMem hash perm RATE toNat params vk core A initState logN view
      tr d hshape hlegs hasm)

/-- setFieldDyn: graduated rotated base ++ the dynamic-address write + read-back `.memOp` pair
(`EffectVmEmitV2.lean:1383/:1394`, appended at `EffectVmEmitRotationV3.lean:2085`). -/
theorem setFieldDynV3_shape :
    ∀ c ∈ setFieldDynV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MemOp, c = VmConstraint2.memOp m) :=
  shape_of_graduated_append_mem setFieldDynV3
    (rotateV3 setFieldDynV1Face) [fieldWriteOp, fieldReadbackOp] rfl

/-- setFieldDynForced (the LIVE wave-3 variant with the fields-root weld — the weld is a `.base`
gate inside the graduated base, so the non-arith shape is identical). -/
theorem setFieldDynForcedV3_shape :
    ∀ c ∈ setFieldDynForcedV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MemOp, c = VmConstraint2.memOp m) :=
  shape_of_graduated_append_mem setFieldDynForcedV3
    (rotateV3WithFieldsRootGate EffectVmEmitSetField.SEL_SET_FIELD
      (afterFieldsRootCol setFieldDynV1Face.traceWidth) setFieldDynV1Face)
    [fieldWriteOp, fieldReadbackOp] rfl

section Instances

variable {F : Type*} [Field F] [DecidableEq F]
variable (p : ℕ) [CharP F p]
variable (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
variable (fp : List ℤ → F) (embed : ℤ → F) (fpMem : MemoryChecking.Entry ℤ ℤ → F)
variable (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
variable (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
variable (initState : List ℤ) (logN : Nat) (view : ProofView)
variable (tr : BatchPublicInputs → BatchProof → VmTrace)

/-- **★ SetFieldDyn — the LAST per-effect kernel STARK-soundness instance**, at the deployed
rotated `setFieldDynV3` (the Blum write→read transport pair on the dynamic address
`param[SLOT]`). Residual = the named bundles of the header; `MemCheck` on the genuinely
repeated-address 2-op log is DERIVED via the multiset-equality SZ extension, not carried. -/
theorem algoStarkSound_setFieldDyn
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
      setFieldDynV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      setFieldDynV3)
    (hlegs : MemBusDisciplineFamily p fpMem perm RATE toNat params vk core A initState logN
      view tr setFieldDynV3)
    (hasm : MemTableAssembly perm RATE toNat params vk core A initState logN view tr
      setFieldDynV3) :
    AlgoStarkSound hash (fun _ => setFieldDynV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_memShape p setFieldDynV3 sponge hCR hash fp embed fpMem perm RATE toNat
    params vk core A initState logN view tr setFieldDynV3_shape rfl rfl hfri hbusF hlegs hasm

/-- **SetFieldDyn (LIVE fields-root-welded deployment variant)** — STARK-soundness at
`setFieldDynForcedV3` (registry slot `setFieldDynVmDescriptor2R24`): the wave-3 in-circuit
fields-root weld rides the graduated base; the memory legs are identical in shape. -/
theorem algoStarkSound_setFieldDynForced
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
      setFieldDynForcedV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      setFieldDynForcedV3)
    (hlegs : MemBusDisciplineFamily p fpMem perm RATE toNat params vk core A initState logN
      view tr setFieldDynForcedV3)
    (hasm : MemTableAssembly perm RATE toNat params vk core A initState logN view tr
      setFieldDynForcedV3) :
    AlgoStarkSound hash (fun _ => setFieldDynForcedV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_memShape p setFieldDynForcedV3 sponge hCR hash fp embed fpMem perm RATE
    toNat params vk core A initState logN view tr setFieldDynForcedV3_shape rfl rfl hfri hbusF
    hlegs hasm

end Instances

/-! ## §7 — THE RECEIPT: the whole per-effect structural package is mechanical (`rfl` + the
shape lemma), including the DERIVED map emptiness and the literal 2-op mem declaration. -/

set_option maxRecDepth 8192 in
/-- Every per-effect structural obligation, discharged in one term. (The `memOpsOf` conjuncts
reduce the full graduated constraint list — depth-bounded, not `decide`.) -/
theorem setFieldDyn_sideConditions_mechanical :
    (setFieldDynV3.hashSites = [] ∧ setFieldDynV3.ranges = []
      ∧ mapOpsOf setFieldDynV3 = []
      ∧ memOpsOf setFieldDynV3 = [fieldWriteOp, fieldReadbackOp]) ∧
    (setFieldDynForcedV3.hashSites = [] ∧ setFieldDynForcedV3.ranges = []
      ∧ mapOpsOf setFieldDynForcedV3 = []
      ∧ memOpsOf setFieldDynForcedV3 = [fieldWriteOp, fieldReadbackOp]) :=
  ⟨⟨rfl, rfl, mapOpsOf_eq_nil_of_memShape _ setFieldDynV3_shape, rfl⟩,
   ⟨rfl, rfl, mapOpsOf_eq_nil_of_memShape _ setFieldDynForcedV3_shape, rfl⟩⟩

/-- The map table of the SetFieldDyn assembly fact is the EMPTY log, on every trace — so
`MemTableAssembly`'s second conjunct is exactly the transferV3-species emptiness fact. -/
theorem setFieldDyn_mapLog_nil (t : VmTrace) : mapLog setFieldDynV3 t = [] :=
  mapLog_nil_of_no_mapOps _ t (mapOpsOf_eq_nil_of_memShape _ setFieldDynV3_shape)

/-! ## §8 — NON-VACUITY TEETH (both polarities, `decide`-free over the field).

BabyBear facts ride `CharP.cast_eq_zero_iff` + `norm_num` (via the `LogUpMultiset` §5 helpers);
entries are small `ℤ`/`ℕ` data. -/

section Teeth

open Dregg2.Circuit.BabyBearFriField

/-- **THE MULTIPLICITY-MISMATCH TOOTH (bites)** — the exact case NO membership theorem can see:
`[7,7]` vs `[7]` have EQUAL supports (both containments hold!), yet the numerator is NONZERO —
only the multiset-EQUALITY extension distinguishes a double-spend of a memory tuple from its
single honest use. This is why SetFieldDyn's `MemCheck` needed this file. -/
theorem multiplicity_mismatch_bites : busNum ([7, 7] : List BabyBear) [7] ≠ 0 := by
  intro h
  have hperm := busNum_zero_forces_perm babyBearP (A := ([7, 7] : List BabyBear))
    (B := ([7] : List BabyBear)) (by norm_num) (by norm_num) h
  have hlen := hperm.length_eq
  simp at hlen

/-- The honest dynamic-setField-SHAPED memory log (exactly `setFieldDyn_memLog`'s shape): the
guarded write of `42` at address `5`, then the read-back at the SAME address — the repeated
address that makes the bus's A side a genuine multiset. -/
def toyLog : List MemTraceOp :=
  [⟨.write, 5, 42, 0, 0⟩, ⟨.read, 5, 42, 42, 1⟩]

theorem toyA_eq : memEntriesA (fun _ => (0 : ℤ)) [(5 : ℤ)] toyLog
    = [⟨5, 0, 0⟩, ⟨5, 42, 1⟩, ⟨5, 42, 2⟩] := rfl

theorem toyB_eq : memEntriesB (fun _ => ((42 : ℤ), 2)) [(5 : ℤ)] toyLog
    = [⟨5, 0, 0⟩, ⟨5, 42, 1⟩, ⟨5, 42, 2⟩] := rfl

/-- **THE END-TO-END FIRE**: the whole derivation chain (`MemBusModelOk` → fingerprint perm by
the multiset SZ → entry perm by faithfulness → `MemCheck`) RUNS on the genuine repeated-address
2-op log, with the serial fingerprint and challenge `α = 1`. The accept path is real on the
exact shape SetFieldDyn commits. -/
theorem toy_memCheck_fires :
    MemoryChecking.MemCheck (fun _ => (0 : ℤ)) (fun _ => ((42 : ℤ), 2)) [(5 : ℤ)] toyLog := by
  have hbusAB : memBusA (fun e => ((e.serial : ℕ) : BabyBear)) (fun _ => (0 : ℤ)) [(5 : ℤ)]
        toyLog
      = memBusB (fun e => ((e.serial : ℕ) : BabyBear)) (fun _ => ((42 : ℤ), 2)) [(5 : ℤ)]
        toyLog := by
    unfold memBusA memBusB
    rw [toyA_eq, toyB_eq]
  have hlist : memBusA (fun e => ((e.serial : ℕ) : BabyBear)) (fun _ => (0 : ℤ)) [(5 : ℤ)]
      toyLog = [((0 : ℕ) : BabyBear), ((1 : ℕ) : BabyBear), ((2 : ℕ) : BabyBear)] := by
    unfold memBusA
    rw [toyA_eq]
    rfl
  have hpoles : ∀ a ∈ memBusA (fun e => ((e.serial : ℕ) : BabyBear)) (fun _ => (0 : ℤ))
      [(5 : ℤ)] toyLog, (1 : BabyBear) + a ≠ 0 := by
    rw [hlist]
    intro a ha
    have hstep : ∀ k : ℕ, k < 3 → (1 : BabyBear) + ((k : ℕ) : BabyBear) ≠ 0 := by
      intro k hk
      have hsum : (1 : BabyBear) + ((k : ℕ) : BabyBear) = (((k + 1 : ℕ)) : BabyBear) := by
        push_cast
        ring
      rw [hsum]
      exact babybear_natCast_ne_zero (by omega) (by norm_num; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hstep 0 (by norm_num)
    · exact hstep 1 (by norm_num)
    · exact hstep 2 (by norm_num)
  refine memCheck_of_memBusModel babyBearP (fun e => ((e.serial : ℕ) : BabyBear)) 1 _ _ _ _
    ⟨hpoles, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hbusAB]
    exact hpoles
  · rw [hbusAB]
  · rw [← hbusAB, exceptionalSet, busNum_self, roots_zero]
    simp
  · intro e₁ he₁ e₂ he₂ hfp
    have hmem : ∀ e : MemoryChecking.Entry ℤ ℤ,
        (e ∈ memEntriesA (fun _ => (0 : ℤ)) [(5 : ℤ)] toyLog
          ∨ e ∈ memEntriesB (fun _ => ((42 : ℤ), 2)) [(5 : ℤ)] toyLog) →
        e = ⟨5, 0, 0⟩ ∨ e = ⟨5, 42, 1⟩ ∨ e = ⟨5, 42, 2⟩ := by
      intro e h
      rw [toyA_eq, toyB_eq] at h
      rcases h with h | h <;> simpa using h
    have h01 : ((0 : ℕ) : BabyBear) ≠ ((1 : ℕ) : BabyBear) :=
      babybear_natCast_ne (by norm_num) (by norm_num)
    have h02 : ((0 : ℕ) : BabyBear) ≠ ((2 : ℕ) : BabyBear) :=
      babybear_natCast_ne (by norm_num) (by norm_num)
    have h12 : ((1 : ℕ) : BabyBear) ≠ ((2 : ℕ) : BabyBear) :=
      babybear_natCast_ne (by norm_num) (by norm_num)
    rcases hmem e₁ he₁ with rfl | rfl | rfl <;> rcases hmem e₂ he₂ with rfl | rfl | rfl <;>
      first
        | rfl
        | exact absurd hfp h01
        | exact absurd hfp h02
        | exact absurd hfp h12
        | exact absurd hfp h01.symm
        | exact absurd hfp h02.symm
        | exact absurd hfp h12.symm
  · rw [toyA_eq]
    norm_num
  · rw [toyB_eq]
    norm_num

/-- **THE FORGED-FINAL TOOTH (bites)**: the same log with a FORGED final boundary (claiming the
cell ends at `43`) has NO `MemCheck` — the multiset equation itself refuses: the forged final
entry appears on the read/final side but nowhere among init + writes. -/
theorem forged_final_memcheck_bites :
    ¬ MemoryChecking.MemCheck (fun _ => (0 : ℤ)) (fun _ => ((43 : ℤ), 2)) [(5 : ℤ)] toyLog := by
  intro h
  have hperm := (memCheck_iff_perm _ _ _ _).mp h
  have hBside : memEntriesB (fun _ => ((43 : ℤ), 2)) [(5 : ℤ)] toyLog
      = [⟨5, 0, 0⟩, ⟨5, 42, 1⟩, ⟨5, 43, 2⟩] := rfl
  have hmem : (⟨5, 43, 2⟩ : MemoryChecking.Entry ℤ ℤ)
      ∈ memEntriesA (fun _ => (0 : ℤ)) [(5 : ℤ)] toyLog := by
    refine hperm.mem_iff.mpr ?_
    rw [hBside]
    simp
  rw [toyA_eq] at hmem
  simp at hmem

end Teeth

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms busNum_perm_right
#assert_axioms natCast_ne_zero_of_lt_charP
#assert_axioms sumSkip_ne_zero_of_ne_nil
#assert_axioms eq_nil_of_busNum_nil_eq_zero
#assert_axioms busNum_replicate_both_factor
#assert_axioms busNum_zero_replicate_both
#assert_axioms busNum_zero_forces_perm
#assert_axioms busBalance_forces_perm
#assert_axioms boundarySet_eq_coe
#assert_axioms readSet_eq_coe
#assert_axioms writeSetFrom_eq_coe
#assert_axioms memCheck_iff_perm
#assert_axioms count_map_eq_count
#assert_axioms perm_of_map_perm
#assert_axioms memCheck_of_memBusModel
#assert_axioms memBus_membership_of_model
#assert_axioms shape_of_graduated_append_mem
#assert_axioms mapOpsOf_eq_nil_of_memShape
#assert_axioms mapLog_nil_of_no_mapOps
#assert_axioms memoryLegs_of_memShape
#assert_axioms algoStarkSound_of_memShape
#assert_axioms setFieldDynV3_shape
#assert_axioms setFieldDynForcedV3_shape
#assert_axioms algoStarkSound_setFieldDyn
#assert_axioms algoStarkSound_setFieldDynForced
#assert_axioms setFieldDyn_sideConditions_mechanical
#assert_axioms setFieldDyn_mapLog_nil
#assert_axioms multiplicity_mismatch_bites
#assert_axioms toy_memCheck_fires
#assert_axioms forged_final_memcheck_bites

end Dregg2.Circuit.AlgoStarkSoundFanoutSetField
