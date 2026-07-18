/-
# Dregg2.Circuit.Emit.GnarkVerifier.QueryPowEmit — the QueryPow grinding check, emitted
and LEAF-REFINED as a genuine ∀-theorem.

THE CHECK (the query-phase proof-of-work): the transcript-derived grinding challenge —
the base squeeze drawn immediately after absorbing the PoW witness — has its low
`powBits` bits all zero. Deployed references:

  * `chain/gnark/grinding.go` `CheckWitness` (emulated-BabyBear carrier) and
    `chain/gnark/fri_verify_native.go` `CheckWitnessNative` (MultiField carrier): observe
    the witness, `SampleBitsDecomposed(powBits)`, `AssertIsEqual(b, 0)` per bit — the
    in-circuit form of p3 `GrindingChallenger::check_witness`
    (`grinding_challenger.rs:40-46`) + `sample_bits` (`duplex_challenger.rs:264`), rev
    82cfad73cd734d37a0d51953094f970c531817ec.
  * The Lean SPEC it must refine: `FriVerifier.deriveQueryPow` (the transition
    `verifyAlgoO`'s `deriveQueryPowO` evaluates to — `FriVerifierO.deriveQueryPowO_eval`)
    with acceptance `masked = 0` (`FriChallengerUnified.queryPowCheckUnified`).

The emitted leaf (`emitQueryPow n`, deployed `n = 16` — ir2 leaf-wrap
`query_proof_of_work_bits`, part of the 6·19+16 soundness budget): `var 0` = the
grinding challenge; gnark `ToBinary(base, 31)` as bit hints at vars 1–31 (booleanity +
exact recomposition — the `SampleBitsDecomposed` decomposition, exact because every
deployed sample is canonical `< p < 2^31`); zero-pins `bits[i] = 0` for `i < n`
(`grinding.go:84-86`). A witness below the difficulty target yields an UNSATISFIABLE
system — fail-closed, the `FriError::InvalidPowWitness` reject.

The ∀-refinement ladder (theorems, not `#guard`s):

  * `queryPow_refines`      : `gHolds (emitQueryPow n) (powAsg v) ↔
                               v.val < 2^31 ∧ v.val % 2^n = 0` — every `v : Fr`.
  * `queryPow_refines_deriveQueryPow` : at the SPEC transition — `gHolds` at the encoded
    grinding challenge `↔ (deriveQueryPow perm RATE toNat n [w] c).1 = some 0`, for
    EVERY challenger state and witness (any carrier; canonicality of `toNat` on the
    squeeze is the named hypothesis `hs`, true of the deployed BabyBear carrier).
  * `queryPow_refines_deployed`  : the same at the DEPLOYED w16 Poseidon2-BabyBear
    carrier (`Poseidon2BabyBearW16.perm`, KAT-pinned to p3) — `↔ deployedCheckWitness`,
    the `grinding.go` / `grinding_ref.go checkWitness` accept condition.
  * `queryPow_refines_native`    : at the `ChallengerFr.MRef` MultiField twin
    (`CheckWitnessNative`'s carrier, fork-executed-KAT-pinned) — HYPOTHESIS-FREE: the
    observe→squeeze canonicality (`< p`) is PROVEN (`observe_sample_lt`), not assumed.
  * Reject polarity is the `←` face of each iff; `queryPow_rejects_native` states it
    explicitly, and `queryPow_sound_of_boolean` is the adversarial face: ANY witness
    whose hint region is boolean and satisfies the circuit has a challenge with `< 2^31`
    value and zero low `n` bits — no boolean hint fill exists for a failed grind.

Classified seams (same ledger as `CanonicityToy` / the foundation headers):
  * The main iffs quantify over the HONEST hint fill (`powAsg`); the adversarial face is
    `queryPow_sound_of_boolean`, with booleanity-from-`b·b=b` the named Pratt/primality
    seam of `R1csFr`.
  * `hs` (`toNat` squeeze `< 2^31`) at the GENERIC spec instance is the canonical-carrier
    invariant (BabyBear `as_canonical_u64 < p < 2^31`, `challenger.go:113-116`);
    discharged by proof at the MultiField twin, by the gold `#guard`s at w16.
  * `powBits = 0` is the deployed no-op (no observe, no constraint — `grinding.go:71-76`);
    the transcript-tied theorems take `n ≠ 0` (deployed `n = 16`), while
    `queryPow_refines` itself holds at `n = 0` too (`x % 1 = 0`).

Gold KAT anchor (cross-language): the `#guard`s replay the grinding gold vectors computed
by the deployed Go reference itself — `chain/gnark/grinding_ref.go`'s `grindRef` /
`firstRejectingWitness` brute-force oracles (the serial twins of p3 `grind`) at the
`grinding_test.go` `grindPrefix` transcript `[11,22,33,44,55,66,77,88,99,111]`, extracted
2026-07-17: bits=4 → witness 42 / challenge 160998336; bits=10 → 152 / 1292138496;
bits=16 (deployed) → 46542 / 275578880; rejecting witness 0 → challenge 830621580
(low16 = 18316 ≠ 0). If the Lean w16 challenger, the spec transition, or the emitted
circuit diverged from the deployed Go by one bit, these guards fail the build.
-/
import Mathlib.Tactic.LinearCombination
import Dregg2.Tactics
import Dregg2.Circuit.R1csFr
import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.Poseidon2BabyBearW16
import Dregg2.Circuit.ChallengerFr
import Dregg2.Circuit.Emit.GnarkVerifier.EmitFaithful
import Dregg2.Circuit.Emit.GnarkVerifier.CanonicityToy

namespace Dregg2.Circuit.Emit.GnarkVerifier

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.ChallengerFr (MRef bbP splitLimbs)

/-! ## §1 The emitted circuit — `ToBinary(base, 31)` + low-bit zero-pins. -/

/-- The deployed query-grinding difficulty: ir2 leaf-wrap `query_proof_of_work_bits = 16`
(`fri/src/config.rs:82-83`; `docs/deos/ETH-NATIVE-WRAP.md §0`). -/
def deployedPowBits : ℕ := 16

/-- **The QueryPow leaf circuit** at difficulty `n`: `var 0` = the grinding challenge;
the 31-bit `ToBinary` block (booleanity + recomposition, bit hints at vars 1–31 — the
`SampleBitsDecomposed` decomposition, `challenger.go:127-145`); the grinding zero-pins
`AssertIsEqual(bits[i], 0)` for `i < n` (`grinding.go:84-86` / `CheckWitnessNative`). -/
def queryPowCircuit (n : ℕ) : Circuit :=
  ⟨rangeAsserts (.var 0) 1 31
    ++ (List.range n).map fun i => (Wire.var (1 + i), Wire.const (0 : Fr))⟩

/-- **The emission package** — one public input (the transcript-derived grinding
challenge), the recorded gadget invocations, the circuit above. -/
def emitQueryPow (n : ℕ) : GnarkCircuitData :=
  { name         := "fri_query_pow_check_v1"
    publicInputs := [("grindingChallenge", 0)]
    gadgets      := [⟨"SampleBitsDecomposed", [0]⟩,
                     ⟨"AssertPowBitsZero", (List.range n).map (1 + ·)⟩]
    circuit      := queryPowCircuit n }

/-- **The honest hint fill** (the Lean twin of gnark's `ToBinary` hint solver): `var 0` =
the challenge, canonical bits of its value at vars 1–31. -/
def powAsg (v : Fr) : Assignment := fun i =>
  if i = 0 then v else ((v.val / 2 ^ (i - 1) % 2 : ℕ) : Fr)

/-! ## §2 Arithmetic lemmas (local twins of `CanonicityToy`'s private engine, plus the
digit-exact boolean face and the low-bits/mod bridge). -/

private theorem natCast_val_self (v : Fr) : ((v.val : ℕ) : Fr) = v :=
  ZMod.natCast_rightInverse v

/-- Under honest bit hints for `x`, the recomposition wire evaluates to `x % 2^n`. -/
private theorem recompWire_eval_honest (x base : ℕ) (a : Assignment) :
    ∀ n : ℕ, (∀ i, i < n → a (base + i) = ((x / 2 ^ i % 2 : ℕ) : Fr)) →
      (recompWire base n).eval a = ((x % 2 ^ n : ℕ) : Fr)
  | 0, _ => by simp [recompWire, Wire.eval, Nat.mod_one]
  | n + 1, ha => by
      have hih := recompWire_eval_honest x base a n fun i hi => ha i (by omega)
      have hbit := ha n (by omega)
      have hmod : x % 2 ^ (n + 1) = x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2) := by
        rw [pow_succ, Nat.mod_mul]
      simp only [recompWire, Wire.eval, hih, hbit, hmod]
      push_cast
      ring

/-- Under honest bit hints for `x`, the whole `ToBinary` block is satisfied IFF the
checked wire evaluates to `x % 2^n`. -/
private theorem rangeAsserts_honest_iff (w : Wire) (base x n : ℕ) (a : Assignment)
    (ha : ∀ i, i < n → a (base + i) = ((x / 2 ^ i % 2 : ℕ) : Fr)) :
    (∀ p ∈ rangeAsserts w base n, p.1.eval a = p.2.eval a)
      ↔ w.eval a = ((x % 2 ^ n : ℕ) : Fr) := by
  simp only [rangeAsserts]
  constructor
  · intro h
    have hlast := h (w, recompWire base n) (by simp)
    simpa [recompWire_eval_honest x base a n ha] using hlast
  · intro hw p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      have hbit := ha i (List.mem_range.mp hi)
      rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h0 | h0 <;>
        simp [Wire.eval, hbit, h0]
    · have hp' : p = (w, recompWire base n) := by simpa using hp
      subst hp'
      simpa [recompWire_eval_honest x base a n ha] using hw

/-- Under ANY boolean bit fill, the recomposition wire evaluates to SOME `x < 2^n`, and
the fill IS the binary representation of that `x` digit-for-digit — the digit-exact
adversarial-face engine (strengthens the toy's existence form). -/
private theorem recompWire_eval_boolean_digits (base : ℕ) (a : Assignment) :
    ∀ n : ℕ, (∀ i, i < n → a (base + i) = 0 ∨ a (base + i) = 1) →
      ∃ x : ℕ, x < 2 ^ n ∧ (recompWire base n).eval a = (x : Fr) ∧
        ∀ i, i < n → a (base + i) = ((x / 2 ^ i % 2 : ℕ) : Fr)
  | 0, _ => ⟨0, by norm_num, by simp [recompWire, Wire.eval], fun i hi => absurd hi (by omega)⟩
  | n + 1, hb => by
      obtain ⟨x, hx, hev, hdig⟩ :=
        recompWire_eval_boolean_digits base a n fun i hi => hb i (by omega)
      rcases hb n (by omega) with h | h
      · refine ⟨x, lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)), ?_, ?_⟩
        · simp [recompWire, Wire.eval, hev, h]
        · intro i hi
          rcases Nat.lt_or_ge i n with hin | hin
          · exact hdig i hin
          · have hieq : i = n := by omega
            subst hieq
            rw [h, Nat.div_eq_of_lt hx]
            norm_num
      · have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        refine ⟨x + 2 ^ n, by omega, ?_, ?_⟩
        · simp only [recompWire, Wire.eval, hev, h]
          push_cast
          ring
        · intro i hi
          rcases Nat.lt_or_ge i n with hin | hin
          · have hpow : 2 ^ n = 2 ^ i * 2 ^ (n - i) := by
              rw [← pow_add]
              congr 1
              omega
            have hdiv : (x + 2 ^ n) / 2 ^ i = x / 2 ^ i + 2 ^ (n - i) := by
              rw [hpow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
            have hsplit : 2 ^ (n - i) = 2 * 2 ^ (n - i - 1) := by
              rw [← pow_succ']
              congr 1
              omega
            have hmod2 : (x / 2 ^ i + 2 ^ (n - i)) % 2 = x / 2 ^ i % 2 := by
              rw [hsplit, Nat.add_mul_mod_self_left]
            rw [hdiv, hmod2]
            exact hdig i hin
          · have hieq : i = n := by omega
            subst hieq
            rw [Nat.add_div_right x (Nat.two_pow_pos i), Nat.div_eq_of_lt hx]
            simpa using h

/-- `x % 2^n = 0` IFF every low binary digit of `x` below `n` is zero — the bridge
between the per-bit zero-pins and the spec's masked squeeze. -/
private theorem mod_pow_eq_zero_iff (x : ℕ) :
    ∀ n : ℕ, x % 2 ^ n = 0 ↔ ∀ i, i < n → x / 2 ^ i % 2 = 0
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
      have hmod : x % 2 ^ (n + 1) = x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2) := by
        rw [pow_succ, Nat.mod_mul]
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      have ih := mod_pow_eq_zero_iff x n
      constructor
      · intro h
        have hcomp : x % 2 ^ n = 0 ∧ x / 2 ^ n % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ n) with hd | hd <;>
            rw [hd] at hmod <;> constructor <;> omega
        intro i hi
        rcases Nat.lt_or_ge i n with hin | hin
        · exact ih.mp hcomp.1 i hin
        · have hieq : i = n := by omega
          subst hieq
          exact hcomp.2
      · intro h
        have h1 : x % 2 ^ n = 0 := ih.mpr fun i hi => h i (by omega)
        have h2 : x / 2 ^ n % 2 = 0 := h n (by omega)
        rw [h2] at hmod
        omega

/-- The zero-pin block is satisfied IFF every pinned hint variable is zero. -/
private theorem zeroPins_iff (n : ℕ) (a : Assignment) :
    (∀ p ∈ (List.range n).map (fun i => (Wire.var (1 + i), Wire.const (0 : Fr))),
        p.1.eval a = p.2.eval a)
      ↔ ∀ i, i < n → a (1 + i) = 0 := by
  constructor
  · intro h i hi
    have := h (Wire.var (1 + i), Wire.const 0)
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simpa [Wire.eval] using this
  · intro h p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    simpa [Wire.eval] using h i (List.mem_range.mp hi)

/-! ## §3 The frontend ∀-theorem. -/

/-- The QueryPow circuit under the honest hint fill accepts EXACTLY the values that fit
31 bits and have zero low `n` bits — for every `v : Fr`. -/
theorem queryPow_frontend (n : ℕ) (hn : n ≤ 31) (v : Fr) :
    (queryPowCircuit n).satisfied (powAsg v) ↔ v.val < 2 ^ 31 ∧ v.val % 2 ^ n = 0 := by
  have hvr : v.val < rBN254 := ZMod.val_lt v
  have ha1 : ∀ i : ℕ, i < 31 → powAsg v (1 + i) = ((v.val / 2 ^ i % 2 : ℕ) : Fr) := by
    intro i hi
    have h0 : ¬(1 + i = 0) := by omega
    have h2 : 1 + i - 1 = i := by omega
    simp only [powAsg, if_neg h0, h2]
  have hv0 : powAsg v 0 = v := by simp [powAsg]
  show (∀ p ∈ (queryPowCircuit n).asserts, p.1.eval (powAsg v) = p.2.eval (powAsg v)) ↔ _
  simp only [queryPowCircuit]
  rw [List.forall_mem_append, rangeAsserts_honest_iff _ 1 v.val 31 _ ha1, zeroPins_iff]
  simp only [Wire.eval, hv0]
  constructor
  · rintro ⟨h1, h2⟩
    have hval31 : v.val < 2 ^ 31 := by
      have hm : v.val % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
      have h1' := congrArg ZMod.val h1
      rw [ZMod.val_cast_of_lt (a := v.val % 2 ^ 31)
        (lt_of_le_of_lt (Nat.mod_le _ _) hvr)] at h1'
      omega
    refine ⟨hval31, (mod_pow_eq_zero_iff v.val n).mpr ?_⟩
    intro i hi
    have hbit := h2 i hi
    rw [ha1 i (by omega)] at hbit
    rcases Nat.mod_two_eq_zero_or_one (v.val / 2 ^ i) with h0 | h0
    · exact h0
    · rw [h0] at hbit
      exact absurd hbit (by norm_num)
  · rintro ⟨h31, hmod⟩
    refine ⟨?_, ?_⟩
    · rw [Nat.mod_eq_of_lt h31, natCast_val_self]
    · intro i hi
      rw [ha1 i (by omega), (mod_pow_eq_zero_iff v.val n).mp hmod i hi]
      norm_num

/-! ## §4 THE LEAF ∀-REFINEMENT — the deliverable. -/

/-- **`queryPow_refines`** — the leaf ∀-refinement: the LOWERED genuine R1CS of the
emitted QueryPow package, under the canonical witness extension of the honest hint fill,
is satisfied IFF the challenge value fits 31 bits AND its low `n` bits are all zero —
for EVERY `v : Fr`. The `< 2^31` conjunct is itself deployed content: gnark's
`ToBinary(base, 31)` constrains the decomposition, so an out-of-range challenge is
UNSATISFIABLE, exactly as in `grinding.go`. -/
theorem queryPow_refines (n : ℕ) (hn : n ≤ 31) (v : Fr) :
    gHolds (emitQueryPow n) (powAsg v) ↔ v.val < 2 ^ 31 ∧ v.val % 2 ^ n = 0 := by
  unfold gHolds
  rw [← R1csFr.gHolds]
  exact queryPow_frontend n hn v

/-- The same ∀-refinement at the EMITTED wire form (composing `emit_faithful`). -/
theorem queryPow_refines_emitted (n : ℕ) (hn : n ≤ 31) (v : Fr) :
    satisfiedEmitted (emit (emitQueryPow n)) (powAsg v)
      ↔ v.val < 2 ^ 31 ∧ v.val % 2 ^ n = 0 :=
  (emit_faithful (emitQueryPow n) (powAsg v)).symm.trans (queryPow_refines n hn v)

/-- **The adversarial face** (modulo booleanity — the named Pratt/primality seam): ANY
witness whose hint region 1–31 is boolean and which satisfies the circuit carries a
challenge that fits 31 bits and passed the grind. No boolean hint fill exists for a
challenge with a nonzero low bit. -/
theorem queryPow_sound_of_boolean (n : ℕ) (hn : n ≤ 31) (a : Assignment)
    (hbool : ∀ i : ℕ, 1 ≤ i → i ≤ 31 → a i = 0 ∨ a i = 1)
    (hsat : (queryPowCircuit n).satisfied a) :
    (a 0).val < 2 ^ 31 ∧ (a 0).val % 2 ^ n = 0 := by
  have hsat' : ∀ p ∈ (queryPowCircuit n).asserts, p.1.eval a = p.2.eval a := hsat
  simp only [queryPowCircuit] at hsat'
  rw [List.forall_mem_append] at hsat'
  obtain ⟨hs1, hs2⟩ := hsat'
  obtain ⟨x, hx, hev, hdig⟩ := recompWire_eval_boolean_digits 1 a 31
    (fun i hi => hbool (1 + i) (by omega) (by omega))
  have hlast := hs1 (Wire.var 0, recompWire 1 31) (by simp [rangeAsserts])
  simp only [Wire.eval] at hlast
  rw [hev] at hlast
  have hxr : x < rBN254 := lt_trans hx (by norm_num [rBN254])
  have hval : (a 0).val = x := by
    rw [hlast, ZMod.val_cast_of_lt hxr]
  refine ⟨by rw [hval]; exact hx, ?_⟩
  rw [hval]
  refine (mod_pow_eq_zero_iff x n).mpr fun i hi => ?_
  have hz := (zeroPins_iff n a).mp hs2 i hi
  have hd := hdig i (by omega)
  rw [hz] at hd
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h0 | h0
  · exact h0
  · rw [h0] at hd
    exact absurd hd.symm (by norm_num)

/-! ## §5 Refinement AGAINST THE SPEC — `FriVerifier.deriveQueryPow` (the transition
`verifyAlgoO` executes; acceptance `= some 0` is `queryPowCheckUnified`). -/

/-- The transcript-derived grinding challenge: the base squeeze drawn immediately after
absorbing the PoW witness (`grinding_challenger.rs:44-45`, `grinding.go:78-83`). -/
def grindingChallenge {F : Type} [Inhabited F] (perm : List F → List F) (RATE : ℕ)
    (c : FriVerifier.Challenger F) (w : F) : F :=
  (FriVerifier.Challenger.sampleBase perm RATE (FriVerifier.Challenger.observe perm RATE c w)).1

/-- **The spec-level ∀-refinement.** For EVERY challenger state `c`, witness `w`, carrier
`(F, perm, RATE, toNat)`: the emitted R1CS at the encoded grinding challenge is satisfied
IFF the spec's query-PoW transition accepts (`deriveQueryPow … = some 0` — the
`queryPowCheckUnified` accept). `hs` is the canonical-carrier fact (`as_canonical_u64 <
p < 2^31` for deployed BabyBear); it is PROVEN, not assumed, at the MultiField twin
(`queryPow_refines_native`). -/
theorem queryPow_refines_deriveQueryPow {F : Type} [Inhabited F]
    (perm : List F → List F) (RATE : ℕ) (toNat : F → ℕ) (n : ℕ)
    (hn0 : n ≠ 0) (hn : n ≤ 31) (c : FriVerifier.Challenger F) (w : F)
    (hs : toNat (grindingChallenge perm RATE c w) < 2 ^ 31) :
    gHolds (emitQueryPow n) (powAsg ((toNat (grindingChallenge perm RATE c w) : ℕ) : Fr))
      ↔ (FriVerifier.deriveQueryPow perm RATE toNat n [w] c).1 = some 0 := by
  rcases hsb : FriVerifier.Challenger.sampleBase perm RATE
      (FriVerifier.Challenger.observe perm RATE c w) with ⟨v, c2⟩
  have hv : grindingChallenge perm RATE c w = v := by
    rw [grindingChallenge, hsb]
  rw [hv] at hs ⊢
  have hsr : toNat v < rBN254 := lt_trans hs (by norm_num [rBN254])
  have hval : ((toNat v : ℕ) : Fr).val = toNat v := ZMod.val_cast_of_lt hsr
  have hrhs : (FriVerifier.deriveQueryPow perm RATE toNat n [w] c).1
      = some (toNat v % 2 ^ n) := by
    simp only [FriVerifier.deriveQueryPow, if_neg hn0, FriVerifier.Challenger.sampleBits, hsb]
  rw [queryPow_refines n hn, hval, hrhs]
  constructor
  · rintro ⟨-, h⟩
    rw [h]
  · intro h
    exact ⟨hs, Option.some.inj h⟩

/-! ## §6 The DEPLOYED carrier — the w16 Poseidon2-BabyBear duplex challenger
(`Poseidon2BabyBearW16.perm`, KAT-pinned to p3), i.e. `grinding.go`'s transcript. -/

/-- The deployed w16 permutation (KAT-pinned bit-exact in `Poseidon2BabyBearW16`). -/
def w16Perm : List ℕ → List ℕ := Dregg2.Circuit.Poseidon2BabyBearW16.perm

/-- **The deployed QueryPow check** — p3 `check_witness` / `grinding_ref.go checkWitness`
at the deployed carrier (w16 perm, RATE 8, canonical-ℕ `toNat = id`): `true` IFF the spec
transition yields a zero masked squeeze. `powBits = 0` is the deployed unconditional
pass. -/
def deployedCheckWitness (powBits : ℕ) (c : FriVerifier.Challenger ℕ) (w : ℕ) : Bool :=
  match (FriVerifier.deriveQueryPow w16Perm 8 id powBits [w] c).1 with
  | some masked => decide (masked = 0)
  | none => false

private theorem deployedCheckWitness_iff (n : ℕ) (c : FriVerifier.Challenger ℕ) (w : ℕ) :
    deployedCheckWitness n c w = true
      ↔ (FriVerifier.deriveQueryPow w16Perm 8 id n [w] c).1 = some 0 := by
  unfold deployedCheckWitness
  rcases (FriVerifier.deriveQueryPow w16Perm 8 id n [w] c).1 with _ | m
  · simp
  · simp

/-- **The deployed QueryPow ∀-refinement**: at the w16 carrier, for EVERY transcript
state and witness, the emitted R1CS at the grinding challenge accepts IFF the deployed
`check_witness` does. `hs` is the BabyBear canonicality of the squeeze (`< p < 2^31`),
exhibited concretely by the gold `#guard`s below. -/
theorem queryPow_refines_deployed (n : ℕ) (hn0 : n ≠ 0) (hn : n ≤ 31)
    (c : FriVerifier.Challenger ℕ) (w : ℕ)
    (hs : grindingChallenge w16Perm 8 c w < 2 ^ 31) :
    gHolds (emitQueryPow n) (powAsg ((grindingChallenge w16Perm 8 c w : ℕ) : Fr))
      ↔ deployedCheckWitness n c w = true := by
  rw [deployedCheckWitness_iff]
  exact queryPow_refines_deriveQueryPow w16Perm 8 id n hn0 hn c w hs

/-! ## §7 The MultiField twin (`CheckWitnessNative`, `fri_verify_native.go:251`) —
HYPOTHESIS-FREE: squeeze canonicality is proven from `ChallengerFr.MRef`. -/

private theorem splitLimbs_lt (v : Fr) : ∀ x ∈ splitLimbs v, x < bbP := by
  intro x hx
  simp only [splitLimbs, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact Nat.mod_lt _ (by norm_num [bbP])

private theorem getLastD_lt {b : ℕ} (hb : 0 < b) :
    ∀ l : List ℕ, (∀ x ∈ l, x < b) → l.getLast?.getD 0 < b := by
  intro l
  induction l with
  | nil => intro _; simpa using hb
  | cons x xs ih =>
      intro hl
      cases xs with
      | nil => simpa using hl x (by simp)
      | cons y ys =>
          rw [List.getLast?_cons_cons]
          exact ih fun z hz => hl z (by simp [hz])

private theorem flush_fSq_lt (m : MRef) (hsq : ∀ x ∈ m.fSq, x < bbP) :
    ∀ x ∈ m.flush.fSq, x < bbP := by
  unfold MRef.flush
  split
  · exact hsq
  · intro x hx
    simp at hx

/-- Every value the MultiField squeeze can pop is a split limb — canonical `< p`. -/
private theorem sampleBB_lt (m : MRef) (hsq : ∀ x ∈ m.fSq, x < bbP) :
    (m.sampleBB).1 < bbP := by
  have hbP : 0 < bbP := by norm_num [bbP]
  have hflush := flush_fSq_lt m hsq
  unfold MRef.sampleBB
  cases hemp : m.flush.fSq.isEmpty <;> simp only [hemp]
  · simp only [Bool.false_eq_true, if_false]
    exact getLastD_lt hbP _ hflush
  · simp only [if_true]
    apply getLastD_lt hbP
    intro x hx
    simp only [List.mem_flatten, List.mem_map] at hx
    obtain ⟨l, ⟨v, -, rfl⟩, hxl⟩ := hx
    exact splitLimbs_lt v x hxl

private theorem observeBB_fSq (m : MRef) (w : ℕ) : (m.observeBB w).fSq = [] := by
  unfold MRef.observeBB
  dsimp only
  split
  · unfold MRef.flush
    split
    · rfl
    · rfl
  · rfl

/-- **Squeeze canonicality after an observe** — the fact `CheckWitnessNative` relies on
(`multifield_challenger.go`: SampleBits requires the base sample canonical `< p`), here a
THEOREM for every state and witness. -/
theorem observe_sample_lt (m : MRef) (w : ℕ) : ((m.observeBB w).sampleBB).1 < bbP :=
  sampleBB_lt _ (by rw [observeBB_fSq]; intro x hx; simp at hx)

/-- p3 `check_witness` over the KAT-pinned MultiField challenger twin — the accept
condition of `CheckWitnessNative` (`fri_verify_native.go:251-261`): observe the witness,
then the low `n` bits of the next BabyBear squeeze must all be zero. -/
def checkWitnessNativeRef (n : ℕ) (m : MRef) (w : ℕ) : Bool :=
  if n = 0 then true
  else decide (((m.observeBB w).sampleBits n).1 = 0)

/-- **The hypothesis-free transcript ∀-refinement** — for EVERY MultiField challenger
state `m` and witness `w`: the emitted R1CS at the transcript-derived grinding challenge
is satisfied IFF the deployed native check accepts. Canonicality is `observe_sample_lt`;
nothing is assumed. -/
theorem queryPow_refines_native (n : ℕ) (hn0 : n ≠ 0) (hn : n ≤ 31) (m : MRef) (w : ℕ) :
    gHolds (emitQueryPow n) (powAsg ((((m.observeBB w).sampleBB).1 : ℕ) : Fr))
      ↔ checkWitnessNativeRef n m w = true := by
  have hsP : ((m.observeBB w).sampleBB).1 < bbP := observe_sample_lt m w
  have hs31 : ((m.observeBB w).sampleBB).1 < 2 ^ 31 := lt_trans hsP (by norm_num [bbP])
  have hsr : ((m.observeBB w).sampleBB).1 < rBN254 := lt_trans hs31 (by norm_num [rBN254])
  have hval : ((((m.observeBB w).sampleBB).1 : ℕ) : Fr).val = ((m.observeBB w).sampleBB).1 :=
    ZMod.val_cast_of_lt hsr
  have hbits : ((m.observeBB w).sampleBits n).1 = ((m.observeBB w).sampleBB).1 % 2 ^ n := by
    rcases hsb : (m.observeBB w).sampleBB with ⟨v, m2⟩
    simp [MRef.sampleBits, hsb]
  rw [queryPow_refines n hn, hval]
  simp only [checkWitnessNativeRef, if_neg hn0, hbits, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨hs31, h⟩⟩

/-- **The reject polarity, explicitly**: a witness the deployed native check refuses (a
failed grind) admits NO satisfying assignment — the emitted R1CS is unsatisfiable under
the honest fill at its own transcript-derived challenge (`FriError::InvalidPowWitness`,
fail-closed). -/
theorem queryPow_rejects_native (n : ℕ) (hn0 : n ≠ 0) (hn : n ≤ 31) (m : MRef) (w : ℕ)
    (hbad : checkWitnessNativeRef n m w = false) :
    ¬ gHolds (emitQueryPow n) (powAsg ((((m.observeBB w).sampleBB).1 : ℕ) : Fr)) := by
  rw [queryPow_refines_native n hn0 hn m w, hbad]
  simp

/-- The native transcript refinement at the EMITTED wire form. -/
theorem queryPow_refines_native_emitted (n : ℕ) (hn0 : n ≠ 0) (hn : n ≤ 31)
    (m : MRef) (w : ℕ) :
    satisfiedEmitted (emit (emitQueryPow n)) (powAsg ((((m.observeBB w).sampleBB).1 : ℕ) : Fr))
      ↔ checkWitnessNativeRef n m w = true :=
  (emit_faithful _ _).symm.trans (queryPow_refines_native n hn0 hn m w)

#assert_axioms queryPow_frontend
#assert_axioms queryPow_refines
#assert_axioms queryPow_refines_emitted
#assert_axioms queryPow_sound_of_boolean
#assert_axioms queryPow_refines_deriveQueryPow
#assert_axioms queryPow_refines_deployed
#assert_axioms observe_sample_lt
#assert_axioms queryPow_refines_native
#assert_axioms queryPow_rejects_native
#assert_axioms queryPow_refines_native_emitted

/-! ## §8 Teeth — the cross-language gold KAT (`chain/gnark/grinding_ref.go` oracles at
the `grinding_test.go` prefix; provenance in the header) + executable both-polarity
samples at the MultiField twin. The ∀-theorems above subsume these; the guards pin that
the DEFINITIONS compute and that the Lean carriers match the deployed Go bit-for-bit. -/

/-- The `grinding_test.go` transcript prefix (one full-rate duplexing, two buffered). -/
def w16GrindState : FriVerifier.Challenger ℕ :=
  FriVerifier.Challenger.observeList w16Perm 8
    (FriVerifier.Challenger.init (List.replicate 16 0))
    [11, 22, 33, 44, 55, 66, 77, 88, 99, 111]

-- ACCEPT (gold): the Go-ground witnesses land challenges with cleared low bits, and the
-- Lean spec instance reproduces the exact Go challenge values.
#guard grindingChallenge w16Perm 8 w16GrindState 46542 = 275578880
#guard deployedCheckWitness 16 w16GrindState 46542 = true
#guard grindingChallenge w16Perm 8 w16GrindState 152 = 1292138496
#guard deployedCheckWitness 10 w16GrindState 152 = true
#guard grindingChallenge w16Perm 8 w16GrindState 42 = 160998336
#guard deployedCheckWitness 4 w16GrindState 42 = true
-- REJECT (gold): the Go first-rejecting witness 0 → challenge 830621580, low16 = 18316.
#guard grindingChallenge w16Perm 8 w16GrindState 0 = 830621580
#guard 830621580 % 2 ^ 16 = 18316
#guard deployedCheckWitness 16 w16GrindState 0 = false
#guard deployedCheckWitness 4 w16GrindState 0 = false
-- The emitted circuit AT the gold transcript-derived challenges — both polarities, at
-- the frontend and at the emitted wire form (the theorems carry these to genuine R1CS).
#guard (queryPowCircuit 16).satisfied (powAsg ((275578880 : ℕ) : Fr))
#guard ¬ (queryPowCircuit 16).satisfied (powAsg ((830621580 : ℕ) : Fr))
#guard satisfiedEmitted (emit (emitQueryPow 16)) (powAsg ((275578880 : ℕ) : Fr))
#guard ¬ satisfiedEmitted (emit (emitQueryPow 16)) (powAsg ((830621580 : ℕ) : Fr))
-- The 0-bit degenerate face: no pins, acceptance = 31-bit range only.
#guard (queryPowCircuit 0).satisfied (powAsg ((830621580 : ℕ) : Fr))

/-- The fork-gold MultiField prefix (`multifield_challenger_test.go` protocol head). -/
def mfPrefix : MRef := ({} : MRef).observeBBs [11, 22, 33]

/-- Brute-force grind over the MultiField twin (the `grindRef` serial-oracle shape). -/
def grindNative (n bound : ℕ) (m : MRef) : Option ℕ :=
  (List.range bound).find? fun w => checkWitnessNativeRef n m w

def mfGoodW4 : ℕ := (grindNative 4 512 mfPrefix).getD 0
def mfBadW4 : ℕ := ((List.range 512).find? fun w => !checkWitnessNativeRef 4 mfPrefix w).getD 0

-- ACCEPT: a real ground witness passes the native check AND the emitted circuit at its
-- transcript-derived challenge. REJECT: a failed grind refutes both.
#guard checkWitnessNativeRef 4 mfPrefix mfGoodW4 = true
#guard (queryPowCircuit 4).satisfied
  (powAsg ((((mfPrefix.observeBB mfGoodW4).sampleBB).1 : ℕ) : Fr))
#guard checkWitnessNativeRef 4 mfPrefix mfBadW4 = false
#guard ¬ (queryPowCircuit 4).satisfied
  (powAsg ((((mfPrefix.observeBB mfBadW4).sampleBB).1 : ℕ) : Fr))

end Dregg2.Circuit.Emit.GnarkVerifier
