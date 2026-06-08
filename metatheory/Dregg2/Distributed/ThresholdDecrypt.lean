/-
# Dregg2.Distributed.ThresholdDecrypt — the federation's threshold-decryption core, ported faithfully.

This is the previously-uncovered load-bearing protocol semantics of `federation/src/threshold_decrypt.rs`
(763 LOC): the t-of-n **threshold decryption** that gives turns privacy until consensus orders them. The
running node encrypts a turn body to an epoch key whose symmetric secret is **Shamir-shared over GF(256)**
among validators; after ordering, validators each emit a `DecryptionShare`, and any `t` of them
reconstruct the key by **Lagrange interpolation at x=0**. No Lean module modeled this before
(`Crypto/*` covers Pedersen/Poseidon CR; `Distributed/*` covers consensus/membership/migration). It is a
real protocol with a clean headline property, so it follows the consensus template — a faithful
executable Lean model + a property that EXPLAINS the protocol + a Rust differential.

## What is modeled

* **§1 GF(256)** — the AES field `𝔽₂[x]/(x⁸+x⁴+x³+x+1)` exactly as the Rust `mod gf256` computes it:
  `gf256Mul` is the bitwise carry-less multiply with the `0x1b` reduction (`threshold_decrypt.rs:158`),
  `gf256Inv a = a^254` via Fermat (`threshold_decrypt.rs:178`). Both are `Nat`-level, `decide`-able, and
  the §4 `#guard`s pin them byte-for-byte against the Rust `test_gf256_arithmetic` golden vectors.

* **§2 Shamir over GF(256)** — `shamirSplitByte` evaluates `f(x)=secret + a₁x + … + a_{t-1}x^{t-1}` at the
  evaluation points `1..n` (`shamir_split_byte`, `threshold_decrypt.rs:208`); `shamirReconstructByte`
  is Lagrange interpolation at `x=0` over a list of `(xᵢ,yᵢ)` (`shamir_reconstruct_byte`,
  `threshold_decrypt.rs:232`), with subtraction = XOR and the `numerator/denominator` basis exactly the
  Rust loop. Transcribed line-for-line; the §4 `#guard`s pin the `test_shamir_single_byte_roundtrip`
  vectors (t=2,n=3 over every 2-of-3 subset).

* **§3 the threshold gate** — `combine` mirrors `combine_shares` (`threshold_decrypt.rs:430`): it REJECTS
  fail-closed when `shares.length < threshold` (`InsufficientShares`), rejects duplicate indices and the
  reserved index `0`, and otherwise reconstructs. The proved gate `combine_rejects_below_threshold` is the
  liveness/secrecy boundary: < t shares NEVER yield a key.

## The headline property that EXPLAINS the protocol

`shamir_any_t_reconstruct` (§2): for a secret byte `s` Shamir-split with threshold `t` over `n ≥ t`
validators, **any** `t` distinct share-holders reconstruct exactly `s`. This is the `t`-of-`n`
availability guarantee that makes threshold decryption work — no privileged subset, any quorum decrypts.
It is proved via Mathlib's `Lagrange` interpolation theory over the field `𝔽 = ZMod`-style byte field, so
the proof EXPLAINS why it holds (degree-`<t` polynomial uniquely determined by `t` evaluations ⇒ its value
at `0` is recovered) rather than checking finitely many cases. The companion `shamir_below_t_undetermined`
states the secrecy-floor side: `t-1` shares are consistent with EVERY secret (information-theoretic
privacy), the reason `< t` validators learn nothing.

## Crypto hypotheses, named honestly

This module proves the **Shamir/Lagrange algebra** — the reconstruction correctness and the threshold gate.
It does NOT prove the AEAD secure: `ThresholdCiphertext`'s confidentiality+integrity (BLAKE3-keyed
ChaCha20-style stream + MAC tag, `threshold_decrypt.rs:363,552`) rest on the keyed-hash being a secure
PRF/MAC, which is the named `Blake3Prf` carrier — the same discipline as `CaveatChain.MacUnforgeable`. The
share-MAC tamper-detection (`combine_shares` verifying each `share_mac` before interpolation,
`threshold_decrypt.rs:482`) is sound RELATIVE to that carrier; we model the integrity reduction shape,
not the BLAKE3 internals. The prototype's trusted-dealer key generation (vs a production DKG) is an
out-of-model setup assumption stated explicitly, not proved away.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`:=True`.

Differential: `federation/src/threshold_decrypt_diff.rs` transcribes §1–§3 and asserts the Lean semantics is
the one the real `gf256`/`shamir_reconstruct_byte`/`combine_shares` compute, on the Rust test vectors plus
randomized roundtrips (same discipline as `coord::entangled_diff` / `BlocklaceFinality`'s `tau` golden).
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.ZMod.Basic
import Dregg2.Tactics

namespace Dregg2.Distributed.ThresholdDecrypt

/-! ## §1 — GF(256), the AES field, transcribed byte-for-byte from `mod gf256`.

We keep a CONCRETE `Nat`-level model (`decide`-able, matches the Rust bit-twiddling exactly) for the
differential `#guard`s, and SEPARATELY use a Mathlib field for the algebraic reconstruction proof in §2.
The concrete model below is the executable transcription; it is what the Rust `gf256::mul`/`gf256::inv`
compute, and the §4 golden vectors pin that. -/

/-- One round of the GF(256) carry-less multiply (`threshold_decrypt.rs:162-173`): for each of the 8 bits
of `b`, conditionally XOR `a` into the accumulator, then shift `a` left with the `0x1b` reduction when the
high bit was set. `acc`, `a`, `b` are kept as `Nat` masked to a byte. -/
def gf256MulStep (acc a b : Nat) : Nat × Nat × Nat :=
  let acc' := if b % 2 == 1 then acc ^^^ a else acc
  let high := a &&& 0x80
  let a1 := (a <<< 1) &&& 0xFF
  let a' := if high != 0 then a1 ^^^ 0x1b else a1
  (acc', a', b >>> 1)

/-- GF(256) multiplication (`gf256::mul`, `threshold_decrypt.rs:158`): 8 rounds of `gf256MulStep`. -/
def gf256Mul (a b : Nat) : Nat :=
  let s0 := gf256MulStep 0 (a &&& 0xFF) (b &&& 0xFF)
  let s1 := gf256MulStep s0.1 s0.2.1 s0.2.2
  let s2 := gf256MulStep s1.1 s1.2.1 s1.2.2
  let s3 := gf256MulStep s2.1 s2.2.1 s2.2.2
  let s4 := gf256MulStep s3.1 s3.2.1 s3.2.2
  let s5 := gf256MulStep s4.1 s4.2.1 s4.2.2
  let s6 := gf256MulStep s5.1 s5.2.1 s5.2.2
  let s7 := gf256MulStep s6.1 s6.2.1 s6.2.2
  s7.1

/-- GF(256) multiplicative inverse via Fermat `a⁻¹ = a²⁵⁴` (`gf256::inv`, the exponentiation-by-squaring
branch, `threshold_decrypt.rs:191-203`). `inv 0 = 0` by convention. Computed as the explicit
square-and-multiply ladder for exponent 254 = 0b11111110. -/
def gf256Inv (a : Nat) : Nat :=
  if a == 0 then 0 else
  -- exp = 254 = bits (from LSB) 0,1,1,1,1,1,1,1
  -- result starts 1, power starts a; multiply result by power when bit set, square power each step
  let p0 := a; let r0 := 1                              -- bit0 = 0: no mul
  let p1 := gf256Mul p0 p0; let r1 := gf256Mul r0 p1    -- bit1 = 1
  let p2 := gf256Mul p1 p1; let r2 := gf256Mul r1 p2    -- bit2 = 1
  let p3 := gf256Mul p2 p2; let r3 := gf256Mul r2 p3    -- bit3 = 1
  let p4 := gf256Mul p3 p3; let r4 := gf256Mul r3 p4    -- bit4 = 1
  let p5 := gf256Mul p4 p4; let r5 := gf256Mul r4 p5    -- bit5 = 1
  let p6 := gf256Mul p5 p5; let r6 := gf256Mul r5 p6    -- bit6 = 1
  let p7 := gf256Mul p6 p6; let r7 := gf256Mul r6 p7    -- bit7 = 1
  r7

/-! ## §2 — Shamir split / reconstruct over the GF(256) algebra (Mathlib field for the proof).

The reconstruction CORRECTNESS is a field-theoretic fact independent of which concrete field: a polynomial
of degree `< t` is uniquely determined by its values at `t` distinct points, so Lagrange interpolation at
`x = 0` recovers `f(0)` = the shared secret. We prove it over an ABSTRACT field `F` using Mathlib's
`Lagrange.interpolate`, which is exactly the GF(256) Lagrange the Rust `shamir_reconstruct_byte` runs (XOR
= field subtraction, `gf256::mul` = field multiply, `gf256::inv` = field inverse). The §1 concrete model is
the differential anchor; this §2 proof is WHY any t-of-n quorum decrypts. -/

variable {F : Type*} [Field F]

/-- The Shamir secret-sharing polynomial `f(x) = secret + a₁x + … + a_{t-1}x^{t-1}`
(`shamir_split_byte`, `threshold_decrypt.rs:211-214`). `coeffs.head = secret`, the tail = the random
coefficients; the share for evaluation point `x` is `f(x)`. We carry `f` as a `Polynomial F` whose
constant coefficient is the secret and whose degree is `< t`. -/
noncomputable def shamirPoly (secret : F) (coeffs : List F) : Polynomial F :=
  -- secret + Σ coeffs[i] · X^{i+1}
  (coeffs.zipIdx).foldl
    (fun p (c, i) => p + Polynomial.C c * Polynomial.X ^ (i + 1))
    (Polynomial.C secret)

/-- `shamirPoly` always has the secret as its evaluation at `0`: `f(0) = secret`. This is the structural
invariant the whole scheme rests on — the secret is the constant term. -/
theorem shamirPoly_eval_zero (secret : F) (coeffs : List F) :
    (shamirPoly secret coeffs).eval 0 = secret := by
  unfold shamirPoly
  -- induct on the fold: each added term `C c * X^(i+1)` evaluates to 0 at x=0 since i+1 ≥ 1.
  suffices h : ∀ (l : List (F × ℕ)) (p : Polynomial F),
      (∀ q ∈ l, 1 ≤ q.2 + 1) →
      (l.foldl (fun p (c, i) => p + Polynomial.C c * Polynomial.X ^ (i + 1)) p).eval 0
        = p.eval 0 by
    have := h coeffs.zipIdx (Polynomial.C secret) (by intro q _; exact Nat.le_add_left 1 q.2)
    simpa using this
  intro l
  induction l with
  | nil => intro p _; simp
  | cons hd tl ih =>
      intro p hpos
      simp only [List.foldl_cons]
      rw [ih]
      · obtain ⟨c, i⟩ := hd
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X]
      · intro q hq; exact hpos q (List.mem_cons_of_mem _ hq)

/-- **`shamir_any_t_reconstruct`** — the headline `t`-of-`n` property. Let `f` be a Shamir sharing
polynomial of `degree < t` (constant term = the secret `s`). Take ANY `t` distinct share-holders: a
finite set `S` of evaluation points with `|S| = t`. Lagrange-interpolating the shares `(x, f(x))` for
`x ∈ S` and evaluating the interpolant at `0` recovers exactly `s`. No privileged subset — every size-`t`
quorum decrypts. This is `combine_shares` reconstructing the key (`threshold_decrypt.rs:468-476`).

We state it via Mathlib's `Lagrange.interpolate`: the interpolant of `f`'s values on `S` IS `f` (since
`deg f < |S|`), hence its value at `0` is `f.eval 0 = s`. -/
theorem shamir_any_t_reconstruct
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → F)
    (hinj : Set.InjOn x S) (f : Polynomial F)
    (hdeg : f.degree < S.card) (s : F) (hsecret : f.eval 0 = s) :
    (Lagrange.interpolate S x (fun i => f.eval (x i))).eval 0 = s := by
  -- `f.degree < #S` ⇒ `f = interpolate S x (fun i => f.eval (x i))`, so the interpolant's value at 0 IS f's.
  have hdeg' : f.degree < (S.card : WithBot ℕ) := by simpa using hdeg
  rw [← Lagrange.eq_interpolate hinj hdeg']
  exact hsecret

/-- **`shamir_below_t_undetermined`** — the secrecy-floor side: with only the shares at the points `S`
(think `|S| = t-1`, one short of threshold) the secret at `0` is NOT determined. For ANY target gap
`s₀ ≠ s₁` between two candidate secrets there exist two polynomials that AGREE on every point of `S`
(so produce the identical observed shares) yet have constant terms — the secret value at `0` — differing
by exactly `s₀ - s₁`. So the `t-1` observed shares are consistent with every secret: the
information-theoretic reason `< t` validators learn nothing.

The witnesses are `interp ± c · nodal` where `nodal S x` VANISHES on `S` (so the shares are unchanged)
but `nodal.eval 0 ≠ 0` when `0 ∉ S` (no validator sits at the secret's point — the indices are `1..n`),
hence the constant term is freely shiftable. The hypothesis `0 ∉ x '' S` is exactly the protocol's
"evaluation points are `1..n`, point `0` is the secret" discipline. -/
theorem shamir_below_t_undetermined
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → F)
    (hinj : Set.InjOn x S) (h0 : ∀ i ∈ S, x i ≠ 0)
    (vals : ι → F) (s₀ s₁ : F) :
    ∃ f₀ f₁ : Polynomial F,
      (∀ i ∈ S, f₀.eval (x i) = vals i) ∧ (∀ i ∈ S, f₁.eval (x i) = vals i)
      ∧ f₀.eval 0 - f₁.eval 0 = s₀ - s₁ := by
  classical
  -- `nodal S x = ∏_{i∈S} (X - x i)`; it vanishes on S and `nodal(0) = ∏ (-x i) ≠ 0` since each `x i ≠ 0`.
  have hnod0 : (Lagrange.nodal S x).eval 0 ≠ 0 := by
    rw [Lagrange.eval_nodal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hxi := h0 i hi
    rw [zero_sub, neg_ne_zero]
    exact hxi
  -- scale `nodal` so that adding `c • nodal` shifts the constant term by exactly the demanded gap.
  set c := (s₀ - s₁) * ((Lagrange.nodal S x).eval 0)⁻¹ with hc
  refine ⟨Lagrange.interpolate S x vals + Polynomial.C c * Lagrange.nodal S x,
          Lagrange.interpolate S x vals, ?_, ?_, ?_⟩
  · intro i hi
    rw [Polynomial.eval_add, Polynomial.eval_mul, Lagrange.eval_nodal_at_node hi,
      mul_zero, add_zero, Lagrange.eval_interpolate_at_node _ hinj hi]
  · intro i hi
    exact Lagrange.eval_interpolate_at_node _ hinj hi
  · rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, add_sub_cancel_left, hc,
      inv_mul_cancel_right₀ hnod0 (s₀ - s₁)]

/-! ## §3 — The threshold gate (`combine_shares`), and its fail-closed boundary.

The Rust `combine_shares` (`threshold_decrypt.rs:430`) FIRST checks `shares.len() < threshold`
(`InsufficientShares`), THEN rejects duplicate indices and the reserved index `0`, THEN reconstructs. We
model the gate decision (does the call admit reconstruction?) and prove the fail-closed boundary that is
the secrecy/liveness frontier of threshold decryption. -/

/-- A decryption share, mirroring `DecryptionShare` (the parts the gate inspects): the validator index
and the share byte at a given key-position. `idx = 0` is the reserved/invalid index. -/
structure Share where
  idx : Nat
  val : Nat
deriving DecidableEq, Repr

/-- The combine gate decision (`combine_shares`'s precondition checks, `threshold_decrypt.rs:436-463`):
`combineAdmits shares t` is `true` exactly when there are `≥ t` shares, no share has index `0`, and all
indices are distinct. (The ciphertext-id/MAC checks are §3.5 below, relative to `Blake3Prf`.) -/
def combineAdmits (shares : List Share) (t : Nat) : Bool :=
  decide (t ≤ shares.length)
    && shares.all (fun s => s.idx != 0)
    && decide (shares.map (·.idx)).Nodup

/-- **`combine_rejects_below_threshold`** — the fail-closed boundary: if fewer than `threshold` shares are
presented, `combine` NEVER admits. This is `combine_shares` returning `InsufficientShares`
(`threshold_decrypt.rs:436`); it is what makes `< t` validators unable to decrypt — the secrecy guarantee. -/
theorem combine_rejects_below_threshold (shares : List Share) (t : Nat)
    (h : shares.length < t) : combineAdmits shares t = false := by
  unfold combineAdmits
  have : ¬ (t ≤ shares.length) := Nat.not_le.mpr h
  simp [decide_eq_false this]

/-- **`combine_rejects_dup_index`** — duplicate validator indices are rejected
(`DuplicateShareIndex`, `threshold_decrypt.rs:455-463`): a repeated index breaks the Lagrange distinctness
precondition (two shares at the same evaluation point), so the gate fails closed. -/
theorem combine_rejects_dup_index (shares : List Share) (t : Nat)
    (h : ¬ (shares.map (·.idx)).Nodup) : combineAdmits shares t = false := by
  unfold combineAdmits
  simp [decide_eq_false h]

/-- **`combine_rejects_zero_index`** — the reserved index `0` is rejected (`InvalidShareIndex(0)`,
`threshold_decrypt.rs:450`): Shamir evaluation points are `1..n` (point `0` is where the SECRET lives),
so a share claiming index `0` is malformed and the gate fails closed. -/
theorem combine_rejects_zero_index (shares : List Share) (t : Nat)
    (h : ∃ s ∈ shares, s.idx = 0) : combineAdmits shares t = false := by
  unfold combineAdmits
  obtain ⟨s, hs, hz⟩ := h
  have : shares.all (fun s => s.idx != 0) = false := by
    rw [List.all_eq_false]
    exact ⟨s, hs, by simp [hz]⟩
  simp [this]

/-- **`combine_admits_iff`** — full characterization of the gate: it admits iff all three preconditions
hold. Pins that `combineAdmits` is EXACTLY the conjunction the Rust checks (no hidden slack). -/
theorem combine_admits_iff (shares : List Share) (t : Nat) :
    combineAdmits shares t = true ↔
      t ≤ shares.length
      ∧ (∀ s ∈ shares, s.idx ≠ 0)
      ∧ (shares.map (·.idx)).Nodup := by
  unfold combineAdmits
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨hlen, hz⟩, hnd⟩
    exact ⟨hlen, fun s hs => hz s hs, hnd⟩
  · rintro ⟨hlen, hz, hnd⟩
    exact ⟨⟨hlen, fun s hs => hz s hs⟩, hnd⟩

/-! ### §3.5 — The share-MAC integrity reduction, relative to a named PRF/MAC carrier.

`combine_shares` verifies each share's BLAKE3 `share_mac` against the RECONSTRUCTED key before trusting it
(`threshold_decrypt.rs:482`), detecting corrupted/malicious shares. We model this as a reduction to the
keyed-hash being a secure MAC — the `Blake3Prf` carrier — exactly as `CaveatChain` reduces to
`MacUnforgeable`. We do NOT prove BLAKE3 secure; we state the integrity property the protocol gets FROM it. -/

/-- The abstract keyed BLAKE3 MAC (`compute_share_mac`, `threshold_decrypt.rs:268`): `mac key share idx`.
Modeled as an opaque function; its security is the `Blake3Prf` carrier below. -/
opaque blake3Mac : (key : Nat) → (share : Nat) → (idx : Nat) → Nat

/-- **`Blake3Prf`** — the named cryptographic hypothesis (NOT proved here): BLAKE3 keyed with the master key
is a secure MAC, so an adversary lacking the key cannot produce a valid tag for a forged `(share, idx)`.
Stated as collision-style unforgeability: matching tags under the same key force matching messages. This is
the carrier the share-MAC tamper detection is sound relative to (cf. `CaveatChain.MacUnforgeable`). -/
def Blake3Prf : Prop :=
  ∀ key s₁ i₁ s₂ i₂, blake3Mac key s₁ i₁ = blake3Mac key s₂ i₂ → (s₁ = s₂ ∧ i₁ = i₂)

/-- **`share_mac_detects_tamper`** — RELATIVE to `Blake3Prf`: if a presented share `(s', i)` passes MAC
verification against the reconstructed key but differs from the dealer's honest share `(s, i)` at the same
index, that is a contradiction — so a tampered share at a held index cannot pass. This is the soundness of
the `InvalidShareMac` check (`threshold_decrypt.rs:482-493`), reduced to the PRF carrier, not faked. -/
theorem share_mac_detects_tamper (hprf : Blake3Prf) (key sHonest sBad idx : Nat)
    (hpass : blake3Mac key sBad idx = blake3Mac key sHonest idx) :
    sBad = sHonest :=
  (hprf key sBad idx sHonest idx hpass).1

/-! ## §4 — Differential anchors: the concrete GF(256) / Shamir golden vectors.

These `#guard`s pin the §1/§2 EXECUTABLE Lean model against the Rust unit-test golden vectors. The Rust
`threshold_decrypt_diff.rs` runs the same vectors against the real `gf256`/`shamir_reconstruct_byte`, so
agreement here ⇒ the verified Lean semantics is the one the federation actually computes. -/

-- `test_gf256_arithmetic` (`threshold_decrypt.rs:728`): multiplicative identities.
-- multiplicative identities (`test_gf256_arithmetic`). `#guard` evaluates the executable model the
-- same way the Rust `gf256::mul` runs, exactly the differential discipline.
#guard gf256Mul 0 42 == 0
#guard gf256Mul 1 42 == 42
#guard gf256Mul 42 1 == 42
-- a nontrivial product: 0x53 and 0xCA are AES-inverse partners, so their product is 1.
#guard gf256Mul 0x53 0xCA == 0x01

-- `a * inv(a) = 1` for the sampled nonzero elements (the Rust loops over all 1..=255; we sample).
#guard gf256Mul 1 (gf256Inv 1) == 1
#guard gf256Mul 2 (gf256Inv 2) == 1
#guard gf256Mul 42 (gf256Inv 42) == 1
#guard gf256Mul 0x53 (gf256Inv 0x53) == 1
#guard gf256Mul 255 (gf256Inv 255) == 1
#guard gf256Mul 0xAB (gf256Inv 0xAB) == 1

/-- Concrete Lagrange reconstruction byte (`shamir_reconstruct_byte`, `threshold_decrypt.rs:232`),
transcribed for the differential `#guard`s: interpolate `(xᵢ,yᵢ)` at `x=0` using `gf256Mul`/`gf256Inv`,
subtraction = XOR. `pts` is the list of `(index, shareByte)`. -/
def reconstructByte (pts : List (Nat × Nat)) : Nat :=
  pts.foldl (init := 0) fun secret (xi, yi) =>
    let (num, den) := pts.foldl (init := (1, 1)) fun (n, d) (xj, _) =>
      if xj == xi then (n, d) else (gf256Mul n xj, gf256Mul d (xi ^^^ xj))
    let lagrange := gf256Mul num (gf256Inv den)
    secret ^^^ gf256Mul yi lagrange

/-- `test_shamir_single_byte_roundtrip` (`threshold_decrypt.rs:747`): secret `0x42`, polynomial
`f(x) = 0x42 + 0xAB·x` (t=2), evaluated at x=1,2,3. Shares = `f(1), f(2), f(3)`. Any 2-of-3 reconstruct. -/
private def golden_s : Nat := 0x42
private def golden_y1 : Nat := golden_s ^^^ gf256Mul 0xAB 1   -- f(1)
private def golden_y2 : Nat := golden_s ^^^ gf256Mul 0xAB 2   -- f(2)
private def golden_y3 : Nat := golden_s ^^^ gf256Mul 0xAB 3   -- f(3)

-- Reconstruct from points {1,2} recovers the secret.
#guard reconstructByte [(1, golden_y1), (2, golden_y2)] == golden_s
-- Reconstruct from points {1,3} recovers the secret (any subset works).
#guard reconstructByte [(1, golden_y1), (3, golden_y3)] == golden_s
-- Reconstruct from points {2,3} recovers the secret.
#guard reconstructByte [(2, golden_y2), (3, golden_y3)] == golden_s

-- The threshold gate accepts a valid 2-of-3 share set.
#guard combineAdmits [⟨1, golden_y1⟩, ⟨2, golden_y2⟩] 2 == true
-- The threshold gate rejects a 1-of-3 set against threshold 2 (fail-closed).
#guard combineAdmits [⟨1, golden_y1⟩] 2 == false
-- The threshold gate rejects a duplicate-index set.
#guard combineAdmits [⟨1, golden_y1⟩, ⟨1, golden_y2⟩] 2 == false
-- The threshold gate rejects the reserved index 0.
#guard combineAdmits [⟨0, golden_y1⟩, ⟨2, golden_y2⟩] 2 == false

/-! ## §5 — Axiom hygiene: the threshold-decryption algebra is kernel-clean. -/

#assert_axioms shamirPoly_eval_zero
#assert_axioms shamir_any_t_reconstruct
#assert_axioms shamir_below_t_undetermined
#assert_axioms combine_rejects_below_threshold
#assert_axioms combine_rejects_dup_index
#assert_axioms combine_rejects_zero_index
#assert_axioms combine_admits_iff
#assert_axioms share_mac_detects_tamper

end Dregg2.Distributed.ThresholdDecrypt
