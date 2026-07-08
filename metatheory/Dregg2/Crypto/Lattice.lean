/-
# `Dregg2.Crypto.Lattice` — MLWE / MSIS, and the IRREDUCIBLE LINE for post-quantum security.

This is where we draw the line precisely. Every threshold/signature theorem above rests on a hardness
carrier; for the post-quantum path that carrier is the LATTICE assumptions — **MLWE** (Module Learning
With Errors) and **MSIS** (Module Short Integer Solution). This file MODELS them as the assumptions they
are — predicates asserting "no efficient adversary finds a short kernel vector / recovers the secret" —
and states them honestly as the irreducible floor: they are NOT proved here (no formal proof discharges
the hardness of a lattice problem; that is the shared floor of ALL post-quantum lattice cryptography,
FIPS ML-DSA/Dilithium included). What we DO formalize is everything ABOVE the line — that a signature
FORGERY reduces to breaking one of these assumptions (see `Dregg2.Crypto.HermineMSIS`).

The load-bearing lattice-specific ingredient — the one a group-theoretic reduction never needs — is a
**norm**: security is about SHORT vectors. We model shortness with an integer-valued seminorm (the
coefficient ∞-norm of a module element over the ring `R_q = ℤ_q[X]/(Xⁿ+1)`), abstracted as `ShortNorm`
so the reduction is norm-generic. The triangle inequality (`nrm_add_le`) is exactly what makes the
extracted difference short — the leg previously treated as a black box.
-/
import Dregg2.Tactics
import Mathlib.Algebra.Module.LinearMap.Defs

namespace Dregg2.Crypto.Lattice

/-- An integer-valued seminorm (the coefficient ∞-norm over `R_q^k`, abstracted): the "shortness"
measure a lattice problem is stated in. `nrm z` is small ⇔ `z` is a short vector. -/
class ShortNorm (M : Type*) [AddCommGroup M] where
  nrm : M → ℕ
  nrm_zero : nrm 0 = 0
  nrm_neg : ∀ a : M, nrm (-a) = nrm a
  nrm_add_le : ∀ a b : M, nrm (a + b) ≤ nrm a + nrm b

export ShortNorm (nrm nrm_zero nrm_neg nrm_add_le)

variable {M : Type*} [AddCommGroup M] [ShortNorm M]

/-- `z` is `β`-short. -/
def IsShort (β : ℕ) (z : M) : Prop := nrm z ≤ β

/-- The triangle inequality for differences — the leg that makes an extracted `z - z'` short. -/
theorem nrm_sub_le (a b : M) : nrm (a - b) ≤ nrm a + nrm b := by
  rw [sub_eq_add_neg]
  calc nrm (a + -b) ≤ nrm a + nrm (-b) := nrm_add_le a (-b)
    _ = nrm a + nrm b := by rw [nrm_neg]

/-- A sum of a short and a short vector is short (additively) — used to bound the extracted witness. -/
theorem IsShort.add {βa βb : ℕ} {a b : M} (ha : IsShort βa a) (hb : IsShort βb b) :
    IsShort (βa + βb) (a + b) :=
  le_trans (nrm_add_le a b) (Nat.add_le_add ha hb)

/-- Likewise for a difference. -/
theorem IsShort.sub {βa βb : ℕ} {a b : M} (ha : IsShort βa a) (hb : IsShort βb b) :
    IsShort (βa + βb) (a - b) :=
  le_trans (nrm_sub_le a b) (Nat.add_le_add ha hb)

variable {Rq : Type*} [CommRing Rq] [Module Rq M]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-- **An MSIS solution** for the public matrix `A` at bound `β`: a SHORT, NONZERO vector in the kernel
of `A`. Finding one is the Module-SIS problem. (The kernel is nonempty for a compressing `A`; the
hardness is FINDING a short nonzero element — captured by `MSISHard`.) -/
def IsMSISSolution (A : M →ₗ[Rq] N) (β : ℕ) (z : M) : Prop :=
  z ≠ 0 ∧ nrm z ≤ β ∧ A z = 0

/-- **THE IRREDUCIBLE ASSUMPTION (MSIS).** Module-SIS is hard for `(A, β)`: no short nonzero kernel
vector is findable. Stated as a predicate and ASSUMED where a reduction bottoms out — never proved,
because no formal proof discharges lattice hardness (the shared floor of all PQ lattice crypto). A
`Dregg2.Crypto.HermineMSIS` reduction shows a forgery would produce an `IsMSISSolution`, contradicting
this. -/
def MSISHard (A : M →ₗ[Rq] N) (β : ℕ) : Prop :=
  ¬ ∃ z, IsMSISSolution A β z

/-- **An MLWE sample**: the public key `t` is a noisy linear image `A·s + e` with `s` (the secret) and
`e` (the error) both short. Distinguishing such `t` from uniform (or recovering `s`) is Module-LWE. -/
def IsMLWESample [ShortNorm N] (A : M →ₗ[Rq] N) (β : ℕ) (t : N) : Prop :=
  ∃ s : M, ∃ e : N, nrm s ≤ β ∧ nrm e ≤ β ∧ t = A s + e

/-- **THE IRREDUCIBLE ASSUMPTION (MLWE, search form).** Module-LWE is hard: the short secret `s`
underlying a sample `t = A·s + e` is not recoverable. This is the assumption that HIDES the signing
key — the leg that rules out the trivial (`u = 0`) case in the MSIS forgery reduction. Assumed, never
proved. -/
def MLWESearchHard [ShortNorm N] (A : M →ₗ[Rq] N) (β : ℕ) (t : N) : Prop :=
  ¬ ∃ s : M, nrm s ≤ β ∧ ∃ e : N, nrm e ≤ β ∧ t = A s + e

/-- Sanity / non-degeneracy: the ZERO vector is never an MSIS solution (a solution must be nonzero),
so `MSISHard` is not vacuously satisfied by the always-present `0 ∈ ker A`. -/
theorem zero_not_msis_solution (A : M →ₗ[Rq] N) (β : ℕ) : ¬ IsMSISSolution A β (0 : M) :=
  fun h => h.1 rfl

#assert_axioms nrm_sub_le
#assert_axioms IsShort.sub
#assert_axioms zero_not_msis_solution

end Dregg2.Crypto.Lattice
