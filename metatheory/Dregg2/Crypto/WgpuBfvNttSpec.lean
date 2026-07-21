/-
# Portable wgpu BFV NTT arithmetic — Lean reference contract

The portable WGSL kernel stores every coefficient as two `u32` limbs, performs
modular arithmetic without shader `u64`, and multiplies each RNS row in
`R_q[X]/(X^N+1)`.  This file specifies the bit-exact arithmetic and the
negacyclic/RNS result which every CPU, wgpu, Metal, Vulkan, DX12, or WebGPU
implementation must refine.

The theorem boundary is deliberate: this file proves the CPU-reference algebra
and shape laws.  It does *not* claim that a device executed WGSL faithfully.
That final correspondence is discharged by the Rust/WGSL parity and mutation
tests; `NttRefines` below is the exact proposition those tests target.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Crypto.WgpuBfvNttSpec

open Finset

/-! ## Split-u32 words -/

/-- One shader limb. -/
def limbBase : Nat := 2 ^ 32

/-- The torus/host-word modulus represented by two shader limbs. -/
def wordModulus : Nat := limbBase ^ 2

/-- A portable two-`u32` representation.  Canonicality is stated separately so
raw transport data can be represented without silently normalizing it. -/
structure Word64 where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

/-- Reassemble a pair of little-endian `u32` limbs. -/
def Word64.join (w : Word64) : Nat := w.lo + limbBase * w.hi

/-- Canonical little-endian split of the low 64 bits of a natural number. -/
def split64 (x : Nat) : Word64 :=
  let y := x % wordModulus
  ⟨y % limbBase, y / limbBase⟩

/-- The two-limb serializer is exact modulo `2^64`. -/
theorem join_split64 (x : Nat) : (split64 x).join = x % wordModulus := by
  unfold split64 Word64.join
  simp only
  simpa [mul_comm] using Nat.mod_add_div (x % wordModulus) limbBase

/-- The low limb emitted by the serializer is a genuine `u32`. -/
theorem split64_lo_lt (x : Nat) : (split64 x).lo < limbBase := by
  unfold split64
  exact Nat.mod_lt _ (by norm_num [limbBase])

/-- The high limb emitted by the serializer is a genuine `u32`. -/
theorem split64_hi_lt (x : Nat) : (split64 x).hi < limbBase := by
  unfold split64 wordModulus
  have hmod : x % limbBase ^ 2 < limbBase ^ 2 :=
    Nat.mod_lt _ (by norm_num [limbBase])
  exact (Nat.div_lt_iff_lt_mul (by norm_num [limbBase])).2 (by
    simpa [pow_two, mul_assoc] using hmod)

/-- Specification of the shader's low-half `64 × 64` multiply.  Implementations
may use the WGSL 16-bit partial-product ladder, but the observable word is this
canonical split of the low 64 product bits. -/
def mul64Low (a b : Word64) : Word64 := split64 (a.join * b.join)

/-- Low-half multiplication rejoins to wrapping `u64` multiplication exactly. -/
theorem join_mul64Low (a b : Word64) :
    (mul64Low a b).join = (a.join * b.join) % wordModulus := by
  exact join_split64 _

/-- The BFV moduli are below `2^62`, so adding two canonical residues cannot
overflow the unsigned 64-bit word represented by the shader limbs. -/
theorem canonical_sum_fits_word {q a b : Nat}
    (hq : q < 2 ^ 62) (ha : a < q) (hb : b < q) : a + b < wordModulus := by
  unfold wordModulus limbBase
  norm_num at hq ⊢
  omega

/-- The same bound proves the stronger invariant used by `mulmod`'s
double-and-add loop: every modular-add input sum is below `2^63`. -/
theorem canonical_sum_fits_signed_word {q a b : Nat}
    (hq : q < 2 ^ 62) (ha : a < q) (hb : b < q) : a + b < 2 ^ 63 := by
  norm_num at hq ⊢
  omega

/-- Mathematical result of the shader's double-and-add scalar multiplication. -/
def mulMod (q a b : Nat) : Nat := (a * b) % q

theorem mulMod_lt {q a b : Nat} (hq : 0 < q) : mulMod q a b < q :=
  Nat.mod_lt _ hq

theorem cast_mulMod (q a b : Nat) :
    ((mulMod q a b : Nat) : ZMod q) = (a : ZMod q) * b := by
  unfold mulMod
  rw [ZMod.natCast_mod, Nat.cast_mul]

/-! ## Negacyclic polynomial reference -/

/-- A fixed-shape polynomial over one RNS modulus.  Using `Fin N` makes the
degree-preservation law intrinsic rather than a runtime hope. -/
abbrev Poly (q n : Nat) := Fin n → ZMod q

/-- The wrapped RHS index contributing to output coefficient `k`. -/
def rhsIndex {n : Nat} (i k : Fin n) : Fin n :=
  if h : i.val ≤ k.val then
    ⟨k.val - i.val, by omega⟩
  else
    ⟨n + k.val - i.val, by omega⟩

/-- One coefficient contribution after reducing by `X^N = -1`. -/
def negacyclicTerm {q n : Nat} (a b : Poly q n) (k i : Fin n) : ZMod q :=
  if i.val ≤ k.val then a i * b (rhsIndex i k)
  else -(a i * b (rhsIndex i k))

/-- Ground-truth schoolbook product in `(Z/qZ)[X]/(X^N+1)`. -/
def negacyclicMul {q n : Nat} (a b : Poly q n) : Poly q n := fun k =>
  ∑ i : Fin n, negacyclicTerm a b k i

/-- Exact coefficient equation: ordinary convolution terms with `i ≤ k` are
added, while terms wrapping past degree `N-1` are subtracted. -/
theorem negacyclicMul_apply {q n : Nat} (a b : Poly q n) (k : Fin n) :
    negacyclicMul a b k = ∑ i : Fin n, negacyclicTerm a b k i := rfl

@[simp] theorem negacyclicMul_zero_left {q n : Nat} (b : Poly q n) :
    negacyclicMul (fun _ => 0) b = 0 := by
  funext k
  simp [negacyclicMul, negacyclicTerm]

@[simp] theorem negacyclicMul_zero_right {q n : Nat} (a : Poly q n) :
    negacyclicMul a (fun _ => 0) = 0 := by
  funext k
  simp [negacyclicMul, negacyclicTerm]

/-- The reference is additive in its left operand. -/
theorem negacyclicMul_add_left {q n : Nat} (a b c : Poly q n) :
    negacyclicMul (a + b) c = negacyclicMul a c + negacyclicMul b c := by
  funext k
  simp only [negacyclicMul, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold negacyclicTerm
  split
  · simp [add_mul]
  · simp [add_mul]
    ac_rfl

/-- The reference is additive in its right operand. -/
theorem negacyclicMul_add_right {q n : Nat} (a b c : Poly q n) :
    negacyclicMul a (b + c) = negacyclicMul a b + negacyclicMul a c := by
  funext k
  simp only [negacyclicMul, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold negacyclicTerm
  split
  · simp [mul_add]
  · simp [mul_add]
    ac_rfl

/-! ## RNS rows and the NTT refinement boundary -/

/-- A family of RNS rows; each row has its own modulus but the same polynomial
degree. -/
abbrev RnsPoly {r n : Nat} (modulus : Fin r → Nat) :=
  (row : Fin r) → Poly (modulus row) n

/-- The strict hbox parity gate's deployed degree. -/
def deployedDegree : Nat := 4096

/-- The three fresh-ciphertext fhe.rs RNS moduli exercised by the RX 6750 XT
Vulkan gate. -/
def deployedModulus (row : Fin 3) : Nat :=
  #[0xffffee001, 0xffffc4001, 0x1ffffe0001][row.val]!

theorem deployed_degree_power_of_two : deployedDegree = 2 ^ 12 := by
  norm_num [deployedDegree]

theorem deployed_modulus_lt (row : Fin 3) :
    deployedModulus row < 2 ^ 62 := by
  fin_cases row <;> norm_num [deployedModulus]

/-- Each deployed row admits the `2N`-root domain required by the twisted
negacyclic NTT (`q ≡ 1 mod 2N`). -/
theorem deployed_ntt_domain (row : Fin 3) :
    deployedModulus row % (2 * deployedDegree) = 1 := by
  fin_cases row <;> norm_num [deployedModulus, deployedDegree]

/-- Host-side preflight required by the portable BFV kernel.  `Context::new`
also validates implementation-specific RNS data; these are its mathematical
contents used by the kernel: bounded power-of-two degree, bounded row count,
prime pairwise-coprime moduli, and a `2N`-th root domain. -/
structure HostShape {r n : Nat} (modulus : Fin r → Nat) : Prop where
  degree_min : 8 ≤ n
  degree_max : n ≤ 2 ^ 16
  degree_power_of_two : ∃ logDegree, n = 2 ^ logDegree
  rows_nonempty : 0 < r
  rows_bounded : r ≤ 16
  modulus_prime : ∀ row, Nat.Prime (modulus row)
  modulus_lt : ∀ row, modulus row < 2 ^ 62
  ntt_domain : ∀ row, modulus row % (2 * n) = 1
  pairwise_coprime : ∀ i j, i ≠ j → Nat.Coprime (modulus i) (modulus j)

/-- Root table loaded by one RNS row.  The `ψ^N = -1` check is the semantic
pin for the negacyclic twist; `ω = ψ²` is the cyclic NTT root. -/
structure RootTable {r n : Nat} (modulus : Fin r → Nat) where
  psi : (row : Fin r) → ZMod (modulus row)
  negacyclic_root : ∀ row, psi row ^ n = -1

def RootTable.omega {r n : Nat} {modulus : Fin r → Nat}
    (table : RootTable (n := n) modulus) (row : Fin r) : ZMod (modulus row) :=
  table.psi row ^ 2

/-- Ground-truth BFV polynomial multiplication, independently in every RNS row. -/
def rnsNegacyclicMul {r n : Nat} {modulus : Fin r → Nat}
    (a b : RnsPoly (n := n) modulus) : RnsPoly (n := n) modulus := fun row =>
  negacyclicMul (a row) (b row)

theorem rnsNegacyclicMul_apply {r n : Nat} {modulus : Fin r → Nat}
    (a b : RnsPoly (n := n) modulus) (row : Fin r) (k : Fin n) :
    rnsNegacyclicMul a b row k =
      ∑ i : Fin n, negacyclicTerm (a row) (b row) k i := rfl

/-- Exact semantic contract for a forward-NTT / pointwise / inverse-NTT
implementation.  It binds *all* rows and coefficients to schoolbook
negacyclic multiplication; table generation and device execution are not erased
into a digest or a single sample. -/
def NttRefines {r n : Nat} {modulus : Fin r → Nat}
    (impl : RnsPoly (n := n) modulus → RnsPoly (n := n) modulus →
      RnsPoly (n := n) modulus) : Prop :=
  ∀ a b row k, impl a b row k = rnsNegacyclicMul a b row k

/-- A backend satisfying the NTT refinement contract is extensionally equal to
the CPU schoolbook reference for every RNS row. -/
theorem nttRefines_eq_reference {r n : Nat} {modulus : Fin r → Nat}
    (impl : RnsPoly (n := n) modulus → RnsPoly (n := n) modulus →
      RnsPoly (n := n) modulus)
    (h : NttRefines impl) (a b : RnsPoly (n := n) modulus) :
    impl a b = rnsNegacyclicMul a b := by
  funext row k
  exact h a b row k

/-- The reference itself is a non-vacuous inhabitant of the refinement
contract. -/
theorem reference_nttRefines {r n : Nat} {modulus : Fin r → Nat} :
    NttRefines (@rnsNegacyclicMul r n modulus) := by
  intro a b row k
  rfl

#assert_axioms join_split64
#assert_axioms canonical_sum_fits_word
#assert_axioms cast_mulMod
#assert_axioms negacyclicMul_add_left
#assert_axioms negacyclicMul_add_right
#assert_axioms deployed_modulus_lt
#assert_axioms deployed_ntt_domain
#assert_axioms nttRefines_eq_reference

end Dregg2.Crypto.WgpuBfvNttSpec
