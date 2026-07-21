/-
# Portable wgpu torus negacyclic MAC — Lean reference contract

This is the first coefficient-domain arithmetic rung below a future TFHE
external product.  It specifies exactly

  `out = accumulator + sum_t lhs_t * rhs_t`

in `(Z/2^64Z)[X]/(X^N+1)`, including the flattened batch indexing used by the
WGSL kernel.  It is not gadget decomposition, a GGSW×GLWE external product,
CMUX, blind rotation, or programmable bootstrapping.
-/
import Dregg2.Crypto.WgpuBfvNttSpec

namespace Dregg2.Crypto.WgpuTorusNegacyclicMacSpec

open Finset
open WgpuBfvNttSpec

/-- One torus coefficient: wrapping `u64` arithmetic. -/
abbrev Torus := ZMod wordModulus

abbrev TorusPoly (n : Nat) := Poly wordModulus n

/-- Batched coefficient-domain polynomial multiply-accumulate. -/
def torusMac {n : Nat} (accumulator : TorusPoly n)
    (products : List (TorusPoly n × TorusPoly n)) : TorusPoly n := fun k =>
  accumulator k +
    (products.map fun pair => negacyclicMul pair.1 pair.2 k).sum

/-- The batched reference has the exact coefficient equation of the shader. -/
theorem torusMac_apply {n : Nat} (accumulator : TorusPoly n)
    (products : List (TorusPoly n × TorusPoly n)) (k : Fin n) :
    torusMac accumulator products k =
      accumulator k +
        (products.map fun pair => ∑ j : Fin n,
          if j.val ≤ k.val then
            pair.1 j * pair.2 (rhsIndex j k)
          else
            -(pair.1 j * pair.2 (rhsIndex j k))).sum := by
  simp only [torusMac, negacyclicMul, negacyclicTerm]

/-- Empty batches are algebraically the accumulator.  The deployed boundary
nevertheless refuses them, so a successful request always has at least one
product. -/
@[simp] theorem torusMac_nil {n : Nat} (accumulator : TorusPoly n) :
    torusMac accumulator [] = accumulator := by
  funext k
  simp [torusMac]

/-- Appending a batch is the same as applying its contribution after the first
batch.  This is the chunking law used by future resident/streaming kernels. -/
theorem torusMac_append {n : Nat} (accumulator : TorusPoly n)
    (xs ys : List (TorusPoly n × TorusPoly n)) :
    torusMac accumulator (xs ++ ys) =
      torusMac (torusMac accumulator xs) ys := by
  funext k
  simp only [torusMac, List.map_append, List.sum_append]
  ring

/-! ## Exact flattened host boundary -/

/-- The host validation accepted by both CPU and wgpu implementations. -/
structure FlatShape (accumulator lhs rhs : Array Nat) (n products : Nat) : Prop where
  degree_positive : 0 < n
  degree_power_of_two : ∃ logDegree, n = 2 ^ logDegree
  products_positive : 0 < products
  accumulator_exact : accumulator.size = n
  lhs_exact : lhs.size = products * n
  rhs_exact : rhs.size = products * n

/-- A flattened product row, matching the shader address `product*N + i`. -/
def flatPoly (flat : Array Nat) (n : Nat) (product : Nat) : TorusPoly n := fun i =>
  (flat[product * n + i.val]! : ZMod wordModulus)

/-- Exact flattened coefficient equation targeted by the WGSL parity gate:

`out[k] = acc[k] + Σ_t (Σ_{j≤k} lhs[tN+j] rhs[tN+k-j]
                              - Σ_{j>k} lhs[tN+j] rhs[tN+N+k-j]) mod 2^64`.
-/
def flatReference (accumulator lhs rhs : Array Nat) (n products : Nat) :
    TorusPoly n := fun k =>
  (accumulator[k.val]! : Torus) + ∑ t : Fin products, ∑ j : Fin n,
    if j.val ≤ k.val then
      (lhs[t.val * n + j.val]! : Torus) *
        (rhs[t.val * n + (k.val - j.val)]! : Torus)
    else
      -((lhs[t.val * n + j.val]! : Torus) *
        (rhs[t.val * n + (n + k.val - j.val)]! : Torus))

theorem flatReference_apply (accumulator lhs rhs : Array Nat) (n products : Nat)
    (k : Fin n) :
    flatReference accumulator lhs rhs n products k =
      (accumulator[k.val]! : Torus) + ∑ t : Fin products, ∑ j : Fin n,
        if j.val ≤ k.val then
          (lhs[t.val * n + j.val]! : Torus) *
            (rhs[t.val * n + (k.val - j.val)]! : Torus)
        else
          -((lhs[t.val * n + j.val]! : Torus) *
            (rhs[t.val * n + (n + k.val - j.val)]! : Torus)) := rfl

/-- The flattened equation is exactly the structured torus MAC after slicing
the same buffers into `products` rows. -/
theorem flatReference_eq_torusMac (accumulator lhs rhs : Array Nat)
    (n products : Nat) :
    flatReference accumulator lhs rhs n products =
      torusMac (fun k => (accumulator[k.val]! : Torus))
        (List.ofFn fun t : Fin products =>
          (flatPoly lhs n t.val, flatPoly rhs n t.val)) := by
  funext k
  simp only [flatReference, torusMac, negacyclicMul, negacyclicTerm,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  apply congrArg ((accumulator[k.val]! : Torus) + ·)
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  unfold flatPoly rhsIndex
  split <;> rfl

/-- The result's degree is fixed by `Fin n`; serialization therefore always
emits exactly `n` coefficients. -/
def serialize {n : Nat} (poly : TorusPoly n) : Array Nat :=
  Array.ofFn fun i => (poly i).val

@[simp] theorem serialize_size {n : Nat} (poly : TorusPoly n) :
    (serialize poly).size = n := by
  simp [serialize]

/-! ## Backend metadata is observational only -/

inductive Backend where
  | wgpu
  | cpuFallback
  deriving DecidableEq, Repr

/-- A portable execution reports where the coefficients came from. -/
structure Result (n : Nat) where
  coefficients : TorusPoly n
  backend : Backend

/-- Correctness never branches on backend metadata. -/
def Result.Correct {n : Nat} (result : Result n) (reference : TorusPoly n) : Prop :=
  result.coefficients = reference

/-- A capability fallback and a GPU execution satisfying the contract have
identical observable coefficients. -/
theorem backend_metadata_irrelevant {n : Nat} {reference : TorusPoly n}
    {gpu cpu : Result n} (hgpu : gpu.Correct reference)
    (hcpu : cpu.Correct reference) : gpu.coefficients = cpu.coefficients := by
  rw [hgpu, hcpu]

#assert_axioms torusMac_apply
#assert_axioms torusMac_append
#assert_axioms flatReference_eq_torusMac
#assert_axioms serialize_size
#assert_axioms backend_metadata_irrelevant

end Dregg2.Crypto.WgpuTorusNegacyclicMacSpec
