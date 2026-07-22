/-
# Market.PrivateBookBfvRootOrder -- exact production odd-NTT root orders

The three executable root teeth in `PrivateBookBfvNttFamily` prove only
`psi ^ 4096 = -1`.  The Fourier refinement additionally needs the roots to
have exact order `8192`.  This file closes that concrete root-order premise for
all deployed RNS rows; the remaining `OddNttRefines` theorem is the general
orthogonality/convolution argument, not a caller-supplied root-table claim.
-/

import Market.PrivateBookBfvNttFamily

namespace Market.PrivateBookBfvRootOrder

open Dregg2.Crypto.WgpuBfvNttSpec
open Market.PrivateBookBfvBindingAir
open Market.PrivateBookBfvNttFamily

set_option autoImplicit false

private theorem primitive8192_of_half_power_neg_one {q : Nat} (psi : ZMod q)
    (halfPower : psi ^ 4096 = -1) (minusOne_ne_one : (-1 : ZMod q) ≠ 1) :
    IsPrimitiveRoot psi 8192 := by
  have fullPower : psi ^ 8192 = 1 := by
    calc
      psi ^ 8192 = (psi ^ 4096) ^ 2 := by rw [show 8192 = 4096 * 2 by norm_num, pow_mul]
      _ = 1 := by rw [halfPower]; ring
  have exactOrder : orderOf psi = 8192 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) fullPower
    intro p pPrime pDvd
    have pDvdPower : p ∣ 2 ^ 13 := by norm_num at pDvd ⊢; exact pDvd
    have p_eq_two : p = 2 := Nat.prime_eq_prime_of_dvd_pow pPrime Nat.prime_two pDvdPower
    subst p
    norm_num
    simpa [halfPower] using minusOne_ne_one
  rw [← exactOrder]
  exact IsPrimitiveRoot.orderOf psi

theorem deployed_psi0_isPrimitiveRoot :
    IsPrimitiveRoot (DEPLOYED_PSI0 : ZMod 68719403009) (2 * deployedDegree) := by
  rw [show 2 * deployedDegree = 8192 by norm_num [deployedDegree]]
  apply primitive8192_of_half_power_neg_one
  · exact deployed_psi0_negacyclic_root
  · letI : Fact (2 < 68719403009) := ⟨by norm_num⟩
    exact ZMod.neg_one_ne_one

theorem deployed_psi1_isPrimitiveRoot :
    IsPrimitiveRoot (DEPLOYED_PSI1 : ZMod 68719230977) (2 * deployedDegree) := by
  rw [show 2 * deployedDegree = 8192 by norm_num [deployedDegree]]
  apply primitive8192_of_half_power_neg_one
  · exact deployed_psi1_negacyclic_root
  · letI : Fact (2 < 68719230977) := ⟨by norm_num⟩
    exact ZMod.neg_one_ne_one

theorem deployed_psi2_isPrimitiveRoot :
    IsPrimitiveRoot (DEPLOYED_PSI2 : ZMod 137438822401) (2 * deployedDegree) := by
  rw [show 2 * deployedDegree = 8192 by norm_num [deployedDegree]]
  apply primitive8192_of_half_power_neg_one
  · exact deployed_psi2_negacyclic_root
  · letI : Fact (2 < 137438822401) := ⟨by norm_num⟩
    exact ZMod.neg_one_ne_one

/-- The one canonical production root family, indexed by the typed RNS row. -/
def deployedPsi (row : ModulusIx) : ZMod (deployedModulus row) :=
  (#[DEPLOYED_PSI0, DEPLOYED_PSI1, DEPLOYED_PSI2][row.val]! :
    ZMod (deployedModulus row))

/-- Every member of the typed production root family has exact order `2N`. -/
theorem deployedPsi_isPrimitiveRoot (row : ModulusIx) :
    IsPrimitiveRoot (deployedPsi row) (2 * deployedDegree) := by
  fin_cases row
  · exact deployed_psi0_isPrimitiveRoot
  · exact deployed_psi1_isPrimitiveRoot
  · exact deployed_psi2_isPrimitiveRoot

/-- The exact-order facts in particular discharge the root-table contract used
by the executable negacyclic NTT specification. -/
theorem deployedPsi_negacyclic_root (row : ModulusIx) :
    deployedPsi row ^ deployedDegree = -1 := by
  fin_cases row
  · exact deployed_psi0_negacyclic_root
  · exact deployed_psi1_negacyclic_root
  · exact deployed_psi2_negacyclic_root

/-- Canonical, fully checked production root table. -/
def deployedRootTable : RootTable (n := deployedDegree) deployedModulus where
  psi := deployedPsi
  negacyclic_root := deployedPsi_negacyclic_root

#assert_axioms deployed_psi0_isPrimitiveRoot
#assert_axioms deployed_psi1_isPrimitiveRoot
#assert_axioms deployed_psi2_isPrimitiveRoot
#assert_axioms deployedPsi_isPrimitiveRoot
#assert_axioms deployedPsi_negacyclic_root

end Market.PrivateBookBfvRootOrder
