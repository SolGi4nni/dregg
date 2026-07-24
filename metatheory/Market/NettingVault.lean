import Dregg2.Tactics
import Bfv.Noise

/-!
# The Netting Vault — theory stone: multilateral netting conserves value and compresses the gross web

The Netting Vault (a FRONTIER hall in `THE-DARK-BAZAAR.md`: hidden guild obligations, revealing only the
final net settlement) rests on multilateral netting. Each party `i` holds hidden bilateral obligations
`g i j` (`i` owes `j`); the settlement reveals only each party's NET position
`net i = (Σ_j g i j) − (Σ_j g j i)` — what `i` owes minus what `i` is owed — while the gross obligation web
`g` stays encrypted (each `net i` is a SUM of hidden obligations, so the additive FHE fold reveals the net and
nothing else).

This file proves the two facts that make netting a real settlement primitive:
1. **conservation** — the nets sum to zero (`net_conserves`): settling nets is value-balanced, every debt is
   someone's credit. This is the invariant a settlement layer must have.
2. **compression** — mutual/symmetric obligations net to zero (`symmetric_obligations_net_zero`): if `i` owes
   `j` exactly what `j` owes `i`, both cancel and neither party's net moves. So netting COMPRESSES the gross
   web down to the imbalances alone — the frontier's "no-viewer multilateral compression". Only the
   irreducible net crosses the reveal boundary.

Perf note: netting is purely ADDITIVE (`O(n²)` adds over the hidden `g`), so — unlike the multiply/bootstrap
halls — it rides the cheap fold and needs no GPU. The Netting Vault is the additive hall.
-/

namespace Market.NettingVault

/-- Party `i`'s NET position over the hidden bilateral obligation matrix `g` (`g i j` = `i` owes `j`):
what `i` owes minus what `i` is owed. This is the ONLY value the vault reveals; `g` stays encrypted. -/
def net {n : ℕ} (g : Fin n → Fin n → ℤ) (i : Fin n) : ℤ :=
  (∑ j, g i j) - (∑ j, g j i)

/-- **CONSERVATION — the nets sum to zero.** Settling the net positions is value-balanced: the total owed
equals the total owed-to, so the reveal boundary never creates or destroys value. This is the settlement
invariant the Netting Vault must uphold. -/
theorem net_conserves {n : ℕ} (g : Fin n → Fin n → ℤ) : (∑ i, net g i) = 0 := by
  unfold net
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact Finset.sum_comm

/-- **COMPRESSION — mutual obligations net to zero.** If the obligation matrix is symmetric (`i` owes `j`
exactly what `j` owes `i`, e.g. equal reciprocal debts), every party's net is zero. So netting cancels the
mutual part of the gross web and reveals only the IMBALANCES — the "no-viewer multilateral compression": the
irreducible net is all that crosses the reveal boundary, the reciprocal detail stays hidden. -/
theorem symmetric_obligations_net_zero {n : ℕ} (g : Fin n → Fin n → ℤ)
    (hsym : ∀ i j, g i j = g j i) (i : Fin n) : net g i = 0 := by
  unfold net
  have : (∑ j, g i j) = (∑ j, g j i) := Finset.sum_congr rfl (fun j _ => hsym i j)
  rw [this, sub_self]

/-- **The reveal is exactly the antisymmetric (imbalance) part.** Splitting `g` into any symmetric `s` and
antisymmetric `a` (`g = s + a`), the net depends ONLY on `a` — the symmetric part contributes nothing. So the
vault's public output is a function of the imbalances alone; the reciprocal/symmetric detail is provably
absent from what is revealed. -/
theorem net_ignores_symmetric_part {n : ℕ} (s a : Fin n → Fin n → ℤ)
    (hs : ∀ i j, s i j = s j i) (i : Fin n) :
    net (fun x y => s x y + a x y) i = net a i := by
  unfold net
  have hss : (∑ j, s i j) = (∑ j, s j i) := Finset.sum_congr rfl (fun j _ => hs i j)
  simp only [Finset.sum_add_distrib]
  rw [hss]; ring

#assert_all_clean [Market.NettingVault.net_conserves,
  Market.NettingVault.symmetric_obligations_net_zero,
  Market.NettingVault.net_ignores_symmetric_part]

end Market.NettingVault
