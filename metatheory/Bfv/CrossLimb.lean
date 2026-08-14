/-
# Bfv.CrossLimb — the cross-limb hole for ct×ct, STATED and EXHIBITED.

**The lane this closes a step of.** `docs/VERDICTS.md` §7 item 5 and `docs/SELVAGE.md` §7 carry
"**cross-limb binding** for ct×ct" as the vFHE #1 named soundness hole, described as: *the verifier
sees per-limb equations; nothing binds the limbs of one ciphertext together, so a prover could
satisfy each limb's relation with limbs from different ciphertexts.* **A hole nobody has exhibited
is a suspicion.** This module states it and exhibits it.

## ⚑ Why it had never been exhibited: every carrier in the tree makes the attack UNREPRESENTABLE

`Market/PrivateBookBfvBindingAir.lean` — the only Lean AIR in the tree that checks a BFV relation —
binds the limbs *in the type of its witness*: `witness.u : OrderIx → CoeffIx → Int` is ONE signed
integer vector which `liftSigned` pushes into every RNS row. `Market/DarkBazaarSameOpeningPoly.lean`
says the consequence out loud in its own residual list: *"a forged single residue row is not
representable in this model"*. That is a true sentence about the model and it is exactly why the
model cannot see the wound. **The first job of this file is a carrier in which the forgery IS
representable** — `RnsCt` below stores the limbs as `L` INDEPENDENT residue vectors, with no
integer preimage anywhere in the type.

## The two holes the one name was carrying

The repo's notes hold two different defects under "cross-limb binding". Separating them is half the
finding, because they have different fixes and only one of them survives the ct×pt narrowing.

  * **HOLE A — PROVENANCE.** The per-limb system asks `∀ i, ∃ source. limb i checks against that
    source`. The honest statement is `∃ source, ∀ i. limb i checks against THAT source`. It is a
    quantifier swap, it is invisible per-limb, and it is what `perLimb_not_imp_bound` exhibits:
    limbs drawn from DIFFERENT ciphertexts satisfying every per-limb equation, with
    `exhibit_accepted_value_is_dishonest` showing the accepted output is a value **no honest pair
    from the pool can produce**. Hole A is about the operation not at all — it applies to any
    per-limb-checked relation, ct×ct or ct×pt.
  * **HOLE B — EXPRESSIBILITY.** The ct×ct rescale `⌊t·x/Q⌉` is a function of the CRT
    RECONSTRUCTION, and `rescale_not_limb_local` proves it is not determined by any single limb's
    residue. This is what `notes/archive/vfhe-shortest-path.md` means by *"the extended-basis tensor
    + t/Q rounding is not expressible in any single limb"*. No amount of provenance binding fixes
    Hole B, and no amount of rescale machinery fixes Hole A.

## The candidate fix that is a TAUTOLOGY

`crt_consistency_vacuous`: for pairwise-coprime moduli the CRT map is a **bijection**, so EVERY limb
tuple is the image of some ring element. "Check the limbs are CRT-consistent" can never refuse, and
the frankenstein of the exhibit is itself perfectly CRT-consistent (it reconstructs to `1 ∈ ℤ/15`).
The candidate named in the brief and in `VERDICTS.md` is not a weak fix; it is not a fix.

## What IS pinned, and where the hole therefore is NOT

`perLimb_pins_modProd`: with the operands held FIXED, the conjunction of the `L` per-limb congruences
is exactly the congruence mod `∏ qᵢ` — the CRT ring isomorphism, no loss. **The per-limb system is
not weak arithmetic.** Every bit of Hole A is in *which object each limb's equation is fed*, which
means the fix is a binding, not an arithmetic strengthening.

## The narrowing verdict for ct×pt (the coefficient-matmul route)

  * **Hole B is ABSENT.** `scalarStep_limb_local`: a public integer multiplier commutes with
    reduction mod every `qᵢ`, so the limb-`i` output is a function of the limb-`i` input. This is
    the same property `Bfv.stepR_noise_le` is built on and the reason that route has a provable
    noise budget; it also makes it limb-local. (`fhegg-fhe/src/bfv_coeff_matmul.rs` performs no RNS
    basis extension at all.)
  * **Hole A SURVIVES, at a square root of the attack surface.** `perLimbPt_not_imp_boundPt`
    exhibits it with a public multiplier. The public operand cannot be forged, so the selector space
    falls from `(K²)^L` to `K^L` (`forgery_surface_ctct` / `forgery_surface_ctpt`) — narrower by a
    square root, still exponential in the limb count, still ≥ 2 forgeries at `L = K = 2`.
  * **It closes exactly when the pool is a singleton** (`perLimbPt_singleton_pool_bound`). The hole
    is a function of HOW MANY ciphertexts the transcript exposes, not of the operation. At depth 1
    against one committed input there is nothing to mix; at depth 2 — the deployed depth — there is.

## The closure, and its soundness error

`rlc_binds` is the random-linear-combination fix with its error quantified: if the prover's limb
vector differs from the committed one at any limb, at most `L − 1` challenges out of `|F|` accept.
The other closure — one commitment over the limb vector, i.e. a single opening index shared by every
limb — is the `∃`/`∀` hoist itself and costs no arithmetic at all; `boundMul_iff_sharedSelector`
records that it IS the honest predicate rather than an approximation of it. ⚠ Neither theorem says
the deployed Rust does either thing; as everywhere in `Bfv/`, these are the statements an emitter
would have to discharge. **There is at present NO ct×ct arithmetization in the tree to fix** — the
hole is in the design, and this file is what any future emitter must refute.

Pure. No axioms beyond the kernel triple.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum.GCD
import Bfv.Params
import Bfv.Ring

namespace Bfv

open Finset

/-! ## 1. The carrier: limbs as INDEPENDENT residue vectors.

`Rn N` (from `Bfv.Ring`) is one polynomial's `N` coefficients. A deployed ciphertext element is
stored as `L` of those — `fhegg-core/src/bfv_lean.rs`'s `RnsPoly { rows : Vec<Vec<u64>> }`, with
`rows[i][j]` the `j`-th coefficient mod `moduli[i]`. **There is no integer preimage in that type,
and there is none here.** That is the whole point: a value of `RnsCt L N` is `L` unrelated residue
vectors, so a limb tuple assembled from different sources is an inhabitant like any other. -/

/-- A ciphertext element in RNS limb representation: for each of `L` moduli, the `N` coefficient
residues (kept in `ℤ`, as `Bfv.Rn` does, so the congruences are exact integer statements). -/
abbrev RnsCt (L N : ℕ) : Type := Fin L → Rn N

/-- **The per-limb equation the verifier checks at limb `i`**, for a ct×ct multiply: the output
residue is the negacyclic product of the operand residues, modulo `qᵢ`.

Written with `Int.emod` rather than `Int.ModEq` so it is decidable by `rfl` at concrete parameters;
`limbMulRel_iff_modEq` proves the two agree, so nothing here is a relation merely NAMED a
congruence. -/
def LimbMulRel (q : ℕ) {N : ℕ} (a b c : Rn N) : Prop :=
  ∀ k, c k % (q : ℤ) = negaMul a b k % (q : ℤ)

/-- **Read the carrier before the conclusion:** `LimbMulRel` is genuine congruence mod `q`. -/
theorem limbMulRel_iff_modEq (q : ℕ) {N : ℕ} (a b c : Rn N) :
    LimbMulRel q a b c ↔ ∀ k, c k ≡ negaMul a b k [ZMOD (q : ℤ)] :=
  Iff.rfl

/-- **The HONEST relation — what the statement is supposed to say.** There is ONE pair of
ciphertexts in the pool, and EVERY limb's equation is fed that pair. `∃` outside `∀`. -/
def BoundMul {L N K : ℕ} (q : Fin L → ℕ) (pool : Fin K → RnsCt L N) (out : RnsCt L N) : Prop :=
  ∃ ja jb : Fin K, ∀ i : Fin L, LimbMulRel (q i) (pool ja i) (pool jb i) (out i)

/-- **What a per-limb system actually pins.** Each limb's equation is satisfiable against SOME pair
from the pool — chosen independently per limb. `∀` outside `∃`. This is what a verifier that checks
`L` separate equations, each opening its own operands, is buying. -/
def PerLimbMul {L N K : ℕ} (q : Fin L → ℕ) (pool : Fin K → RnsCt L N) (out : RnsCt L N) : Prop :=
  ∀ i : Fin L, ∃ ja jb : Fin K, LimbMulRel (q i) (pool ja i) (pool jb i) (out i)

/-! The three predicates above are decidable at concrete parameters — that is what makes the
exhibit of §2 a kernel computation rather than a hand argument. -/

instance instDecidableLimbMulRel (q : ℕ) {N : ℕ} (a b c : Rn N) :
    Decidable (LimbMulRel q a b c) := Fintype.decidableForallFintype

instance instDecidableBoundMul {L N K : ℕ} (q : Fin L → ℕ) (pool : Fin K → RnsCt L N)
    (out : RnsCt L N) : Decidable (BoundMul q pool out) := Fintype.decidableExistsFintype

instance instDecidablePerLimbMul {L N K : ℕ} (q : Fin L → ℕ) (pool : Fin K → RnsCt L N)
    (out : RnsCt L N) : Decidable (PerLimbMul q pool out) := Fintype.decidableForallFintype

/-- The per-limb system is NECESSARY — it is not wrong, it is incomplete. Every honest evaluation
satisfies it, which is exactly why its failure to imply `BoundMul` is invisible to a completeness
test and to every honest-prover differential. -/
theorem bound_imp_perLimb {L N K : ℕ} {q : Fin L → ℕ} {pool : Fin K → RnsCt L N}
    {out : RnsCt L N} (h : BoundMul q pool out) : PerLimbMul q pool out := by
  obtain ⟨ja, jb, h⟩ := h
  exact fun i => ⟨ja, jb, h i⟩

/-! ## 2. HOLE A — provenance. The exhibit.

Two limbs (`q₀ = 3`, `q₁ = 5`), one coefficient (`N = 1`, where `negaMul` is integer multiplication
by `Bfv.negaMul_one_eq_mul`), and a pool of two ciphertexts: `ct₀ = (1, 0)` and `ct₁ = (0, 1)`.

The forgery takes limb 0 from `ct₀·ct₀` and limb 1 from `ct₁·ct₁`. -/

/-- The exhibit's RNS basis: `q₀ = 3`, `q₁ = 5`. -/
def exhibitQ : Fin 2 → ℕ := fun i => if i = 0 then 3 else 5

/-- The exhibit's pool: `ct_j` has residue `1` at limb `j` and `0` at the other limb. -/
def exhibitPool : Fin 2 → RnsCt 2 1 := fun j i _ => if (j : ℕ) = (i : ℕ) then 1 else 0

/-- **The forgery.** Limb 0 is the limb-0 product of `ct₀` with itself; limb 1 is the limb-1
product of `ct₁` with itself. Neither limb is anomalous. Together they are a ciphertext that no
evaluation ever produced. -/
def exhibitOut : RnsCt 2 1 := fun _ _ => 1

/-- **HOLE A, EXHIBITED — every per-limb equation is satisfied.** Limb 0 checks against `ct₀`,
limb 1 checks against `ct₁`. A verifier that checks the `L` equations separately accepts. -/
theorem exhibit_perLimb : PerLimbMul exhibitQ exhibitPool exhibitOut := by decide

/-- **HOLE A, EXHIBITED — and NO single pair from the pool works.** All four candidate pairs
`(ct₀,ct₀)`, `(ct₀,ct₁)`, `(ct₁,ct₀)`, `(ct₁,ct₁)` fail at some limb. The accepted object is not
the product of any pair of committed ciphertexts. -/
theorem exhibit_not_bound : ¬ BoundMul exhibitQ exhibitPool exhibitOut := by decide

/-- **THE HOLE, as the implication it refutes.** `PerLimbMul` does not imply `BoundMul`: a
per-limb verifier is strictly weaker than the statement it is believed to prove. -/
theorem perLimb_not_imp_bound :
    ∃ (q : Fin 2 → ℕ) (pool : Fin 2 → RnsCt 2 1) (out : RnsCt 2 1),
      PerLimbMul q pool out ∧ ¬ BoundMul q pool out :=
  ⟨exhibitQ, exhibitPool, exhibitOut, exhibit_perLimb, exhibit_not_bound⟩

/-- CRT reconstruction at the exhibit basis `(3, 5)`: the representative in `[0, 15)` with residue
`r 0` mod 3 and `r 1` mod 5 (`10 ≡ 1, 0` and `6 ≡ 0, 1`). -/
def exhibitCrt (r : Fin 2 → ℤ) : ℤ := (10 * r 0 + 6 * r 1) % 15

/-- ⚑ **THE FORGERY IS A WRONG ANSWER, not merely an unbound proof.** In the reconstructed ring
`ℤ/15` the accepted output is `1`, while the only values an honest evaluation of this pool can
produce are `10` (`ct₀·ct₀`), `6` (`ct₁·ct₁`) and `0` (either mixed pair). **`1` is none of them.**

A soundness break that produced only well-formed-but-unattributable outputs would be a weaker
finding; this one lets the prover commit to a ciphertext outside the image of the evaluation. -/
theorem exhibit_accepted_value_is_dishonest :
    exhibitCrt (fun i => exhibitOut i 0) = 1 ∧
      exhibitCrt (fun i => negaMul (exhibitPool 0 i) (exhibitPool 0 i) 0) = 10 ∧
      exhibitCrt (fun i => negaMul (exhibitPool 1 i) (exhibitPool 1 i) 0) = 6 ∧
      exhibitCrt (fun i => negaMul (exhibitPool 0 i) (exhibitPool 1 i) 0) = 0 ∧
      exhibitCrt (fun i => negaMul (exhibitPool 1 i) (exhibitPool 0 i) 0) = 0 := by
  decide

/-- **Satisfiability side (house law: a floor must be satisfiable AND refutable).** `BoundMul` is
not an empty predicate that `exhibit_not_bound` refutes for free — the honest product of `ct₀` with
itself satisfies it. Without this, `¬ BoundMul` would be evidence about a vacuous relation. -/
theorem exhibit_bound_satisfiable :
    BoundMul exhibitQ exhibitPool (fun i => negaMul (exhibitPool 0 i) (exhibitPool 0 i)) := by
  decide

#assert_all_clean [Bfv.limbMulRel_iff_modEq, Bfv.bound_imp_perLimb, Bfv.exhibit_perLimb,
  Bfv.exhibit_not_bound, Bfv.perLimb_not_imp_bound, Bfv.exhibit_accepted_value_is_dishonest,
  Bfv.exhibit_bound_satisfiable]

/-! ## 3. The size of the hole: the selector space. -/

/-- **The ct×ct attack surface.** A per-limb verifier lets the prover pick an operand PAIR
independently at each of the `L` limbs: `(K²)^L` selectors, of which only `K²` are honest. At the
deployed tower (`L = 3`) with a two-ciphertext pool that is `64` selectors and `4` honest ones —
**60 forgeries**, and the count grows exponentially in the limb count. -/
theorem forgery_surface_ctct (L K : ℕ) :
    Fintype.card (Fin L → Fin K × Fin K) = (K * K) ^ L := by
  simp

/-- **The ct×pt attack surface**, for comparison: the public multiplier cannot be forged, so only
the ciphertext operand carries a selector — `K^L` against `K` honest. A square root of the ct×ct
surface, and still `2³ = 8` against `2` at the deployed tower. -/
theorem forgery_surface_ctpt (L K : ℕ) : Fintype.card (Fin L → Fin K) = K ^ L := by
  simp

/-- The deployed shape, pinned: three limbs, a two-ciphertext pool, **60 ct×ct forgeries against 4
honest selectors**, and **6 ct×pt forgeries against 2**. -/
theorem deployed_forgery_counts :
    Fintype.card (Fin 3 → Fin 2 × Fin 2) = 64 ∧ Fintype.card (Fin 3 → Fin 2) = 8 := by
  simp

/-! ## 4. HOLE B — the rescale is not limb-local.

Hole A is about which object a limb's equation is fed. Hole B is worse: for ct×ct there is a step
whose output residue at limb `i` is **not a function of the input residues at limb `i` at all**, so
there is no per-limb equation to feed in the first place. -/

/-- The BFV ct×ct rescale on the reconstructed integer, `⌊t·x/Q⌉` round-half-up — the same
convention and the same integer form as `Bfv.mulPhase`. -/
def rescale (t Q x : ℤ) : ℤ := (2 * t * x + Q) / (2 * Q)

/-- ⚑ **HOLE B, EXHIBITED — `⌊t·x/Q⌉` IS NOT LIMB-LOCAL.** Two integers with the SAME residue mod
`q₀ = 3` whose rescales differ mod `q₀`. The rescale reads the CRT reconstruction; a limb sees only
its own residue; so **no system of per-limb equations can pin it**, however the operands are bound.

This is the defect `notes/archive/vfhe-shortest-path.md` names ("the extended-basis tensor + t/Q
rounding is not expressible in any single limb"), and it is INDEPENDENT of Hole A: a commitment
that binds the limb vector as one object closes Hole A and leaves this untouched. The fix for Hole
B is different in kind — the rescale must be arithmetized over a representation that carries the
reconstruction (an extended/redundant basis, or a single prime). -/
theorem rescale_not_limb_local :
    ∃ x y : ℤ, x % 3 = y % 3 ∧ rescale 2 15 x % 3 ≠ rescale 2 15 y % 3 :=
  ⟨0, 15, by decide, by decide⟩

/-- The companion positive fact, so `rescale_not_limb_local` is not a statement about a degenerate
function: the rescale is not constant either, and it does agree with itself. A non-limb-local map
that was also nowhere-defined would refute nothing. -/
theorem rescale_nondegenerate : rescale 2 15 0 = 0 ∧ rescale 2 15 15 = 2 := by decide

#assert_all_clean [Bfv.forgery_surface_ctct, Bfv.forgery_surface_ctpt, Bfv.deployed_forgery_counts,
  Bfv.rescale_not_limb_local, Bfv.rescale_nondegenerate]

/-! ## 5. What the per-limb system DOES pin — and why "CRT consistency" is a tautology. -/

/-- **The per-limb system is EXACTLY the `R_Q` relation, once the operands are fixed.** Under
pairwise-coprime moduli, agreeing on every limb is agreeing mod `∏ qᵢ`: the CRT isomorphism, with
no loss. So the hole is not in the arithmetic and cannot be closed by strengthening the equations —
**all of Hole A is in which object each equation is fed.** -/
theorem perLimb_pins_modProd {L : ℕ} (q : Fin L → ℤ)
    (hcop : Pairwise (fun i j => IsCoprime (q i) (q j))) (a b : ℤ) (h : ∀ i, q i ∣ (b - a)) :
    (∏ i, q i) ∣ (b - a) :=
  Fintype.prod_dvd_of_coprime hcop h

/-- ⚑ **THE NAMED CANDIDATE FIX IS VACUOUS.** `VERDICTS.md` lists "a CRT-consistency relation over
the limbs" first among the closures. For pairwise-coprime moduli the CRT map
`ZMod (∏ qᵢ) ≃+* Π ZMod qᵢ` is a **bijection**, so every limb tuple whatsoever is the image of a
ring element: the check can never refuse, on any input, and adds exactly zero constraints' worth of
soundness. The forgery of §2 is itself perfectly CRT-consistent — `exhibitCrt` reconstructs it to
`1 ∈ ℤ/15`.

A consistency check over the BASE basis is not a weak fix; it is not a fix. (A check over a
REDUNDANT basis — an auxiliary modulus the honest limbs must also agree with — is a different
object and is not refuted here.) -/
theorem crt_consistency_vacuous {L : ℕ} (q : Fin L → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (q i) (q j))) (r : Π i, ZMod (q i)) :
    ∃ x : ZMod (∏ i, q i), ZMod.prodEquivPi q hcop x = r :=
  ⟨(ZMod.prodEquivPi q hcop).symm r, (ZMod.prodEquivPi q hcop).apply_symm_apply r⟩

/-- The deployed tower is pairwise coprime, so the two theorems above apply to it and not merely to
the exhibit: `q = 0xffffee001 · 0xffffc4001 · 0x1ffffe0001`, the `fhe.rs` degree-4096 set of
`Bfv.q4096`. -/
theorem deployed_moduli_pairwise_coprime :
    Nat.Coprime 0xffffee001 0xffffc4001 ∧ Nat.Coprime 0xffffee001 0x1ffffe0001 ∧
      Nat.Coprime 0xffffc4001 0x1ffffe0001 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- And the tower really is the deployed modulus: the three limbs multiply to `Bfv.q4096`. -/
theorem deployed_moduli_prod : 0xffffee001 * 0xffffc4001 * 0x1ffffe0001 = q4096 := rfl

/-! ## 6. The ct×pt narrowing — Hole B absent, Hole A alive at a square root. -/

/-- **ct×pt IS limb-local: Hole B does not arise.** A public integer multiplier commutes with
reduction mod every `qᵢ`, so limb `i` of the output is a function of limb `i` of the input. This is
the same property `Bfv.stepR_noise_le` runs on — the reason the coefficient-encoded matmul route
has a PROVABLE noise budget is also the reason it has no expressibility hole. Contrast
`rescale_not_limb_local`. -/
theorem scalarStep_limb_local (q S x y : ℤ) (h : x % q = y % q) : (S * x) % q = (S * y) % q :=
  Int.ModEq.mul_left S h

/-- The ct×pt per-limb check: a PUBLIC multiplier `S` (identical in every limb, so unforgeable)
against a pool-selected ciphertext operand. -/
def LimbPtRel (q : ℕ) {N : ℕ} (S : Rn N) (a c : Rn N) : Prop :=
  ∀ k, c k % (q : ℤ) = negaMul S a k % (q : ℤ)

/-- Honest ct×pt: one ciphertext, every limb. -/
def BoundPt {L N K : ℕ} (q : Fin L → ℕ) (S : Rn N) (pool : Fin K → RnsCt L N)
    (out : RnsCt L N) : Prop :=
  ∃ j : Fin K, ∀ i : Fin L, LimbPtRel (q i) S (pool j i) (out i)

/-- Per-limb ct×pt: a ciphertext per limb. -/
def PerLimbPt {L N K : ℕ} (q : Fin L → ℕ) (S : Rn N) (pool : Fin K → RnsCt L N)
    (out : RnsCt L N) : Prop :=
  ∀ i : Fin L, ∃ j : Fin K, LimbPtRel (q i) S (pool j i) (out i)

instance instDecidableLimbPtRel (q : ℕ) {N : ℕ} (S a c : Rn N) :
    Decidable (LimbPtRel q S a c) := Fintype.decidableForallFintype

instance instDecidableBoundPt {L N K : ℕ} (q : Fin L → ℕ) (S : Rn N)
    (pool : Fin K → RnsCt L N) (out : RnsCt L N) : Decidable (BoundPt q S pool out) :=
  Fintype.decidableExistsFintype

instance instDecidablePerLimbPt {L N K : ℕ} (q : Fin L → ℕ) (S : Rn N)
    (pool : Fin K → RnsCt L N) (out : RnsCt L N) : Decidable (PerLimbPt q S pool out) :=
  Fintype.decidableForallFintype

/-- The public multiplier of the exhibit: the constant `1`, which at `N = 1` makes `negaMul S a`
the identity on the ciphertext operand. Public means IDENTICAL IN EVERY LIMB — that is exactly the
property that removes it from the prover's selector space. -/
def exhibitS : Rn 1 := fun _ => 1

/-- **Hole A SURVIVES ct×pt.** With a public multiplier and the same two-ciphertext pool, the
frankenstein still passes every per-limb equation and still matches no single ciphertext. Making one
operand public halves the exponent of the attack surface; it does not close the hole. -/
theorem perLimbPt_not_imp_boundPt :
    PerLimbPt exhibitQ exhibitS exhibitPool exhibitOut ∧
      ¬ BoundPt exhibitQ exhibitS exhibitPool exhibitOut := by
  constructor <;> decide

/-- **The hole is a function of the POOL, not of the operation: a singleton pool closes it.** With
exactly one ciphertext available there is nothing to mix, and the per-limb system implies the bound
one outright. At depth 1 against a single committed input, cross-limb binding is vacuous; at the
deployed depth 2 an intermediate ciphertext exists and it is not. -/
theorem perLimbPt_singleton_pool_bound {L N : ℕ} (q : Fin L → ℕ) (S : Rn N)
    (pool : Fin 1 → RnsCt L N) (out : RnsCt L N) (h : PerLimbPt q S pool out) :
    BoundPt q S pool out := by
  refine ⟨0, fun i => ?_⟩
  obtain ⟨j, hj⟩ := h i
  rw [Subsingleton.elim j (0 : Fin 1)] at hj
  exact hj

/-- The same statement for ct×ct, so the singleton escape is not an artifact of the ct×pt shape. -/
theorem perLimb_singleton_pool_bound {L N : ℕ} (q : Fin L → ℕ) (pool : Fin 1 → RnsCt L N)
    (out : RnsCt L N) (h : PerLimbMul q pool out) : BoundMul q pool out := by
  refine ⟨0, 0, fun i => ?_⟩
  obtain ⟨ja, jb, hj⟩ := h i
  rw [Subsingleton.elim ja (0 : Fin 1), Subsingleton.elim jb (0 : Fin 1)] at hj
  exact hj

/-! ## 7. The closures. -/

/-- **CLOSURE 1 — one commitment over the limb vector.** The fix is the `∃`/`∀` hoist itself: an
arithmetization that carries ONE opening index per operand, used by every limb, checks `BoundMul`
by construction. This is a statement about the SHAPE of the checked predicate, not an extra
constraint, which is why it costs no arithmetic — the same residues are already committed; what
changes is that every limb's equation must open at the same index.

Stated as an `Iff` so it is visible that this is the honest predicate, not an approximation of it. -/
theorem boundMul_iff_sharedSelector {L N K : ℕ} (q : Fin L → ℕ) (pool : Fin K → RnsCt L N)
    (out : RnsCt L N) :
    BoundMul q pool out ↔
      ∃ sel : Fin K × Fin K, ∀ i : Fin L,
        LimbMulRel (q i) (pool sel.1 i) (pool sel.2 i) (out i) :=
  ⟨fun ⟨a, b, h⟩ => ⟨(a, b), h⟩, fun ⟨sel, h⟩ => ⟨sel.1, sel.2, h⟩⟩

/-- **CLOSURE 2 — a random linear combination across the limbs, with its soundness error.**

If the prover's limb vector differs from the committed one at ANY limb, the combined equation
`∑ᵢ γⁱ·dᵢ = 0` accepts for at most `L − 1` challenges `γ`. The error is therefore `(L−1)/|F|`:
`2/|F|` at the deployed three-limb tower, negligible at any proof field we use.

⚠ **What this theorem does NOT say, and the cost lives here.** The sum `∑ γⁱ·dᵢ` is taken in ONE
field `F`. The deployed limbs are 36-, 36- and 37-bit primes and the proof field is 31-bit BabyBear,
so the residues do not live in `F` — each must be embedded as ≥2 felts with a range check, or the
embedding is not injective and this bound is about the wrong quantity. That embedding, not this
lemma, is what the closure costs. -/
theorem rlc_binds {F : Type*} [Field F] [DecidableEq F] [Fintype F] {L : ℕ}
    (d : Fin L → F) (hd : ∃ i, d i ≠ 0) :
    (univ.filter fun γ : F => ∑ i : Fin L, γ ^ (i : ℕ) * d i = 0).card ≤ L - 1 := by
  classical
  set p : Polynomial F := ∑ i : Fin L, Polynomial.C (d i) * Polynomial.X ^ (i : ℕ) with hp
  have hcoeff : ∀ j : Fin L, p.coeff (j : ℕ) = d j := by
    intro j
    rw [hp, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun h : (j : ℕ) = (i : ℕ) => hi (Fin.val_injective h).symm), mul_zero]
    · simp
  have hp0 : p ≠ 0 := by
    obtain ⟨i, hi⟩ := hd
    intro h
    exact hi (by rw [← hcoeff i, h, Polynomial.coeff_zero])
  have hdeg : p.natDegree ≤ L - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    have hi := i.isLt
    rw [Polynomial.natDegree_X_pow]
    omega
  have hev : ∀ γ : F, Polynomial.eval γ p = ∑ i : Fin L, γ ^ (i : ℕ) * d i := by
    intro γ
    rw [hp, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hsub : (univ.filter fun γ : F => ∑ i : Fin L, γ ^ (i : ℕ) * d i = 0) ⊆ p.roots.toFinset := by
    intro γ hγ
    simp only [mem_filter, mem_univ, true_and] at hγ
    refine Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hp0, ?_⟩)
    show Polynomial.eval γ p = 0
    rw [hev γ]
    exact hγ
  calc (univ.filter fun γ : F => ∑ i : Fin L, γ ^ (i : ℕ) * d i = 0).card
      ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ L - 1 := hdeg

/-- **Teeth for CLOSURE 2: the hypothesis is load-bearing.** Drop `hd` (the limb vector agrees
everywhere) and the conclusion is FALSE — every challenge accepts, which is exactly what a
completeness test sees. A bound whose failing side is never exhibited would be satisfied by a check
that always passes. -/
theorem rlc_binds_hypothesis_necessary :
    ¬ ((univ.filter fun γ : ZMod 5 => ∑ i : Fin 2, γ ^ (i : ℕ) * (0 : ZMod 5) = 0).card ≤ 1) := by
  decide

#assert_all_clean [Bfv.perLimb_pins_modProd, Bfv.crt_consistency_vacuous,
  Bfv.deployed_moduli_pairwise_coprime, Bfv.deployed_moduli_prod, Bfv.scalarStep_limb_local,
  Bfv.perLimbPt_not_imp_boundPt, Bfv.perLimbPt_singleton_pool_bound,
  Bfv.perLimb_singleton_pool_bound, Bfv.boundMul_iff_sharedSelector, Bfv.rlc_binds,
  Bfv.rlc_binds_hypothesis_necessary]

end Bfv
