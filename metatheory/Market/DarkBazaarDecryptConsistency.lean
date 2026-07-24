/-
# Market.DarkBazaarDecryptConsistency — the crypto CORE under `SameOpening`:
# a safe-noise phase determines its message UNIQUELY.

**What this file is for.** The Tier-0 apex relation (`Market.DarkBazaarSameOpening.SameOpening`)
says a BFV ciphertext opens to the committed book: `∃ e, SafeNoise P |e| ∧ ct.phase = Δ·m + e`.
That relation is only WELL-DEFINED as "the ciphertext's book" if the phase cannot safely open to
two different messages — otherwise "the same opening" is ambiguous and the gadget would constrain
nothing.  This file proves that uniqueness over the real `Bfv.Noise` objects:

  * **`phase_two_safe_openings_agree` (THE KEYSTONE)** — if `p = Δ·m + e` with `SafeNoise P |e|`
    AND `p = Δ·m₂ + e₂` with `SafeNoise P |e₂|`, then `m = m₂`.  No side hypotheses: every
    arithmetic fact is drawn from the `Params` structure itself (`q_eq : q = Δ·t + r`,
    `r_lt_t`, `Δ_pos`, `t_pos`).  Messages are ℤ (the packed book is an integer, and the
    centered encoding is signed), so this is uniqueness over ALL of ℤ, not just `[0, t)`.
  * **`decryptConsistent_decrypts`** — the unique message is the one `Bfv.decryptPhase` actually
    computes (via `decrypt_exact`), for in-range ℕ messages.  So the relation is not a free-
    floating predicate: its unique witness is what the real decoder returns.
  * **`packedBook_openings_agree`** — composed with `packedBook_injective_on_orders`: a phase
    that safely opens to two packed books forces the same ORDERS.  The ciphertext cannot open
    to two different books — exactly what `SameOpening` needs to be meaningful.
  * **FAILING SIDE (`phase_without_bound_does_not_determine`)** — delete the noise bound and
    uniqueness is FALSE: the phase `Δ` decomposes as `Δ·1 + 0` and as `Δ·0 + Δ`.  And
    **`delta_not_safe`** proves the aliasing noise `Δ` is ALWAYS over the margin (for every
    parameter set, from `q = Δ·t + r` alone) — so the counterexample lives exactly and only
    outside the safe region, which is consistency, not luck.

**Honest scope (NAMED, not hidden).**
  * SCALAR model: one integer phase (`Bfv.Ct`), the same model as `Bfv.Noise`.  The deployed
    ciphertext is RNS-polynomial with `n = 4096` slots; the per-slot uniqueness is this theorem
    applied coordinatewise, and that polynomial lift is the poly-lift lane's composition, NOT
    proved here.
  * ℤ-phase, not mod-`q`: same NAMED model gap as `Bfv.Noise` (mitigated there by
    `decryptPhase_add_q` + the fold envelope).
  * `BfvOpensTo P ct m` (the apex file `DarkBazaarSameOpening`) is exactly
    `DecryptConsistent P ct.phase m` — this file does NOT import the apex file (the supervisor
    wires imports; the apex should sit ABOVE this core, not below), so that bridge is one
    `Iff.rfl` at wiring time, named here rather than smuggled.
  * Nothing here is a circuit.  The in-circuit `SameOpeningGadget` must CONSTRAIN this relation
    over the emitted RNS objects; this file is the semantic law the gadget discharges.
-/
import Bfv.Noise
import Market.DarkBazaarPrivateDescriptor
import Dregg2.Tactics

namespace Market.DarkBazaarDecryptConsistency

open Bfv Market.DarkBazaarPrivateDescriptor

set_option autoImplicit false

/-- **The decryption-consistency relation**: phase `p` is a valid BFV encryption of message `m` —
there is a noise `e` inside the decrypt margin with `p = Δ·m + e`.  This is the relation the
Tier-0 gadget must constrain in-circuit; `BfvOpensTo P ct m` (apex file) is definitionally
`DecryptConsistent P ct.phase m`. -/
def DecryptConsistent (P : Params) (p m : ℤ) : Prop :=
  ∃ e : ℤ, SafeNoise P |e| ∧ p = (P.Δ : ℤ) * m + e

/-! ## 1. The keystone: two safe openings of one phase agree. -/

/-- **THE KEYSTONE — safe-noise openings are UNIQUE.**  If `p = Δ·m + e` with `SafeNoise P |e|`
and `p = Δ·m₂ + e₂` with `SafeNoise P |e₂|`, then `m = m₂`.  All arithmetic side conditions come
from the `Params` structure itself (`q = Δ·t + r`, `r < t`, `Δ ≥ 1`, `t ≥ 1`) — no extra
hypotheses.  Proof shape: a collision forces `Δ·(m − m₂) = e₂ − e`, so a nonzero difference makes
the noises bridge a gap of at least `Δ`; but two safe margins sum to strictly less than that
(using `r < t`, which kills the residue cross-term in both the `t = 1` and `t ≥ 2` regimes). -/
theorem phase_two_safe_openings_agree {P : Params} {p m m₂ e e₂ : ℤ}
    (he : SafeNoise P |e|) (hp : p = (P.Δ : ℤ) * m + e)
    (he₂ : SafeNoise P |e₂|) (hp₂ : p = (P.Δ : ℤ) * m₂ + e₂) :
    m = m₂ := by
  by_contra hne
  -- ground facts, all from the Params structure
  have hQeq : (P.q : ℤ) = (P.Δ : ℤ) * (P.t : ℤ) + (P.r : ℤ) := by exact_mod_cast P.q_eq
  have hT1 : (1 : ℤ) ≤ (P.t : ℤ) := by exact_mod_cast P.t_pos
  have hD1 : (1 : ℤ) ≤ (P.Δ : ℤ) := by exact_mod_cast P.Δ_pos
  have hR0 : (0 : ℤ) ≤ (P.r : ℤ) := Int.natCast_nonneg _
  have hRT : (P.r : ℤ) < (P.t : ℤ) := by exact_mod_cast P.r_lt_t
  -- the collision equation: Δ·(m − m₂) = e₂ − e
  have hcol : (P.Δ : ℤ) * (m - m₂) = e₂ - e := by
    have h := hp.symm.trans hp₂
    have hexp : (P.Δ : ℤ) * (m - m₂) = (P.Δ : ℤ) * m - (P.Δ : ℤ) * m₂ := by ring
    linarith [h, hexp]
  -- a nonzero integer difference has |·| ≥ 1, so the bridged gap is ≥ Δ
  have hd : m - m₂ ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (1 : ℤ) ≤ |m - m₂| := by
    rcases lt_or_gt_of_ne hd with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have habs : |(P.Δ : ℤ) * (m - m₂)| = (P.Δ : ℤ) * |m - m₂| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℤ) ≤ (P.Δ : ℤ))]
  have hDle : (P.Δ : ℤ) ≤ |e₂ - e| := by
    rw [← hcol, habs]
    have hmul := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℤ) ≤ (P.Δ : ℤ))
    linarith [hmul]
  -- but two safe noises sum below the gap
  have hDsum : (P.Δ : ℤ) ≤ |e₂| + |e| :=
    le_trans hDle (Bfv.abs_sub_le_abs_add_abs e₂ e)
  have hscale : 2 * (P.t : ℤ) * (P.Δ : ℤ) ≤ 2 * (P.t : ℤ) * (|e₂| + |e|) :=
    mul_le_mul_of_nonneg_left hDsum (by linarith)
  unfold SafeNoise at he he₂
  rcases (by omega : 2 ≤ (P.t : ℤ) ∨ (P.t : ℤ) = 1) with h2 | hT
  · -- t ≥ 2: the residue cross-term dominates its own slack
    have hTR : 2 * (P.r : ℤ) ≤ (P.t : ℤ) * (P.r : ℤ) :=
      mul_le_mul_of_nonneg_right h2 hR0
    linarith [he, he₂, hscale, hQeq, hTR, hR0]
  · -- t = 1: the residue is zero (r < t = 1), and q = Δ
    have hR : (P.r : ℤ) = 0 := by omega
    rw [hT, hR] at he he₂ hQeq
    rw [hT] at hscale
    linarith [he, he₂, hscale, hQeq]

/-- Relation form of the keystone: `DecryptConsistent` soundly DETERMINES the message — the
phase is a function of nothing; the message is a function of the phase. -/
theorem decryptConsistent_unique {P : Params} {p m m₂ : ℤ}
    (h : DecryptConsistent P p m) (h₂ : DecryptConsistent P p m₂) : m = m₂ := by
  obtain ⟨e, he, hp⟩ := h
  obtain ⟨e₂, he₂, hp₂⟩ := h₂
  exact phase_two_safe_openings_agree he hp he₂ hp₂

/-! ## 2. The unique message is what the real decoder computes. -/

/-- The relation's unique witness is not free-floating: for an in-range message, `decryptPhase`
RETURNS it (`Bfv.decrypt_exact`).  So `DecryptConsistent P p m` + range gives
`decryptPhase P p = m` — the semantic law a same-opening gadget makes the verifier trust. -/
theorem decryptConsistent_decrypts {P : Params} {p : ℤ} (m : ℕ) (hm : m < P.t)
    (h : DecryptConsistent P p (m : ℤ)) : decryptPhase P p = m := by
  obtain ⟨e, he, hp⟩ := h
  rw [hp]
  exact decrypt_exact P m e hm he

/-! ## 3. Composed with the real book packing: one phase, one order book. -/

/-- **The ciphertext cannot open to two different BOOKS.**  A phase that safely opens to
`packedBook w` and to `packedBook w₂` forces `w.orders = w₂.orders`
(via `packedBook_injective_on_orders` — the real 28-bit injective packing, not a model).  This is
the exact well-definedness fact `SameOpening` rests on. -/
theorem packedBook_openings_agree {P : Params} {p : ℤ} {w w₂ : PrivateWitness}
    (h : DecryptConsistent P p (packedBook w))
    (h₂ : DecryptConsistent P p (packedBook w₂)) :
    w.orders = w₂.orders :=
  packedBook_injective_on_orders (decryptConsistent_unique h h₂)

/-! ## 4. FAILING SIDE: without the noise bound, the phase determines NOTHING. -/

/-- The aliasing noise `Δ` is over the decrypt margin for EVERY parameter set — from
`q = Δ·t + r` and `r < t` alone.  (`2t·Δ + 2(t−1)·r ≥ q` always: `t·Δ ≥ t > r`.)  So the
counterexample below cannot be smuggled inside the safe region; the bound and the uniqueness
theorem partition reality with no overlap. -/
theorem delta_not_safe (P : Params) : ¬ SafeNoise P (P.Δ : ℤ) := by
  unfold SafeNoise
  intro h
  have hQeq : (P.q : ℤ) = (P.Δ : ℤ) * (P.t : ℤ) + (P.r : ℤ) := by exact_mod_cast P.q_eq
  have hT1 : (1 : ℤ) ≤ (P.t : ℤ) := by exact_mod_cast P.t_pos
  have hD1 : (1 : ℤ) ≤ (P.Δ : ℤ) := by exact_mod_cast P.Δ_pos
  have hR0 : (0 : ℤ) ≤ (P.r : ℤ) := Int.natCast_nonneg _
  have hRT : (P.r : ℤ) < (P.t : ℤ) := by exact_mod_cast P.r_lt_t
  have hTD : (P.t : ℤ) ≤ (P.t : ℤ) * (P.Δ : ℤ) :=
    le_mul_of_one_le_right (by linarith) hD1
  have hTR0 : (0 : ℤ) ≤ ((P.t : ℤ) - 1) * (P.r : ℤ) :=
    mul_nonneg (by linarith) hR0
  linarith [h, hQeq, hTD, hTR0, hRT]

/-- **RED — drop the bound, lose the message.**  The keystone with its `SafeNoise` hypotheses
DELETED is refutable: the phase `Δ` is `Δ·1 + 0` and also `Δ·0 + Δ`, so unbounded noise lets one
phase decompose over two different messages.  The noise bound is load-bearing, not decoration. -/
theorem phase_without_bound_does_not_determine (P : Params) :
    ¬ (∀ p m m₂ e e₂ : ℤ,
        p = (P.Δ : ℤ) * m + e → p = (P.Δ : ℤ) * m₂ + e₂ → m = m₂) := by
  intro h
  exact one_ne_zero (h (P.Δ : ℤ) 1 0 0 (P.Δ : ℤ) (by ring) (by ring))

/-- The RED's witness, itemized: both decompositions hold, and the aliasing noise is PROVABLY
unsafe — the ambiguity exists exactly where `delta_not_safe` says the margin is gone. -/
theorem ambiguity_witness_noise_unsafe (P : Params) :
    ((P.Δ : ℤ) = (P.Δ : ℤ) * 1 + 0)
      ∧ ((P.Δ : ℤ) = (P.Δ : ℤ) * 0 + (P.Δ : ℤ))
      ∧ ¬ SafeNoise P |(P.Δ : ℤ)| := by
  refine ⟨by ring, by ring, ?_⟩
  rw [abs_of_nonneg (Int.natCast_nonneg _ : (0 : ℤ) ≤ (P.Δ : ℤ))]
  exact delta_not_safe P

/-! ## 5. Deployed pins: the relation is inhabited AND discriminating on the real numbers. -/

/-- Zero noise is inside the margin on the deployed fhe.rs degree-4096 set (kernel-checked on
the real 109-bit `q`).  This also discharges, on the deployed numbers, the `hpos` hypothesis the
apex RED (`independent_valid_objects_break_same_opening`) takes as input. -/
theorem deployed_zero_noise_safe : SafeNoise fheRs4096 (0 : ℤ) := by
  unfold SafeNoise
  decide

/-- On the deployed parameters: the honest phase `Δ·1` safely opens to `1`, and PROVABLY has no
safe opening to `0` — the relation admits the true message and rejects the neighbor.  (The
rejection is the keystone at work, not a `decide` coincidence.) -/
theorem deployed_safe_opening_rejects_alias :
    DecryptConsistent fheRs4096 ((fheRs4096.Δ : ℤ) * 1) 1
      ∧ ¬ DecryptConsistent fheRs4096 ((fheRs4096.Δ : ℤ) * 1) 0 := by
  have hopen : DecryptConsistent fheRs4096 ((fheRs4096.Δ : ℤ) * 1) 1 :=
    ⟨0, by simpa using deployed_zero_noise_safe, by ring⟩
  exact ⟨hopen, fun hbad => one_ne_zero (decryptConsistent_unique hopen hbad)⟩

#assert_all_clean [Market.DarkBazaarDecryptConsistency.phase_two_safe_openings_agree,
  Market.DarkBazaarDecryptConsistency.decryptConsistent_unique,
  Market.DarkBazaarDecryptConsistency.decryptConsistent_decrypts,
  Market.DarkBazaarDecryptConsistency.packedBook_openings_agree,
  Market.DarkBazaarDecryptConsistency.delta_not_safe,
  Market.DarkBazaarDecryptConsistency.phase_without_bound_does_not_determine,
  Market.DarkBazaarDecryptConsistency.ambiguity_witness_noise_unsafe,
  Market.DarkBazaarDecryptConsistency.deployed_zero_noise_safe,
  Market.DarkBazaarDecryptConsistency.deployed_safe_opening_rejects_alias]

end Market.DarkBazaarDecryptConsistency
