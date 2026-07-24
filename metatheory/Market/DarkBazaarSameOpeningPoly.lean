/-
# Market.DarkBazaarSameOpeningPoly — the Tier-0 SAME-OPENING relation lifted to the
  per-slot (polynomial-coefficient) ciphertext model.

`Market.DarkBazaarSameOpening` states the apex relation over ONE scalar `Bfv.Ct` (a single phase
`Δ·m + e`) carrying the whole 28-bit `packedBook w`.  The DEPLOYED object is not one scalar: the
composite receipt (`HANDOFF-FHEGG-CODEX-SWARM-RESULTS.md` §54) carries **four ordered ciphertext
rows — one per order slot** — and `bfv_lean.rs::LeanCiphertext` stores each ring element as RNS
residue rows `rows[modulus][coeff]`.  The Lean `Bfv` model is scalar-per-coefficient by declared
scope (`Bfv.Noise` module doc: "no polynomial ring here — a NAMED model gap"), so the honest lift
available TODAY is the **per-slot lift**: each order slot is one encrypted coefficient (one scalar
`Ct`), and the polynomial relation is the conjunction of per-slot scalar openings PLUS the base-128
packing that the private root already commits (`rootPreimage` absorbs `packedBook w`).

**Substrate, out loud:** this file is the Lean-authored relation layer.  The `SameOpeningGadget`
that would discharge it is an in-circuit relation and therefore MUST also be authored in Lean over
the emitted descriptor objects (like `DarkBazaarPrivateDescriptor`'s AIR) — never a hand-written
Rust AIR.  Nothing here is a gadget; it is the statement the future Lean-authored gadget must hit.

**What is PROVED here (each with a failing side or an exact-arithmetic spine):**

  1. `SameOpeningPoly` — the per-slot relation: every slot ciphertext opens to that slot's REAL
     `orderCode (w.orders j)` within the fresh-noise budget `B`, `B` is inside the decrypt margin,
     and the root is the REAL `orderRoot` of the SAME `w` (which commits the packing).
  2. `slot_projection` + `slot_decrypts_exact` — (a) the per-slot projection: each slot satisfies
     the scalar opening relation `BfvOpensTo` at its own coefficient, and (via the `Bfv` keystone
     `decrypt_exact`) decrypts to EXACTLY its order code.
  3. `sameOpeningPoly_packs_to_sameOpening` — (a) the packing connection: the homomorphic base-128
     recombination of the four slots (public-scalar-muls + adds — exactly the fold-path ops)
     satisfies the PROVED scalar apex relation `SameOpening` at `packedBook w`, under the exact
     noise headroom `SafeNoise P (PACK_GAIN·B)` with `PACK_GAIN = 1+128+128²+128³`.  The lift and
     the scalar apex are one relation family, not two stories.
  4. `wrong_slot_breaks_sameOpeningPoly` — **RED (the per-slot lift of the scalar RED):** a slot-`j`
     ciphertext that exactly encrypts a WRONG order is INDEPENDENTLY valid, the root of the intended
     `w` is independently valid, yet `SameOpeningPoly` is FALSE — via `delta_diff_unsafe`, because a
     wrong code forces slot noise `Δ·d`, provably outside any in-margin budget.
  5. `wrong_slot_breaks_packed_sameOpening` — **RED, packed:** the same single-slot forgery
     SURVIVES packing — the recombined carrier breaks the scalar `SameOpening` too (forced noise
     `Δ·128^j·d`).  The per-slot and scalar REDs are the same gap seen at two resolutions.
  6. Deployed pins (`decide` on the real fhe.rs degree-4096 numbers): four slots of fresh
     `B = 2^20` noise recombine with margin to spare, `q ≤ 2tΔ` (the RED's parameter fact) holds,
     and order codes fit the plaintext window.

**NAMED, not proved — what the full RNS/NTT representation adds beyond this per-slot model:**

  * **RNS residue rows.**  `LeanCiphertext.rows[modulus][coeff]` stores each coefficient as three
    CRT residues mod the NTT-friendly moduli.  A slot `Ct.phase : ℤ` here models the
    CRT-RECONSTRUCTED coefficient; the reconstruction bijection `ℤ_q ≃ ∏ᵢ ℤ_{qᵢ}` and per-residue
    arithmetic-consistency (a forged single residue row is not representable in this model) are
    not formalized.
  * **mod-q wrap.**  Phases here live in ℤ; the machine reduces mod `q`.  Inherited mitigation,
    same as `Bfv.Noise` (`decryptPhase_add_q` + fold envelope), same NAMED residual.
  * **The ring/NTT encoding.**  "Slot" here = order index `j` with base-128 weight — exactly the
    `packedBook` packing the root commits.  Real SIMD slot-packing (`t ≡ 1 [MOD 8192]`) is an NTT
    over `ℤ_t`, a DIFFERENT bijective encoding; the negacyclic ring `X^n + 1`, coefficient mixing
    under multiplication (`Bfv.Mul`), and the equivalence of the two encodings are unformalized.
    This file's packing uses only public-LINEAR ops, where coefficient independence is exact.
  * **RLWE well-formedness.**  `BfvOpensTo` constrains the phase only.  That a row pair `(b, a)`
    is a genuine encryption under the collective key (`b = -a·s + Δm + e` with short randomness),
    which the in-circuit `SameOpeningGadget` must enforce, is beyond the phase model.
-/
import Market.DarkBazaarSameOpening

set_option autoImplicit false

namespace Market.DarkBazaarSameOpeningPoly

open Bfv Market.DarkBazaarPrivateDescriptor Market.DarkBazaarSameOpening

/-! ## 1. The per-slot relation over the real objects. -/

/-- Slot opening within an explicit noise budget: `ct`'s phase is `Δ·m + e` with `|e| ≤ B`.
This is the per-slot shape of the deployed fresh-noise contract (`B_fresh ≈ 2^20`). -/
def SlotOpensWithin (P : Params) (B : ℤ) (ct : Ct P) (m : ℤ) : Prop :=
  ∃ e : ℤ, |e| ≤ B ∧ ct.phase = (P.Δ : ℤ) * m + e

/-- **SAME-OPENING, per-slot (polynomial-model) lift.**  The four ciphertext rows of the deployed
receipt, as four slot ciphertexts `cts : Fin 4 → Ct P` (slot `j` = the encrypted coefficient
carrying order `j`):

  * every slot opens to the REAL `orderCode (w.orders j)` of the SAME witness `w`, within `B`;
  * `B` is inside the decrypt margin (`SafeNoise`), so each slot opening is a genuine
    `BfvOpensTo` (projection below), and
  * the root is the REAL `orderRoot` of the SAME `w` — whose preimage absorbs `packedBook w`,
    i.e. the root, not the ciphertext, carries the base-128 packing of exactly these slots.

The shared `w` across all five conjuncts is the entire point (RED below: break one slot and the
relation is false even though every component is independently valid). -/
def SameOpeningPoly (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int) (B : ℤ)
    (cts : Fin 4 → Ct P) (root : Fin 8 → Int) (w : PrivateWitness) : Prop :=
  SafeNoise P B ∧
  (∀ j : Fin 4, SlotOpensWithin P B (cts j) (orderCode (w.orders j))) ∧
  (∀ i, root i = orderRoot hash8 session w i)

/-- The margin is monotone: a smaller noise bound inherits `SafeNoise`. -/
theorem safeNoise_mono {P : Params} {B B' : ℤ} (h : B' ≤ B) (hs : SafeNoise P B) :
    SafeNoise P B' := by
  unfold SafeNoise at hs ⊢
  have ht : (0 : ℤ) ≤ 2 * (P.t : ℤ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h ht]

/-! ## 2. (a) Projection: each slot satisfies the scalar opening relation and decrypts exactly. -/

/-- **Per-slot projection to the scalar relation.**  `SameOpeningPoly` gives, at EVERY slot `j`,
the scalar `BfvOpensTo` of `DarkBazaarSameOpening` at that slot's real order code — together with
the root conjunct these are exactly the scalar relation's two conjuncts, slot-indexed. -/
theorem slot_projection {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ}
    {cts : Fin 4 → Ct P} {root : Fin 8 → Int} {w : PrivateWitness}
    (h : SameOpeningPoly P hash8 session B cts root w) (j : Fin 4) :
    BfvOpensTo P (cts j) (orderCode (w.orders j)) ∧ (∀ i, root i = orderRoot hash8 session w i) := by
  obtain ⟨hB, hslots, hroot⟩ := h
  obtain ⟨e, heB, hp⟩ := hslots j
  exact ⟨⟨e, safeNoise_mono heB hB, hp⟩, hroot⟩

/-- The order code as a natural (the plaintext the slot carries): `kind + 8·qty < 128`. -/
def natCode (o : PrivateOrder) : ℕ := o.kind.val + 8 * o.qty.val

theorem natCode_cast (o : PrivateOrder) : (natCode o : ℤ) = orderCode o := by
  simp [natCode, orderCode]

theorem natCode_lt (o : PrivateOrder) : natCode o < 128 := by
  have hk := o.kind.isLt
  have hq := o.qty.isLt
  simp only [natCode]
  omega

/-- **Per-slot exact decryption** — the `Bfv.decrypt_exact` keystone applied at every slot: under
`SameOpeningPoly`, slot `j` decrypts to EXACTLY `orderCode (w.orders j)` whenever the 7-bit code
window fits the plaintext modulus (deployed: `128 ≤ t = 1032193`, pinned below).  No slot can be a
silently-different order. -/
theorem slot_decrypts_exact {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ}
    {cts : Fin 4 → Ct P} {root : Fin 8 → Int} {w : PrivateWitness}
    (h : SameOpeningPoly P hash8 session B cts root w) (ht : 128 ≤ P.t) (j : Fin 4) :
    (cts j).decrypt = orderCode (w.orders j) := by
  obtain ⟨⟨e, he, hp⟩, -⟩ := slot_projection h j
  have hm : natCode (w.orders j) < P.t := lt_of_lt_of_le (natCode_lt _) ht
  have hphase : (cts j).phase = (P.Δ : ℤ) * (natCode (w.orders j) : ℤ) + e := by
    rw [natCode_cast]; exact hp
  show decryptPhase P (cts j).phase = orderCode (w.orders j)
  rw [hphase, decrypt_exact P (natCode (w.orders j)) e hm he, natCode_cast]

/-! ## 3. (a) The packing connection to the PROVED scalar apex relation. -/

/-- Homomorphic base-128 recombination of the four slots: public-scalar-muls plus adds — the exact
op set of the fold path (`Bfv.Ct.add` / `matVecCt` row) — evaluating the `packedBook` packing on
ciphertexts. -/
def packCt (P : Params) (cts : Fin 4 → Ct P) : Ct P :=
  ⟨(cts 0).phase + 128 * (cts 1).phase + 16384 * (cts 2).phase + 2097152 * (cts 3).phase⟩

/-- The exact noise gain of the base-128 recombination: `1 + 128 + 128² + 128³`. -/
def PACK_GAIN : ℤ := 2113665

theorem PACK_GAIN_eq : PACK_GAIN = 1 + 128 + 16384 + 2097152 := by decide

/-- `packedBook` as the explicit four-term base-128 sum (the same expansion the descriptor's
injectivity proof uses). -/
theorem packedBook_expand (w : PrivateWitness) :
    packedBook w =
      orderCode (w.orders 0) + 128 * orderCode (w.orders 1) +
        16384 * orderCode (w.orders 2) + 2097152 * orderCode (w.orders 3) := by
  simp [packedBook, List.ofFn_succ, add_assoc]

/-- **The lift MEETS the scalar apex (theorem (a), packing side):** if `SameOpeningPoly` holds and
the recombination headroom `PACK_GAIN·B` is inside the margin, then the packed carrier satisfies
the PROVED scalar relation `SameOpening` at the same `w` — same root, same witness, noise tracked
exactly (`e = e₀ + 128·e₁ + 128²·e₂ + 128³·e₃`).  So the per-slot model is a refinement of the
scalar apex relation, not a parallel construction. -/
theorem sameOpeningPoly_packs_to_sameOpening {P : Params} {hash8 : List Int → Fin 8 → Int}
    {session : Int} {B : ℤ} {cts : Fin 4 → Ct P} {root : Fin 8 → Int} {w : PrivateWitness}
    (h : SameOpeningPoly P hash8 session B cts root w)
    (hgain : SafeNoise P (PACK_GAIN * B)) :
    SameOpening P hash8 session (packCt P cts) root w := by
  obtain ⟨hB, hslots, hroot⟩ := h
  obtain ⟨e0, he0, hp0⟩ := hslots 0
  obtain ⟨e1, he1, hp1⟩ := hslots 1
  obtain ⟨e2, he2, hp2⟩ := hslots 2
  obtain ⟨e3, he3, hp3⟩ := hslots 3
  refine ⟨⟨e0 + 128 * e1 + 16384 * e2 + 2097152 * e3, ?_, ?_⟩, hroot⟩
  · -- the recombined noise is inside the margin: |Σ 128^j·e_j| ≤ PACK_GAIN·B, then monotonicity
    have habs : |e0 + 128 * e1 + 16384 * e2 + 2097152 * e3| ≤ PACK_GAIN * B := by
      have t1 : |e0 + 128 * e1 + 16384 * e2 + 2097152 * e3|
          ≤ |e0 + 128 * e1 + 16384 * e2| + |2097152 * e3| := abs_add_le _ _
      have t2 : |e0 + 128 * e1 + 16384 * e2| ≤ |e0 + 128 * e1| + |16384 * e2| := abs_add_le _ _
      have t3 : |e0 + 128 * e1| ≤ |e0| + |128 * e1| := abs_add_le _ _
      have m1 : |(128 : ℤ) * e1| = 128 * |e1| := by rw [abs_mul]; norm_num
      have m2 : |(16384 : ℤ) * e2| = 16384 * |e2| := by rw [abs_mul]; norm_num
      have m3 : |(2097152 : ℤ) * e3| = 2097152 * |e3| := by rw [abs_mul]; norm_num
      rw [PACK_GAIN_eq]
      have w1 : 128 * |e1| ≤ 128 * B := by linarith
      have w2 : 16384 * |e2| ≤ 16384 * B := by linarith
      have w3 : 2097152 * |e3| ≤ 2097152 * B := by linarith
      linarith [t1, t2, t3, m1 ▸ w1, m2 ▸ w2, m3 ▸ w3, he0]
    exact safeNoise_mono habs hgain
  · -- exact phase algebra: the packed phase is Δ·packedBook w + Σ 128^j·e_j
    show (packCt P cts).phase = _
    rw [packedBook_expand]
    simp only [packCt, hp0, hp1, hp2, hp3]
    ring

/-! ## 4. RED — a wrong slot breaks the lift (the scalar RED, per slot). -/

/-- **RED (required failing side): slot `j` encrypting a WRONG order breaks `SameOpeningPoly`.**
Exactly the scalar apex RED, lifted per slot: the slot-`j` ciphertext exactly encrypting a
different order `o'` is INDEPENDENTLY a valid slot ciphertext (`BfvOpensTo` at `o'`, zero noise),
and the root of the intended `w` is trivially the root of `w` — yet the conjunction is FALSE for
ANY budget `B`, because membership would force slot noise `e = Δ·(code o' − code (w.orders j))`,
and `delta_diff_unsafe` proves `Δ` times a nonzero code difference is NEVER inside the margin.
So per-slot binding is genuinely required; four independently-valid rows do not give it. -/
theorem wrong_slot_breaks_sameOpeningPoly
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ} {w : PrivateWitness}
    (j : Fin 4) (o' : PrivateOrder)
    (hne : orderCode o' ≠ orderCode (w.orders j))
    (hΔ : (0 : ℤ) ≤ (P.Δ : ℤ)) (ht1 : (1 : ℤ) ≤ (P.t : ℤ)) (hr : (0 : ℤ) ≤ (P.r : ℤ))
    (hq : (P.q : ℤ) ≤ 2 * (P.t : ℤ) * (P.Δ : ℤ))
    (hpos : SafeNoise P (0 : ℤ))
    (cts : Fin 4 → Ct P)
    (hj : cts j = ⟨(P.Δ : ℤ) * orderCode o'⟩) :
    BfvOpensTo P (cts j) (orderCode o')
      ∧ (∀ i, (orderRoot hash8 session w) i = orderRoot hash8 session w i)
      ∧ ¬ SameOpeningPoly P hash8 session B cts (orderRoot hash8 session w) w := by
  refine ⟨⟨0, by simpa using hpos, by simp [hj]⟩, fun _ => rfl, ?_⟩
  rintro ⟨hB, hslots, -⟩
  obtain ⟨e, heB, hp⟩ := hslots j
  rw [hj] at hp
  -- hp : Δ·(code o') = Δ·(code (w.orders j)) + e  ⇒  e = Δ·d with d ≠ 0
  have hp' : (P.Δ : ℤ) * orderCode o' = (P.Δ : ℤ) * orderCode (w.orders j) + e := hp
  have hde : e = (P.Δ : ℤ) * (orderCode o' - orderCode (w.orders j)) := by
    linear_combination -hp'
  have hd : orderCode o' - orderCode (w.orders j) ≠ 0 := sub_ne_zero.mpr hne
  exact delta_diff_unsafe hd hΔ ht1 hr hq (hde ▸ safeNoise_mono heB hB)

/-- **RED, packed: the single-slot forgery survives recombination.**  Take the four slots to be
EXACT encryptions of `w`'s orders except slot `j`, which exactly encrypts the wrong order `o'`.
The recombined carrier then fails the scalar `SameOpening` at `w` as well — the forced noise is
`Δ·128^j·d`, and `128^j·d ≠ 0` feeds the same `delta_diff_unsafe` bite.  The per-slot RED and the
scalar RED are the same gap at two resolutions; packing cannot launder a wrong slot. -/
theorem wrong_slot_breaks_packed_sameOpening
    {P : Params} {w : PrivateWitness}
    (j : Fin 4) (o' : PrivateOrder)
    (hne : orderCode o' ≠ orderCode (w.orders j))
    (hΔ : (0 : ℤ) ≤ (P.Δ : ℤ)) (ht1 : (1 : ℤ) ≤ (P.t : ℤ)) (hr : (0 : ℤ) ≤ (P.r : ℤ))
    (hq : (P.q : ℤ) ≤ 2 * (P.t : ℤ) * (P.Δ : ℤ))
    (cts : Fin 4 → Ct P)
    (hj : cts j = ⟨(P.Δ : ℤ) * orderCode o'⟩)
    (hk : ∀ k : Fin 4, k ≠ j → cts k = ⟨(P.Δ : ℤ) * orderCode (w.orders k)⟩) :
    ¬ BfvOpensTo P (packCt P cts) (packedBook w) := by
  rintro ⟨e, he, hp⟩
  rw [packedBook_expand] at hp
  have hd : orderCode o' - orderCode (w.orders j) ≠ 0 := sub_ne_zero.mpr hne
  fin_cases j
  · have hj0 : cts 0 = (⟨(P.Δ : ℤ) * orderCode o'⟩ : Ct P) := hj
    have hd0 : orderCode o' - orderCode (w.orders 0) ≠ 0 := hd
    have h1 := hk 1 (by decide); have h2 := hk 2 (by decide); have h3 := hk 3 (by decide)
    simp only [packCt, hj0, h1, h2, h3] at hp
    have hde : e = (P.Δ : ℤ) * (1 * (orderCode o' - orderCode (w.orders 0))) := by
      linear_combination -hp
    exact delta_diff_unsafe (mul_ne_zero one_ne_zero hd0) hΔ ht1 hr hq (hde ▸ he)
  · have hj1 : cts 1 = (⟨(P.Δ : ℤ) * orderCode o'⟩ : Ct P) := hj
    have hd1 : orderCode o' - orderCode (w.orders 1) ≠ 0 := hd
    have h0 := hk 0 (by decide); have h2 := hk 2 (by decide); have h3 := hk 3 (by decide)
    simp only [packCt, hj1, h0, h2, h3] at hp
    have hde : e = (P.Δ : ℤ) * (128 * (orderCode o' - orderCode (w.orders 1))) := by
      linear_combination -hp
    exact delta_diff_unsafe (mul_ne_zero (by norm_num) hd1) hΔ ht1 hr hq (hde ▸ he)
  · have hj2 : cts 2 = (⟨(P.Δ : ℤ) * orderCode o'⟩ : Ct P) := hj
    have hd2 : orderCode o' - orderCode (w.orders 2) ≠ 0 := hd
    have h0 := hk 0 (by decide); have h1 := hk 1 (by decide); have h3 := hk 3 (by decide)
    simp only [packCt, hj2, h0, h1, h3] at hp
    have hde : e = (P.Δ : ℤ) * (16384 * (orderCode o' - orderCode (w.orders 2))) := by
      linear_combination -hp
    exact delta_diff_unsafe (mul_ne_zero (by norm_num) hd2) hΔ ht1 hr hq (hde ▸ he)
  · have hj3 : cts 3 = (⟨(P.Δ : ℤ) * orderCode o'⟩ : Ct P) := hj
    have hd3 : orderCode o' - orderCode (w.orders 3) ≠ 0 := hd
    have h0 := hk 0 (by decide); have h1 := hk 1 (by decide); have h2 := hk 2 (by decide)
    simp only [packCt, hj3, h0, h1, h2] at hp
    have hde : e = (P.Δ : ℤ) * (2097152 * (orderCode o' - orderCode (w.orders 3))) := by
      linear_combination -hp
    exact delta_diff_unsafe (mul_ne_zero (by norm_num) hd3) hΔ ht1 hr hq (hde ▸ he)

/-! ## 5. Deployed pins — the hypotheses are LIVE on the real fhe.rs degree-4096 numbers. -/

/-- Four slots of fresh `B = 2^20` noise recombine with margin to spare on the deployed set:
`SafeNoise fheRs4096 (PACK_GAIN · 2^20)` (~2^41 against a ~2^88 radius), kernel-checked.  The
packing theorem's headroom hypothesis is satisfiable in production, not vacuously strong. -/
theorem deployed_pack_headroom : SafeNoise fheRs4096 (PACK_GAIN * 2 ^ 20) := by
  unfold SafeNoise; decide

/-- The RED's parameter fact `q ≤ 2tΔ` HOLDS on the deployed set (kernel-checked on the 109-bit
`q`): the per-slot and packed failing sides bite the real parameters, not a hypothetical set. -/
theorem deployed_q_le_two_t_delta :
    (fheRs4096.q : ℤ) ≤ 2 * (fheRs4096.t : ℤ) * (fheRs4096.Δ : ℤ) := by decide

/-- The 7-bit order-code window fits the deployed plaintext modulus (`128 ≤ t = 1032193`), so
`slot_decrypts_exact` applies to every deployed slot. -/
theorem deployed_code_window : 128 ≤ fheRs4096.t := by decide

#assert_all_clean [Market.DarkBazaarSameOpeningPoly.slot_projection,
  Market.DarkBazaarSameOpeningPoly.slot_decrypts_exact,
  Market.DarkBazaarSameOpeningPoly.sameOpeningPoly_packs_to_sameOpening,
  Market.DarkBazaarSameOpeningPoly.wrong_slot_breaks_sameOpeningPoly,
  Market.DarkBazaarSameOpeningPoly.wrong_slot_breaks_packed_sameOpening,
  Market.DarkBazaarSameOpeningPoly.deployed_pack_headroom,
  Market.DarkBazaarSameOpeningPoly.deployed_q_le_two_t_delta,
  Market.DarkBazaarSameOpeningPoly.deployed_code_window]

end Market.DarkBazaarSameOpeningPoly
