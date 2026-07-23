import Dregg2.Tactics
import Bfv.Noise
import Market.DarkBazaarPrivateDescriptor

/-!
# The Tier-0 apex, stated as a theorem: BFV-ciphertext ↔ private-root SAME-OPENING

The composite Dark Bazaar receipt (`Market.DarkBazaarAttestation`) binds a `HidingFri` proof over a private
book `w` AND a BFV ciphertext digest — but **independently**.  Codex's RED
`output_only_attestation_does_not_bind_source` shows a receipt with only `(p*,V*)` cannot identify the source
book.  This file states the *deeper* gap named as the cryptographic apex
(`HANDOFF-FHEGG-CODEX-SWARM-RESULTS.md` §53): nothing proves the BFV ciphertext ENCRYPTS THE SAME opening `w`
that the private root commits to.  That relation is `SameOpening`.

**What is Tier-1 vs Tier-0.**  Tier-1 (built): a trace-builder who SEES the plaintext book `w` proves the
clearing over it (`HidingFriPcs`, so proof consumers learn nothing).  Tier-0 (the apex): the book only ever
existed as ciphertext, and the clearing is proven over it with NO ONE seeing `w`.  The missing link is
`SameOpening`: the ciphertext and the root must open to the SAME `w`.  Without it, an adversary encrypts book
`w'` while committing a proof about a different book `w`.

**Scope, honest.**  This is the SCALAR `Bfv` model (`Bfv.Ct` = phase `Δ·m + e`); the deployed ciphertext is
RNS-polynomial over slots.  The `SameOpeningGadget` residual (below) names the in-circuit construction that
would DISCHARGE `SameOpening` — a joint AIR proving the RLWE/decryption-consistency constraint and the
Poseidon2 root over one shared witness.  What is PROVED here: the relation, that it forces the ciphertext to
decrypt to exactly the committed book, and — the biting RED — that two independently-valid objects (a
ciphertext of a DIFFERENT book, a root of the intended book) violate it.  So the apex gap is a theorem, not
prose.
-/

namespace Market.DarkBazaarSameOpening

open Bfv Market.DarkBazaarPrivateDescriptor

/-- The **lattice opening**: `ct` is a valid BFV encryption of message `m` — its phase is `Δ·m + e` for a
noise `e` inside the decrypt margin.  This is the real `Bfv` scalar object, not a mirror. -/
def BfvOpensTo (P : Params) (ct : Ct P) (m : ℤ) : Prop :=
  ∃ e : ℤ, SafeNoise P |e| ∧ ct.phase = (P.Δ : ℤ) * m + e

/-- **SAME-OPENING** — the Tier-0 relation the composite receipt does NOT currently prove: the BFV
ciphertext opens to the packed book of `w`, AND the private root commits to the SAME `w`.  The shared `w` is
the whole point; two independent bindings do not give it (RED below). -/
def SameOpening (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int)
    (ct : Ct P) (root : Fin 8 → Int) (w : PrivateWitness) : Prop :=
  BfvOpensTo P ct (packedBook w) ∧ (∀ i, root i = orderRoot hash8 session w i)

/-- A consequence with teeth: if same-opening holds, the ciphertext's noise AT the committed book is safe,
so it decrypts to exactly `packedBook w` (via `Bfv.decrypt_exact` once `packedBook w` is a valid slot).  The
ciphertext cannot be a silently-different book. -/
theorem sameOpening_noise_safe {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int}
    {ct : Ct P} {root : Fin 8 → Int} {w : PrivateWitness}
    (h : SameOpening P hash8 session ct root w) :
    SafeNoise P |ct.noiseAtInt (packedBook w)| := by
  obtain ⟨⟨e, he, hp⟩, _⟩ := h
  have hn : ct.noiseAtInt (packedBook w) = e := by
    simp only [Ct.noiseAtInt, hp]; ring
  rw [hn]; exact he

/-- `Δ` times a NONZERO integer difference exceeds the decrypt margin, under the standard BFV parameter fact
`q ≤ 2·t·Δ` (which holds because `Δ = ⌊q/t⌋`, so `t·Δ` is within `t` of `q`).  This is what makes the RED a
real bite, not a hypothesis assuming its conclusion. -/
theorem delta_diff_unsafe {P : Params} {d : ℤ}
    (hd : d ≠ 0) (hΔ : (0 : ℤ) ≤ (P.Δ : ℤ)) (ht1 : (1 : ℤ) ≤ (P.t : ℤ)) (hr : (0 : ℤ) ≤ (P.r : ℤ))
    (hq : (P.q : ℤ) ≤ 2 * (P.t : ℤ) * (P.Δ : ℤ)) :
    ¬ SafeNoise P |(P.Δ : ℤ) * d| := by
  unfold SafeNoise
  have h1 : (1 : ℤ) ≤ |d| := by
    rcases lt_or_gt_of_ne hd with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have habs : |(P.Δ : ℤ) * d| = (P.Δ : ℤ) * |d| := by
    rw [abs_mul, abs_of_nonneg hΔ]
  have hge : (P.Δ : ℤ) ≤ |(P.Δ : ℤ) * d| := by
    rw [habs]; nlinarith [h1, hΔ]
  have key1 : 2 * (P.t : ℤ) * (P.Δ : ℤ) ≤ 2 * (P.t : ℤ) * |(P.Δ : ℤ) * d| :=
    mul_le_mul_of_nonneg_left hge (by linarith)
  have key2 : (0 : ℤ) ≤ 2 * ((P.t : ℤ) - 1) * (P.r : ℤ) :=
    mul_nonneg (by linarith) hr
  intro hsafe
  linarith [hsafe, key1, key2, hq]

/-- **RED — the apex gap is a THEOREM.**  Two DISTINCT books (`packedBook w ≠ packedBook w'`): the ciphertext
encrypting `w'` and the root committing `w` are each INDEPENDENTLY valid — exactly what the composite receipt
binds — yet `SameOpening … w` is FALSE.  So "ciphertext digest ∧ root" does NOT imply same-opening; the
`SameOpeningGadget` is genuinely required, not implied by the composition. -/
theorem independent_valid_objects_break_same_opening
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {w w' : PrivateWitness}
    (hne : packedBook w ≠ packedBook w')
    (hΔ : (0 : ℤ) ≤ (P.Δ : ℤ)) (ht1 : (1 : ℤ) ≤ (P.t : ℤ)) (hr : (0 : ℤ) ≤ (P.r : ℤ))
    (hq : (P.q : ℤ) ≤ 2 * (P.t : ℤ) * (P.Δ : ℤ))
    (hpos : SafeNoise P (0 : ℤ)) :
    BfvOpensTo P (⟨(P.Δ : ℤ) * packedBook w'⟩ : Ct P) (packedBook w')
      ∧ (∀ i, (orderRoot hash8 session w) i = orderRoot hash8 session w i)
      ∧ ¬ SameOpening P hash8 session (⟨(P.Δ : ℤ) * packedBook w'⟩ : Ct P)
            (orderRoot hash8 session w) w := by
  refine ⟨⟨0, by simpa using hpos, by simp⟩, fun _ => rfl, ?_⟩
  rintro ⟨⟨e, he, hp⟩, _⟩
  -- hp : Δ·packedBook w' = Δ·packedBook w + e  ⇒  e = Δ·(packedBook w' − packedBook w)
  have hdiff : e = (P.Δ : ℤ) * (packedBook w' - packedBook w) := by
    have : (P.Δ : ℤ) * packedBook w' = (P.Δ : ℤ) * packedBook w + e := hp
    ring_nf at this ⊢; linarith
  have hne' : packedBook w' - packedBook w ≠ 0 := by omega
  exact (delta_diff_unsafe hne' hΔ ht1 hr hq) (hdiff ▸ he)

/-! ## The named construction residual

`SameOpeningGadget` (Tier-0 apex, unbuilt): an in-circuit relation that DISCHARGES `SameOpening` by proving,
over ONE shared private witness `w`:
  1. the RLWE/decryption-consistency constraint — the deployed RNS-polynomial lift of `ct.phase = Δ·packedBook w + e`
     with `SafeNoise P |e|`, evaluated over the collective-key decryption shares (no single party holds `s`); and
  2. `orderRoot hash8 session w = root` — the existing Poseidon2 root gadget (`DarkBazaarPrivateDescriptor`).
Both must bind the SAME `packedBook w`.  Then followed by DISTRIBUTED witness production so no single prover
sees the full book.  Until that gadget exists, `SameOpening` is a required-but-unproved property, and the
receipt is honestly Tier-1, per the RED above.
-/

#assert_all_clean [Market.DarkBazaarSameOpening.sameOpening_noise_safe,
  Market.DarkBazaarSameOpening.delta_diff_unsafe,
  Market.DarkBazaarSameOpening.independent_valid_objects_break_same_opening]

end Market.DarkBazaarSameOpening
