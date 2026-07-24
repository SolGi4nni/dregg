/-
# Market.DarkBazaarCollectiveOpeningPoly — the COLLECTIVE opening lifted to the per-slot
# (RNS-polynomial model) ciphertext: the apex residual of FHEGG-SAME-OPENING-APEX.md §3.2/§3.3.

**What this file is for.**  `Market.DarkBazaarCollectiveOpening` proves the no-single-viewer
collective decrypt SOUND over ONE scalar phase (`CollectiveOpensTo`, `collective_decrypt_unique`).
`Market.DarkBazaarSameOpeningPoly` lifts the SAME-OPENING relation to the deployed per-slot shape
(4 ordered ciphertext rows, one per order slot).  The deployed system does BOTH at once: each of
the four slot ciphertexts is opened by the SUM of the n party partial-phases
(`fhegg-fhe/src/threshold.rs`: per ciphertext, `c0' = c0 + Σ hᵢ`), and no party ever assembles
`s = Σ sᵢ`.  This file joins the two proved layers:

  1. **`CollectiveOpensToPoly`** — the per-slot collective opening: every order slot's combined
     phase (public row + the sum of that slot's n party shares) is decrypt-consistent at that
     slot's REAL `orderCode (w.orders j)`, and the root is the REAL `orderRoot` of the SAME `w`.
     Defined THROUGH the proved scalar `CollectiveOpensTo` per slot (definitional bridge
     `collectivePoly_is_decryptConsistent`, an `Iff.rfl`) — one relation family, no drift.
  2. **`collective_poly_decrypt_unique`** — the requested keystone: one 4-slot collective
     transcript cannot open to two books.  Scalar collective uniqueness composed per slot through
     the injective 7-bit order code (`orderCode_injective`); `collective_poly_packedBook_unique`
     and `collective_poly_decrypts` (the REAL threshold.rs combine→decode path returns exactly
     each slot's order code).
  3. **The connection to `SameOpeningPoly`, BOTH directions** — the combined-phase ciphertexts of
     a collective poly opening satisfy `SameOpeningPoly` at some budget
     (`collectivePoly_to_sameOpeningPoly`), and any budgeted `SameOpeningPoly` over combined
     phases IS a collective poly opening (`sameOpeningPoly_to_collectivePoly`); chained with the
     proved packing lift, a budgeted collective transcript recombines to the PROVED scalar apex
     `SameOpening` (`collective_slots_pack_to_scalar_apex`).  Collective decrypt, per-slot lift,
     and scalar apex are one story.
  4. **FAILING SIDES (required), all proved:**
     * `wrong_slot_breaks_collectivePoly` — a slot whose collective combine exactly opens to a
       WRONG order is independently valid, the root of the intended `w` is independently valid,
       yet the relation is FALSE for the whole book (`delta_diff_unsafe` bite, any parameters
       with `q ≤ 2tΔ`).
     * `single_tampered_share_breaks_poly_opening` — ONE party shifting ONE slot's share by `Δ·k`
       retargets that slot and the WHOLE book relation refuses (combine is blind to share
       validity, now at the poly level).
     * `short_quorum_breaks_opening` / `short_quorum_breaks_collectivePoly` — a party DROPPED
       from the combine (share zeroed; witness family: its share carried `Δ·k`) makes the
       (n−1)-quorum open to the WRONG message and uniqueness REFUSES the true one — for the
       whole book if it happens in any single slot.  `deployed_short_quorum_red_inhabited`
       pins the hypothesis family inhabited on the deployed 16-party numbers (not vacuous).
  5. **Deployed pins** (`decide` on the real fhe.rs degree-4096 numbers): one slot's collective
     budget (fold envelope `2^32` + 16 smudges of `2^80`) fits the margin
     (`deployed_collective_slot_budget_safe`), and — the ORDER-OF-OPERATIONS boundary — the
     base-128 pack gain applied AFTER collective opening BLOWS the margin
     (`deployed_pack_after_smudge_blows_margin`): packing composes with the collective decrypt
     only on the ciphertext side (fresh noise, `deployed_pack_headroom`), never on
     already-smudged openings.

**Substrate, out loud:** this file is the Lean-authored relation layer.  The gadget/descriptor
that discharges it in-circuit is Lean-emitted (`EmitSameOpeningGadget` shape) — never a
hand-written Rust AIR.

**NAMED, not proved — what the full RNS/NTT representation and malicious shares ADD:**

  * **RNS residue rows.**  A slot phase here is the CRT-RECONSTRUCTED coefficient;
    `bfv_lean.rs::LeanCiphertext` stores three residue rows per coefficient.  The reconstruction
    bijection `ℤ_q ≃ ∏ᵢ ℤ_{qᵢ}`, per-residue arithmetic consistency, and a forged single residue
    row are not representable in this model (inherited from `DarkBazaarSameOpeningPoly` scope).
  * **mod-q wrap.**  ℤ phases, not mod-`q` — inherited `Bfv.Noise` mitigation
    (`decryptPhase_add_q` + fold envelope), same NAMED residual.
  * **NTT/SIMD slot encoding.**  "Slot" here = order index with base-128 weight (exactly the
    `packedBook` pack the root commits).  Real SIMD packing (`t ≡ 1 [MOD 8192]`) is an NTT over
    `ℤ_t`; the negacyclic ring and the equivalence of encodings are unformalized.  Only
    public-LINEAR ops are used here, where coefficient independence is exact.
  * **Collective-key RLWE well-formedness.**  That each slot's `(c0, c1)` is a genuine
    encryption under the collective key with short randomness is assumed (GREEN side only, via
    `HonestTranscript`'s `keyTerm` shape); the REDs and uniqueness do not depend on it.  Same
    residual the SameOpeningGadget names.
  * **Malicious shares (roadmap 3.2).**  The REDs PROVE combine is blind to share validity and
    to quorum completeness, per slot; the FIX — malicious-secure share-validity proofs
    (VSS / share same-opening, attributable refusal of a corrupt partial), and distributed
    witness production so no single prover reconstructs the book across the four slots — is the
    open frontier.  Nothing here authenticates a share or a quorum roster.
  * **Hiding at the poly level.**  Coalition hiding is the scalar `CoalitionViewHides` story
    applied per coefficient (`Bfv.Smudging`); 4-slot × n-party × transcript-wide composition is
    `Bfv.Smudging.TranscriptHybridLedger` — referenced, NOT discharged here.
-/
import Market.DarkBazaarDecryptConsistency
import Market.DarkBazaarSameOpeningPoly
import Market.DarkBazaarCollectiveOpening
import Dregg2.Tactics

namespace Market.DarkBazaarCollectiveOpeningPoly

open Bfv Market.DarkBazaarPrivateDescriptor
open Market.DarkBazaarDecryptConsistency Market.DarkBazaarSameOpening
open Market.DarkBazaarSameOpeningPoly Market.DarkBazaarCollectiveOpening

set_option autoImplicit false

/-! ## 1. The per-slot collective objects. -/

/-- Slot `j`'s combined ciphertext: that slot's public row plus the sum of its n party
partial-phases — the `threshold.rs` combine, per order slot, as a model `Ct`. -/
def combinedCt (P : Params) {n : ℕ} (c0s : Fin 4 → ℤ) (shares : Fin 4 → Fin n → ℤ)
    (j : Fin 4) : Ct P :=
  ⟨combinePhase (c0s j) (shares j)⟩

/-- **COLLECTIVE-OPENS-TO, per-slot (polynomial-model) lift.**  The four order slots of the
deployed receipt, each opened COLLECTIVELY: slot `j`'s combined phase is decrypt-consistent at
the REAL `orderCode (w.orders j)` of ONE shared witness `w`, and the root is the REAL
`orderRoot` of the SAME `w`.  Defined THROUGH the proved scalar `CollectiveOpensTo` per slot,
so the collective poly form cannot drift from the scalar collective form.  No slot's combine
ever assembles a secret; the shared `w` across all five conjuncts is the entire point. -/
def CollectiveOpensToPoly (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int)
    {n : ℕ} (c0s : Fin 4 → ℤ) (shares : Fin 4 → Fin n → ℤ)
    (root : Fin 8 → Int) (w : PrivateWitness) : Prop :=
  (∀ j : Fin 4, CollectiveOpensTo P (c0s j) (shares j) (orderCode (w.orders j))) ∧
  (∀ i, root i = orderRoot hash8 session w i)

/-- The collective poly relation IS the core `DecryptConsistent` relation at each slot's
combined phase (plus the root conjunct) — definitional, the no-drift bridge. -/
theorem collectivePoly_is_decryptConsistent (P : Params) (hash8 : List Int → Fin 8 → Int)
    (session : Int) {n : ℕ} (c0s : Fin 4 → ℤ) (shares : Fin 4 → Fin n → ℤ)
    (root : Fin 8 → Int) (w : PrivateWitness) :
    CollectiveOpensToPoly P hash8 session c0s shares root w ↔
      ((∀ j : Fin 4, DecryptConsistent P (combinePhase (c0s j) (shares j))
          (orderCode (w.orders j))) ∧
       (∀ i, root i = orderRoot hash8 session w i)) :=
  Iff.rfl

/-! ## 2. THE KEYSTONE — one 4-slot collective transcript, one book. -/

/-- **`collective_poly_decrypt_unique`** — the per-slot collective decryption still uniquely
determines the BOOK: two witnesses opened by the SAME per-slot collective transcripts have the
same orders.  Scalar `collective_decrypt_unique` composed per slot, then the injective 7-bit
order code.  The n-of-n split and the 4-slot split together cost NOTHING in decrypt
soundness. -/
theorem collective_poly_decrypt_unique {P : Params} {hash8 : List Int → Fin 8 → Int}
    {session : Int} {n : ℕ} {c0s : Fin 4 → ℤ} {shares : Fin 4 → Fin n → ℤ}
    {root root₂ : Fin 8 → Int} {w w₂ : PrivateWitness}
    (h : CollectiveOpensToPoly P hash8 session c0s shares root w)
    (h₂ : CollectiveOpensToPoly P hash8 session c0s shares root₂ w₂) :
    w.orders = w₂.orders := by
  funext j
  exact orderCode_injective (collective_decrypt_unique (h.1 j) (h₂.1 j))

/-- One 4-slot collective transcript, one PACKED book — the packed-carrier corollary
(`packedBook` depends only on the orders). -/
theorem collective_poly_packedBook_unique {P : Params} {hash8 : List Int → Fin 8 → Int}
    {session : Int} {n : ℕ} {c0s : Fin 4 → ℤ} {shares : Fin 4 → Fin n → ℤ}
    {root root₂ : Fin 8 → Int} {w w₂ : PrivateWitness}
    (h : CollectiveOpensToPoly P hash8 session c0s shares root w)
    (h₂ : CollectiveOpensToPoly P hash8 session c0s shares root₂ w₂) :
    packedBook w = packedBook w₂ := by
  have horders := collective_poly_decrypt_unique h h₂
  simp only [packedBook, horders]

/-- **Per-slot collective decryption is EXACT**: under `CollectiveOpensToPoly`, the REAL decoder
on slot `j`'s combined phase (the threshold.rs combine→scale→round path) returns exactly
`orderCode (w.orders j)`, whenever the 7-bit code window fits `t` (deployed: `128 ≤ t`,
`deployed_code_window`).  No slot of the collectively-opened book can be silently different. -/
theorem collective_poly_decrypts {P : Params} {hash8 : List Int → Fin 8 → Int}
    {session : Int} {n : ℕ} {c0s : Fin 4 → ℤ} {shares : Fin 4 → Fin n → ℤ}
    {root : Fin 8 → Int} {w : PrivateWitness}
    (h : CollectiveOpensToPoly P hash8 session c0s shares root w)
    (ht : 128 ≤ P.t) (j : Fin 4) :
    decryptPhase P (combinePhase (c0s j) (shares j)) = orderCode (w.orders j) := by
  have hm : natCode (w.orders j) < P.t := lt_of_lt_of_le (natCode_lt _) ht
  have hc : CollectiveOpensTo P (c0s j) (shares j) ((natCode (w.orders j) : ℤ)) := by
    rw [natCode_cast]; exact h.1 j
  have hd := collective_decrypts (natCode (w.orders j)) hm hc
  rw [hd, natCode_cast]

/-! ## 3. GREEN — honest per-slot n-party transcripts open, and decrypt, on the deployed
numbers. -/

/-- GREEN (non-vacuity): four honest n-party transcripts — slot `j` carrying exactly
`natCode (w.orders j)` — satisfy `CollectiveOpensToPoly` whenever each slot's total noise
(fold noise + all smudges) is inside the margin. -/
theorem honest_poly_collective_opens {P : Params} (hash8 : List Int → Fin 8 → Int)
    (session : Int) {n : ℕ} (ts : Fin 4 → HonestTranscript P n) (w : PrivateWitness)
    (hmsg : ∀ j, (ts j).m = natCode (w.orders j))
    (hsafe : ∀ j, SafeNoise P |(ts j).eCt + ∑ i, (ts j).smudge i|) :
    CollectiveOpensToPoly P hash8 session (fun j => (ts j).c0) (fun j => (ts j).share)
      (orderRoot hash8 session w) w := by
  refine ⟨fun j => ?_, fun _ => rfl⟩
  show CollectiveOpensTo P (ts j).c0 (ts j).share (orderCode (w.orders j))
  have h0 := honest_collective_opens (ts j) (hsafe j)
  rw [hmsg j] at h0
  rwa [natCode_cast] at h0

/-- **Deployed GREEN pin (opens)**: 16 parties per slot on the real fhe.rs degree-4096 numbers —
per-slot fold noise inside `2^32`, every smudge inside `2^80` — satisfy the full
`CollectiveOpensToPoly`.  Per-slot instantiation of `deployed_honest_collective_opens` (whose
margin fact is kernel-checked on the 109-bit `q`). -/
theorem deployed_honest_poly_collective_opens (hash8 : List Int → Fin 8 → Int) (session : Int)
    (ts : Fin 4 → HonestTranscript fheRs4096 16) (w : PrivateWitness)
    (hmsg : ∀ j, (ts j).m = natCode (w.orders j))
    (he : ∀ j, |(ts j).eCt| ≤ 2 ^ 32) (hu : ∀ j i, |(ts j).smudge i| ≤ 2 ^ 80) :
    CollectiveOpensToPoly fheRs4096 hash8 session
      (fun j => (ts j).c0) (fun j => (ts j).share) (orderRoot hash8 session w) w := by
  refine ⟨fun j => ?_, fun _ => rfl⟩
  show CollectiveOpensTo fheRs4096 (ts j).c0 (ts j).share (orderCode (w.orders j))
  have h0 := deployed_honest_collective_opens (ts j) (he j) (hu j)
  rw [hmsg j] at h0
  rwa [natCode_cast] at h0

/-- **Deployed GREEN pin (decrypts)**: the same deployed honest 4×16 transcript DECRYPTS, slot
by slot, to exactly the committed orders through the real decoder — hiding-level smudge
(`2^80` per party) and exact per-slot collective decryption live simultaneously. -/
theorem deployed_honest_poly_collective_decrypts
    (ts : Fin 4 → HonestTranscript fheRs4096 16) (w : PrivateWitness)
    (hmsg : ∀ j, (ts j).m = natCode (w.orders j))
    (he : ∀ j, |(ts j).eCt| ≤ 2 ^ 32) (hu : ∀ j i, |(ts j).smudge i| ≤ 2 ^ 80) (j : Fin 4) :
    decryptPhase fheRs4096 (combinePhase (ts j).c0 (ts j).share) = orderCode (w.orders j) := by
  have hm : (ts j).m < fheRs4096.t := by
    rw [hmsg j]; exact lt_of_lt_of_le (natCode_lt _) deployed_code_window
  have hd := deployed_honest_collective_decrypts (ts j) hm (he j) (hu j)
  rw [hd, hmsg j, natCode_cast]

/-! ## 4. The connection to `SameOpeningPoly` — both directions, and through to the scalar
apex. -/

/-- **Collective → poly relation**: the combined-phase ciphertexts of a collective poly opening
satisfy `SameOpeningPoly` at SOME noise budget (the max of the four slot noises — itself inside
the margin, since it IS one of them).  The collective lift lands exactly in the proved per-slot
relation family. -/
theorem collectivePoly_to_sameOpeningPoly {P : Params} {hash8 : List Int → Fin 8 → Int}
    {session : Int} {n : ℕ} {c0s : Fin 4 → ℤ} {shares : Fin 4 → Fin n → ℤ}
    {root : Fin 8 → Int} {w : PrivateWitness}
    (h : CollectiveOpensToPoly P hash8 session c0s shares root w) :
    ∃ B : ℤ, SameOpeningPoly P hash8 session B (combinedCt P c0s shares) root w := by
  obtain ⟨hslots, hroot⟩ := h
  have hex : ∀ j : Fin 4, ∃ e : ℤ, SafeNoise P |e| ∧
      combinePhase (c0s j) (shares j) = (P.Δ : ℤ) * orderCode (w.orders j) + e := hslots
  choose e hsafe hphase using hex
  refine ⟨max (max |e 0| |e 1|) (max |e 2| |e 3|), ?_, fun j => ⟨e j, ?_, hphase j⟩, hroot⟩
  · rcases max_choice (max |e 0| |e 1|) (max |e 2| |e 3|) with h4 | h4 <;> rw [h4]
    · rcases max_choice |e 0| |e 1| with h2 | h2 <;> rw [h2]
      · exact hsafe 0
      · exact hsafe 1
    · rcases max_choice |e 2| |e 3| with h2 | h2 <;> rw [h2]
      · exact hsafe 2
      · exact hsafe 3
  · fin_cases j
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_right _ _)

/-- **Poly relation → collective**: any budgeted `SameOpeningPoly` over the combined phases IS a
collective poly opening (`|e| ≤ B` + `SafeNoise P B` gives `SafeNoise P |e|` by monotonicity).
With the previous theorem: the collective per-slot form is a refinement of the proved per-slot
relation, not a parallel construction. -/
theorem sameOpeningPoly_to_collectivePoly {P : Params} {hash8 : List Int → Fin 8 → Int}
    {session : Int} {n : ℕ} {B : ℤ} {c0s : Fin 4 → ℤ} {shares : Fin 4 → Fin n → ℤ}
    {root : Fin 8 → Int} {w : PrivateWitness}
    (h : SameOpeningPoly P hash8 session B (combinedCt P c0s shares) root w) :
    CollectiveOpensToPoly P hash8 session c0s shares root w := by
  obtain ⟨hB, hslots, hroot⟩ := h
  refine ⟨fun j => ?_, hroot⟩
  obtain ⟨e, heB, hp⟩ := hslots j
  exact ⟨e, safeNoise_mono heB hB, hp⟩

/-- **The full chain, consolidated**: one budgeted per-slot collective transcript is
simultaneously (i) a collective poly opening and (ii) — through the proved packing lift, under
the exact pack headroom — a witness of the PROVED scalar apex `SameOpening` on the recombined
carrier.  Collective shares → per-slot poly → packed scalar apex, one relation family. -/
theorem collective_slots_pack_to_scalar_apex {P : Params} {hash8 : List Int → Fin 8 → Int}
    {session : Int} {n : ℕ} {B : ℤ} {c0s : Fin 4 → ℤ} {shares : Fin 4 → Fin n → ℤ}
    {root : Fin 8 → Int} {w : PrivateWitness}
    (h : SameOpeningPoly P hash8 session B (combinedCt P c0s shares) root w)
    (hgain : SafeNoise P (PACK_GAIN * B)) :
    CollectiveOpensToPoly P hash8 session c0s shares root w
      ∧ SameOpening P hash8 session (packCt P (combinedCt P c0s shares)) root w :=
  ⟨sameOpeningPoly_to_collectivePoly h, sameOpeningPoly_packs_to_sameOpening h hgain⟩

/-- **Deployed pin**: ONE slot's collective noise budget — the `2^32` fold envelope plus 16
parties' `2^80` smudges — is inside the deployed margin (kernel-checked on the 109-bit `q`).
The budget every deployed GREEN above spends from. -/
theorem deployed_collective_slot_budget_safe :
    SafeNoise fheRs4096 (2 ^ 32 + 16 * 2 ^ 80) := by
  unfold SafeNoise; decide

/-- **Deployed pin — the ORDER-OF-OPERATIONS boundary (a real deployment fact, kernel-checked):
the base-128 pack gain applied AFTER collective opening BLOWS the margin.**  `PACK_GAIN` times
the smudged per-slot collective budget is provably UNSAFE on the deployed numbers — so
`collective_slots_pack_to_scalar_apex`'s headroom hypothesis is NOT satisfiable at post-smudge
noise levels.  Packing composes with the collective decrypt only on the ciphertext side (fresh
per-slot noise: `deployed_pack_headroom`, `PACK_GAIN·2^20` safe), never by recombining
already-smudged openings.  The smudge that buys hiding spends exactly the headroom the pack
would need. -/
theorem deployed_pack_after_smudge_blows_margin :
    ¬ SafeNoise fheRs4096 (PACK_GAIN * (2 ^ 32 + 16 * 2 ^ 80)) := by
  unfold SafeNoise; decide

/-! ## 5. RED — the required failing sides: a wrong slot, a tampered share, a short quorum. -/

/-- **RED (wrong slot): a slot whose collective combine opens to a WRONG order breaks the whole
book relation.**  Slot `j`'s combined phase exactly `Δ·orderCode o'` (`o' ≠ w.orders j`) is
INDEPENDENTLY a valid collective opening of `o'` (zero residual noise), and the root of the
intended `w` is independently valid — yet `CollectiveOpensToPoly … w` is FALSE: membership would
force slot noise `Δ·(code o' − code (w.orders j))`, never inside the margin
(`delta_diff_unsafe`).  Four independently-valid collective rows do not bind a book. -/
theorem wrong_slot_breaks_collectivePoly
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {n : ℕ}
    {w : PrivateWitness} (j : Fin 4) (o' : PrivateOrder)
    (hne : orderCode o' ≠ orderCode (w.orders j))
    (hΔ : (0 : ℤ) ≤ (P.Δ : ℤ)) (ht1 : (1 : ℤ) ≤ (P.t : ℤ)) (hr : (0 : ℤ) ≤ (P.r : ℤ))
    (hq : (P.q : ℤ) ≤ 2 * (P.t : ℤ) * (P.Δ : ℤ))
    (hpos : SafeNoise P (0 : ℤ))
    (c0s : Fin 4 → ℤ) (shares : Fin 4 → Fin n → ℤ)
    (hj : combinePhase (c0s j) (shares j) = (P.Δ : ℤ) * orderCode o') :
    CollectiveOpensTo P (c0s j) (shares j) (orderCode o')
      ∧ (∀ i, (orderRoot hash8 session w) i = orderRoot hash8 session w i)
      ∧ ¬ CollectiveOpensToPoly P hash8 session c0s shares (orderRoot hash8 session w) w := by
  refine ⟨⟨0, by simpa using hpos, by rw [hj]; ring⟩, fun _ => rfl, ?_⟩
  rintro ⟨hslots, -⟩
  obtain ⟨e, he, hp⟩ := hslots j
  rw [hj] at hp
  have hde : e = (P.Δ : ℤ) * (orderCode o' - orderCode (w.orders j)) := by
    linear_combination -hp
  exact delta_diff_unsafe (sub_ne_zero.mpr hne) hΔ ht1 hr hq (hde ▸ he)

/-- One slot's share function tampered at one party; every other slot untouched. -/
def tamperSlot {n : ℕ} (shares : Fin 4 → Fin n → ℤ) (j : Fin 4) (i₀ : Fin n) (δ : ℤ) :
    Fin 4 → Fin n → ℤ :=
  fun j' => if j' = j then tamperedShares (shares j) i₀ δ else shares j'

/-- **RED (tampered share, poly): ONE party shifting ONE slot's share by `Δ·k` breaks the WHOLE
book relation.**  The tampered slot collectively opens to `code + k` (same noise), and
uniqueness then refuses the true code — so `CollectiveOpensToPoly` at `w` is FALSE for the whole
transcript.  Combine is blind to share validity at the poly level too; malicious-share validity
(roadmap 3.2) is an open obligation as a theorem, per slot. -/
theorem single_tampered_share_breaks_poly_opening
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {n : ℕ}
    {c0s : Fin 4 → ℤ} {shares : Fin 4 → Fin n → ℤ} {root : Fin 8 → Int} {w : PrivateWitness}
    (h : CollectiveOpensToPoly P hash8 session c0s shares root w)
    (j : Fin 4) (i₀ : Fin n) (k : ℤ) (hk : k ≠ 0) :
    CollectiveOpensTo P (c0s j) (tamperedShares (shares j) i₀ ((P.Δ : ℤ) * k))
        (orderCode (w.orders j) + k)
      ∧ ¬ CollectiveOpensToPoly P hash8 session c0s
            (tamperSlot shares j i₀ ((P.Δ : ℤ) * k)) root w := by
  have hpair := single_tampered_share_breaks_opening i₀ k hk (h.1 j)
  refine ⟨hpair.1, ?_⟩
  rintro ⟨hslots', -⟩
  have hj : CollectiveOpensTo P (c0s j) (tamperedShares (shares j) i₀ ((P.Δ : ℤ) * k))
      (orderCode (w.orders j)) := by
    simpa [tamperSlot] using hslots' j
  exact hpair.2 hj

/-- Party `i₀` absent from the combine: its share zeroed — the (n−1)-quorum sum over the same
wire shape.  (Definitionally `tamperedShares shares i₀ (−shares i₀)`.) -/
def absentPartyShares {n : ℕ} (shares : Fin n → ℤ) (i₀ : Fin n) : Fin n → ℤ :=
  tamperedShares shares i₀ (-(shares i₀))

/-- The absent party contributes literally nothing to the combine. -/
theorem absentParty_share_zero {n : ℕ} (shares : Fin n → ℤ) (i₀ : Fin n) :
    absentPartyShares shares i₀ i₀ = 0 := by
  simp [absentPartyShares, tamperedShares]

/-- The (n−1)-quorum combine misses exactly the absent party's share. -/
theorem absent_combine {n : ℕ} (c0 : ℤ) (shares : Fin n → ℤ) (i₀ : Fin n) :
    combinePhase c0 (absentPartyShares shares i₀) = combinePhase c0 shares - shares i₀ := by
  unfold absentPartyShares
  rw [tampered_combine]; ring

/-- **RED (short quorum, scalar): dropping ONE party breaks the collective opening** — witness
family: the absent party's share carried `Δ·k` (`k ≠ 0`; realizable, `keyTerm` is
unconstrained).  The (n−1)-quorum opens to `m − k` with the same noise, and uniqueness REFUSES
`m`.  All n shares are load-bearing; there is no silent quorum degradation. -/
theorem short_quorum_breaks_opening {P : Params} {n : ℕ} {c0 : ℤ} {shares : Fin n → ℤ}
    {m : ℤ} (i₀ : Fin n) (k : ℤ) (hk : k ≠ 0) (hshare : shares i₀ = (P.Δ : ℤ) * k)
    (h : CollectiveOpensTo P c0 shares m) :
    CollectiveOpensTo P c0 (absentPartyShares shares i₀) (m - k)
      ∧ ¬ CollectiveOpensTo P c0 (absentPartyShares shares i₀) m := by
  have hneg : (P.Δ : ℤ) * -k = -(shares i₀) := by rw [hshare]; ring
  have hpair := single_tampered_share_breaks_opening i₀ (-k) (neg_ne_zero.mpr hk) h
  rw [hneg] at hpair
  refine ⟨?_, hpair.2⟩
  have h1 := hpair.1
  rwa [← sub_eq_add_neg] at h1

/-- One slot's combine run short one party; every other slot untouched. -/
def absentPartySlot {n : ℕ} (shares : Fin 4 → Fin n → ℤ) (j : Fin 4) (i₀ : Fin n) :
    Fin 4 → Fin n → ℤ :=
  fun j' => if j' = j then absentPartyShares (shares j) i₀ else shares j'

/-- **RED (short quorum, poly): one party dropped from ONE slot's combine refuses the WHOLE
book.**  If the full transcript opens to `w` and slot `j`'s party `i₀` carried `Δ·k`, the
transcript with that one slot run as an (n−1)-quorum provably does NOT satisfy
`CollectiveOpensToPoly` at `w`.  Quorum completeness is per-slot load-bearing. -/
theorem short_quorum_breaks_collectivePoly
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {n : ℕ}
    {c0s : Fin 4 → ℤ} {shares : Fin 4 → Fin n → ℤ} {root : Fin 8 → Int} {w : PrivateWitness}
    (h : CollectiveOpensToPoly P hash8 session c0s shares root w)
    (j : Fin 4) (i₀ : Fin n) (k : ℤ) (hk : k ≠ 0)
    (hshare : shares j i₀ = (P.Δ : ℤ) * k) :
    ¬ CollectiveOpensToPoly P hash8 session c0s (absentPartySlot shares j i₀) root w := by
  rintro ⟨hslots', -⟩
  have hj : CollectiveOpensTo P (c0s j) (absentPartyShares (shares j) i₀)
      (orderCode (w.orders j)) := by
    simpa [absentPartySlot] using hslots' j
  exact (short_quorum_breaks_opening i₀ k hk hshare (h.1 j)).2 hj

/-- The short-quorum RED's inhabitation transcript: slot `j` carries `w`'s order `j` exactly,
party 0's key term is `Δ·k`, all other noise zero.  (`keyTerm` models `sᵢ·c1`, unconstrained in
the phase model, so this is a legitimate honest-shape transcript.) -/
def shortQuorumFixture (P : Params) (w : PrivateWitness) (k : ℤ) (j : Fin 4) :
    HonestTranscript P 16 where
  m := natCode (w.orders j)
  eCt := 0
  keyTerm := fun i => if i = 0 then (P.Δ : ℤ) * k else 0
  smudge := fun _ => 0

/-- **The short-quorum RED bites a REAL deployed transcript (non-vacuity)**: on the deployed
16-party numbers there is a transcript that satisfies `CollectiveOpensToPoly` at `w` AND whose
slot-0 party-0 share is exactly `Δ·k` — so `short_quorum_breaks_collectivePoly`'s hypothesis
family is inhabited, and the RED is a fact about live transcripts, not a vacuous implication. -/
theorem deployed_short_quorum_red_inhabited (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) (k : ℤ) :
    ∃ (c0s : Fin 4 → ℤ) (shares : Fin 4 → Fin 16 → ℤ),
      CollectiveOpensToPoly fheRs4096 hash8 session c0s shares (orderRoot hash8 session w) w
        ∧ shares 0 0 = (fheRs4096.Δ : ℤ) * k := by
  refine ⟨fun j => (shortQuorumFixture fheRs4096 w k j).c0,
    fun j => (shortQuorumFixture fheRs4096 w k j).share, ?_, ?_⟩
  · exact deployed_honest_poly_collective_opens hash8 session
      (shortQuorumFixture fheRs4096 w k) w (fun j => rfl)
      (fun j => by norm_num [shortQuorumFixture])
      (fun j i => by norm_num [shortQuorumFixture])
  · show (shortQuorumFixture fheRs4096 w k 0).share 0 = (fheRs4096.Δ : ℤ) * k
    simp [shortQuorumFixture, HonestTranscript.share]

/-! ## 6. NAMED, not proved (the honest boundary — see the module doc for the full list)

  1. RNS residue rows / CRT bijection / forged-residue representability — beyond the
     reconstructed-coefficient model (inherited `DarkBazaarSameOpeningPoly` scope).
  2. mod-q wrap (ℤ phases) — inherited `Bfv.Noise` residual.
  3. NTT/SIMD slot encoding vs the base-128 order-index packing — unformalized equivalence.
  4. Collective-key RLWE well-formedness of each slot's `(c0, c1)` — GREEN-side assumption only.
  5. The malicious-share FIX (VSS / attributable refusal) and distributed witness production —
     the REDs prove the obligations; nothing here discharges them.
  6. Poly-level transcript-wide hiding — `Bfv.Smudging.TranscriptHybridLedger`, referenced only.
-/

#assert_all_clean [Market.DarkBazaarCollectiveOpeningPoly.collectivePoly_is_decryptConsistent,
  Market.DarkBazaarCollectiveOpeningPoly.collective_poly_decrypt_unique,
  Market.DarkBazaarCollectiveOpeningPoly.collective_poly_packedBook_unique,
  Market.DarkBazaarCollectiveOpeningPoly.collective_poly_decrypts,
  Market.DarkBazaarCollectiveOpeningPoly.honest_poly_collective_opens,
  Market.DarkBazaarCollectiveOpeningPoly.deployed_honest_poly_collective_opens,
  Market.DarkBazaarCollectiveOpeningPoly.deployed_honest_poly_collective_decrypts,
  Market.DarkBazaarCollectiveOpeningPoly.collectivePoly_to_sameOpeningPoly,
  Market.DarkBazaarCollectiveOpeningPoly.sameOpeningPoly_to_collectivePoly,
  Market.DarkBazaarCollectiveOpeningPoly.collective_slots_pack_to_scalar_apex,
  Market.DarkBazaarCollectiveOpeningPoly.deployed_collective_slot_budget_safe,
  Market.DarkBazaarCollectiveOpeningPoly.deployed_pack_after_smudge_blows_margin,
  Market.DarkBazaarCollectiveOpeningPoly.wrong_slot_breaks_collectivePoly,
  Market.DarkBazaarCollectiveOpeningPoly.single_tampered_share_breaks_poly_opening,
  Market.DarkBazaarCollectiveOpeningPoly.absentParty_share_zero,
  Market.DarkBazaarCollectiveOpeningPoly.absent_combine,
  Market.DarkBazaarCollectiveOpeningPoly.short_quorum_breaks_opening,
  Market.DarkBazaarCollectiveOpeningPoly.short_quorum_breaks_collectivePoly,
  Market.DarkBazaarCollectiveOpeningPoly.deployed_short_quorum_red_inhabited]

end Market.DarkBazaarCollectiveOpeningPoly
