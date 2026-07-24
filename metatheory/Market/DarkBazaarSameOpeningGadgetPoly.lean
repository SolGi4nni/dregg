/-
# Market.DarkBazaarSameOpeningGadgetPoly — the SameOpeningGadget lifted to the
  per-slot (polynomial-model) ciphertext: the CONSOLIDATED apex soundness.

**Substrate, said out loud: this AIR is AUTHORED IN LEAN.**  `GadgetAcceptsPoly` below is the
in-circuit acceptance relation (per-slot columns + vanishing gates + the shared Poseidon2 root
lanes) whose emitted descriptor would discharge the polynomial-model apex relation
`Market.DarkBazaarSameOpeningPoly.SameOpeningPoly` — the four-ordered-ciphertext-row shape the
deployed receipt actually carries.  No Rust AIR exists or will exist for this; Rust only fills a
Lean-authored layout.  Nothing here is emitted yet — emission is the FIRST named residual, not a
claim.

**What this file consolidates.**  The scalar gadget (`DarkBazaarSameOpeningGadget`) constrains ONE
phase column against `Δ·packedBook w`; the deployed object is FOUR ciphertext rows, one per order
slot (`SameOpeningPoly`'s model).  This file states the per-slot gadget — the decryption-
consistency gate on EACH of the 4 slots, conjoined with the SAME Poseidon2 root lanes over one
shared witness `w` — and proves the MASTER SOUNDNESS: an accepting per-slot column assignment
witnesses `SameOpeningPoly`, hence (by the poly file's packing keystone) the scalar apex
`SameOpening` on the recombined carrier, hence (by the poly file's decrypt keystone) exact
per-slot decryption.  One theorem (`gadgetAcceptsPoly_master`) carries the whole apex soundness
over the real per-slot ciphertext model.

**What is PROVED (every keystone has a failing side or an exact-arithmetic spine):**

  1. `gadgetAcceptsPoly_sound` — **MASTER SOUNDNESS, hypothesis-free:** `GadgetAcceptsPoly`
     implies `SameOpeningPoly` at the slot ciphertexts read off the phase columns and the root
     read off the root lanes — same `w`, same budget `B`, NO side conditions at all.
  2. `gadgetAcceptsPoly_packs_to_gadgetAccepts` + `gadgetAcceptsPoly_sound_via_scalar_gadget` —
     the poly gadget REFINES the scalar gadget: packing the four phase/noise columns base-128
     yields accepting SCALAR gadget columns (under the exact `PACK_GAIN·B` headroom), so the
     scalar keystone `gadgetAccepts_sound` is REUSED literally to land on the scalar apex
     `SameOpening` — and `pack_routes_agree` pins (definitionally) that this lands on the SAME
     packed carrier as the relation-level route through `sameOpeningPoly_packs_to_sameOpening`.
     One relation family, not two stories.
  3. `gadgetAcceptsPoly_master` — the consolidation: acceptance ⟹ `SameOpeningPoly` ∧ scalar
     `SameOpening` on the packed carrier ∧ every slot decrypts to EXACTLY its order code.
  4. `gadgetPoly_complete` — the converse: every `SameOpeningPoly` instance is realizable by an
     accepting per-slot column assignment (faithful in-circuit form, not strictly stronger).
  5. `split_slot_fails_gadgetPoly` — **RED (required failing side): a slot using a DIFFERENT
     order than the root commits is rejected.**  Root lanes from `w`, slot `j`'s phase an exact
     encryption of a wrong order `o'` (all other slots honest): `GadgetAcceptsPoly` is FALSE for
     the shared witness `w`, for EVERY noise-column assignment and EVERY budget `B` — the gate
     forces slot noise `Δ·d`, `d ≠ 0`, and the scalar gadget file's hypothesis-free
     `delta_unsafe` kills it.  `split_slot_red` itemizes that both halves are INDEPENDENTLY
     valid (the wrong-slot ciphertext genuinely opens to `o'`; the root is genuinely `w`'s), so
     the per-slot conjunction-over-shared-`w` is the entire cryptographic content.
  6. `split_slot_shared_witness_is_collision` — **RED, strengthened:** ANY witness `u` accepted
     on the split columns has its slot-`j` code pinned to the wrong order by the gate, yet `w`'s
     root — a `RootCollision` between `u` and `w`.  Absent a Poseidon2 binding break, split
     columns have NO shared witness at all.
  7. GREEN + deployed pins (kernel `decide` on the real fhe.rs degree-4096 numbers): honest
     per-slot columns accept (`honest_poly_accepts`, `deployed_fixture_accepts_poly` at
     `B = 2^20`); the tampered fixture order differs (`deployed_codes_differ`) and its split
     columns are REJECTED (`deployed_split_slot_rejected`); and `deployed_master_chain` runs the
     whole master soundness on the deployed numbers end to end.

**Roadmap position** (docs/deos/FHEGG-MATURITY-ROADMAP.md): this is relation-layer progress on
§3.1 (full shared-witness — the BFV market rows and the commitment bound through ONE witness);
the collective-key/distributed-prover residuals below are §3.2/§3.3 obligations, named not faked.
-/
import Market.DarkBazaarSameOpeningGadget
import Market.DarkBazaarSameOpeningPoly

set_option autoImplicit false

namespace Market.DarkBazaarSameOpeningGadgetPoly

open Bfv Market.DarkBazaarPrivateDescriptor Market.DarkBazaarSameOpening
  Market.DarkBazaarSameOpeningPoly Market.DarkBazaarSameOpeningGadget

/-! ## 1. The per-slot gadget columns.

The polynomial-model column set of the joint AIR: four ciphertext phase columns (public, one per
posted ciphertext row), four private noise witness columns (the explicit per-slot existentials of
`SlotOpensWithin`), and the eight shared root lanes — the SAME lanes
`darkBazaarPrivateN4K4Descriptor` pins at columns 2..9, bound once for all four slots. -/

/-- The per-slot gadget column view: slot phases, slot noise witnesses, shared root lanes. -/
structure GadgetColumnsPoly where
  /-- Slot phase columns (scalar model of the four posted BFV ciphertext rows). -/
  phase : Fin 4 → ℤ
  /-- Private per-slot noise witness columns — the explicit `e` of each slot's existential. -/
  noise : Fin 4 → ℤ
  /-- The eight public root lanes, shared by ALL four slot constraints. -/
  root : Fin 8 → Int

/-- The slot ciphertexts read off the phase columns — the `cts : Fin 4 → Ct P` of
`SameOpeningPoly`, so soundness lands on the poly relation over the REAL objects. -/
def slotCts (P : Params) (cols : GadgetColumnsPoly) : Fin 4 → Ct P :=
  fun j => ⟨cols.phase j⟩

/-! ## 2. The constraints: one gate per slot, one root binding, one shared `w`. -/

/-- The slot-`j` decryption-consistency vanishing gate (an expression that must equal `0`):
`phaseⱼ − (Δ·orderCode (w.orders j) + noiseⱼ)` — the per-slot form of the scalar `decGate`,
constraining slot `j` against ITS OWN order code of the shared witness. -/
def slotGate (P : Params) (cols : GadgetColumnsPoly) (w : PrivateWitness) (j : Fin 4) : ℤ :=
  cols.phase j - ((P.Δ : ℤ) * orderCode (w.orders j) + cols.noise j)

/-- **Slot dec-constraint**: the slot gate vanishes AND the slot noise column is inside the
budget `B`.  In the emitted AIR the budget is a bit-decomposition range check on the noise column
(fixed width, exactly like `DIFF_BITS`); here it is the exact bound the range check enforces. -/
def SlotDecConstraint (P : Params) (B : ℤ) (cols : GadgetColumnsPoly) (w : PrivateWitness)
    (j : Fin 4) : Prop :=
  slotGate P cols w j = 0 ∧ |cols.noise j| ≤ B

/-- **Root constraint, shared**: the eight root lanes equal the existing Poseidon2 root-chip
relation output for the SAME witness that feeds ALL FOUR slot gates.  `orderRoot` is reused from
`DarkBazaarPrivateDescriptor` (the chip `wide_root_lookup_sound` binds), not re-authored. -/
def RootConstraintPoly (hash8 : List Int → Fin 8 → Int) (session : Int)
    (cols : GadgetColumnsPoly) (w : PrivateWitness) : Prop :=
  ∀ i, cols.root i = orderRoot hash8 session w i

/-- **The per-slot SameOpeningGadget acceptance relation**: the budget is inside the decrypt
margin, EVERY slot's dec-constraint holds, and the root lanes bind the SAME `w`.  The one shared
`w` across all five conjuncts is the entire cryptographic content (REDs below).  `SafeNoise P B`
is carried in the relation so soundness needs no side hypotheses; in the emitted AIR it is a
parameter-level fact pinned per deployment (see residuals), not a per-proof constraint. -/
def GadgetAcceptsPoly (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int) (B : ℤ)
    (cols : GadgetColumnsPoly) (w : PrivateWitness) : Prop :=
  SafeNoise P B ∧ (∀ j, SlotDecConstraint P B cols w j) ∧ RootConstraintPoly hash8 session cols w

/-! ## 3. MASTER SOUNDNESS — acceptance discharges the polynomial apex relation. -/

/-- **KEYSTONE (master soundness), hypothesis-free.**  Any accepting per-slot column assignment
witnesses `SameOpeningPoly` for the slot ciphertexts read off the phase columns and the root read
off the root lanes — with the SAME `w` and the SAME budget `B`, and NO side conditions.  This is
the polynomial-model `gadgetAccepts_sound`: an emitted AIR faithful to `GadgetAcceptsPoly` closes,
per slot, the gap the poly RED (`wrong_slot_breaks_sameOpeningPoly`) proves the four independent
rows leave open. -/
theorem gadgetAcceptsPoly_sound
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ}
    {cols : GadgetColumnsPoly} {w : PrivateWitness}
    (h : GadgetAcceptsPoly P hash8 session B cols w) :
    SameOpeningPoly P hash8 session B (slotCts P cols) cols.root w := by
  obtain ⟨hB, hslots, hroot⟩ := h
  refine ⟨hB, fun j => ?_, fun i => hroot i⟩
  obtain ⟨hgate, hnb⟩ := hslots j
  refine ⟨cols.noise j, hnb, ?_⟩
  show cols.phase j = (P.Δ : ℤ) * orderCode (w.orders j) + cols.noise j
  unfold slotGate at hgate
  linarith

/-- Chained per-slot exactness: an accepting trace decrypts, at EVERY slot, to exactly that
slot's order code (the poly file's `slot_decrypts_exact` keystone through master soundness). -/
theorem gadgetAcceptsPoly_slot_decrypts
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ}
    {cols : GadgetColumnsPoly} {w : PrivateWitness}
    (h : GadgetAcceptsPoly P hash8 session B cols w) (ht : 128 ≤ P.t) (j : Fin 4) :
    (slotCts P cols j).decrypt = orderCode (w.orders j) :=
  slot_decrypts_exact (gadgetAcceptsPoly_sound h) ht j

/-! ## 4. The poly gadget REFINES the scalar gadget — `gadgetAccepts_sound` reused literally. -/

/-- Base-128 packing of the per-slot columns into SCALAR gadget columns: phases and noises
recombine with the `packedBook` weights (public-linear, the exact fold-path op set); the root
lanes pass through unchanged. -/
def packColumns (cols : GadgetColumnsPoly) : GadgetColumns where
  phase := cols.phase 0 + 128 * cols.phase 1 + 16384 * cols.phase 2 + 2097152 * cols.phase 3
  noise := cols.noise 0 + 128 * cols.noise 1 + 16384 * cols.noise 2 + 2097152 * cols.noise 3
  root := cols.root

/-- **The poly gadget refines the scalar gadget.**  Accepting per-slot columns pack to accepting
SCALAR `GadgetAccepts` columns for the SAME `w`, under the exact recombination headroom
`SafeNoise P (PACK_GAIN·B)` — the packed gate is the weighted sum of the slot gates, and the
packed noise is bounded by the poly file's `PACK_GAIN` arithmetic. -/
theorem gadgetAcceptsPoly_packs_to_gadgetAccepts
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ}
    {cols : GadgetColumnsPoly} {w : PrivateWitness}
    (h : GadgetAcceptsPoly P hash8 session B cols w)
    (hgain : SafeNoise P (PACK_GAIN * B)) :
    GadgetAccepts P hash8 session (packColumns cols) w := by
  obtain ⟨hB, hslots, hroot⟩ := h
  obtain ⟨hg0, hn0⟩ := hslots 0
  obtain ⟨hg1, hn1⟩ := hslots 1
  obtain ⟨hg2, hn2⟩ := hslots 2
  obtain ⟨hg3, hn3⟩ := hslots 3
  have hp0 : cols.phase 0 = (P.Δ : ℤ) * orderCode (w.orders 0) + cols.noise 0 := by
    unfold slotGate at hg0; linarith
  have hp1 : cols.phase 1 = (P.Δ : ℤ) * orderCode (w.orders 1) + cols.noise 1 := by
    unfold slotGate at hg1; linarith
  have hp2 : cols.phase 2 = (P.Δ : ℤ) * orderCode (w.orders 2) + cols.noise 2 := by
    unfold slotGate at hg2; linarith
  have hp3 : cols.phase 3 = (P.Δ : ℤ) * orderCode (w.orders 3) + cols.noise 3 := by
    unfold slotGate at hg3; linarith
  refine ⟨⟨?_, ?_⟩, fun i => hroot i⟩
  · -- the packed gate vanishes: it is the base-128 weighted sum of the four vanished slot gates
    unfold decGate
    rw [packedBook_expand]
    show (cols.phase 0 + 128 * cols.phase 1 + 16384 * cols.phase 2 + 2097152 * cols.phase 3)
        - ((P.Δ : ℤ) * (orderCode (w.orders 0) + 128 * orderCode (w.orders 1)
            + 16384 * orderCode (w.orders 2) + 2097152 * orderCode (w.orders 3))
          + (cols.noise 0 + 128 * cols.noise 1 + 16384 * cols.noise 2
            + 2097152 * cols.noise 3)) = 0
    rw [hp0, hp1, hp2, hp3]
    ring
  · -- the packed noise column is inside the margin: |Σ 128^j·eⱼ| ≤ PACK_GAIN·B, then monotone
    show SafeNoise P |cols.noise 0 + 128 * cols.noise 1 + 16384 * cols.noise 2
        + 2097152 * cols.noise 3|
    have habs : |cols.noise 0 + 128 * cols.noise 1 + 16384 * cols.noise 2
        + 2097152 * cols.noise 3| ≤ PACK_GAIN * B := by
      have t1 : |cols.noise 0 + 128 * cols.noise 1 + 16384 * cols.noise 2
            + 2097152 * cols.noise 3|
          ≤ |cols.noise 0 + 128 * cols.noise 1 + 16384 * cols.noise 2|
            + |2097152 * cols.noise 3| := abs_add_le _ _
      have t2 : |cols.noise 0 + 128 * cols.noise 1 + 16384 * cols.noise 2|
          ≤ |cols.noise 0 + 128 * cols.noise 1| + |16384 * cols.noise 2| := abs_add_le _ _
      have t3 : |cols.noise 0 + 128 * cols.noise 1|
          ≤ |cols.noise 0| + |128 * cols.noise 1| := abs_add_le _ _
      have m1 : |(128 : ℤ) * cols.noise 1| = 128 * |cols.noise 1| := by rw [abs_mul]; norm_num
      have m2 : |(16384 : ℤ) * cols.noise 2| = 16384 * |cols.noise 2| := by rw [abs_mul]; norm_num
      have m3 : |(2097152 : ℤ) * cols.noise 3| = 2097152 * |cols.noise 3| := by
        rw [abs_mul]; norm_num
      rw [PACK_GAIN_eq]
      have w1 : 128 * |cols.noise 1| ≤ 128 * B := by linarith
      have w2 : 16384 * |cols.noise 2| ≤ 16384 * B := by linarith
      have w3 : 2097152 * |cols.noise 3| ≤ 2097152 * B := by linarith
      linarith [t1, t2, t3, m1 ▸ w1, m2 ▸ w2, m3 ▸ w3, hn0]
    exact safeNoise_mono habs hgain

/-- The two pack routes are the SAME carrier, definitionally: the scalar-gadget ciphertext read
off `packColumns` IS the poly file's `packCt` of the slot ciphertexts.  So the refinement route
and the relation route below land on one object, not two look-alikes. -/
theorem pack_routes_agree (P : Params) (cols : GadgetColumnsPoly) :
    (⟨(packColumns cols).phase⟩ : Ct P) = packCt P (slotCts P cols) := rfl

/-- **Scalar apex via the scalar gadget, REUSED**: composing the refinement with the scalar
keystone `gadgetAccepts_sound` lands on the PROVED scalar `SameOpening` at the packed carrier —
the same endpoint as `sameOpeningPoly_packs_to_sameOpening ∘ gadgetAcceptsPoly_sound`
(`pack_routes_agree`). -/
theorem gadgetAcceptsPoly_sound_via_scalar_gadget
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ}
    {cols : GadgetColumnsPoly} {w : PrivateWitness}
    (h : GadgetAcceptsPoly P hash8 session B cols w)
    (hgain : SafeNoise P (PACK_GAIN * B)) :
    SameOpening P hash8 session (packCt P (slotCts P cols)) cols.root w := by
  have hs := gadgetAccepts_sound (gadgetAcceptsPoly_packs_to_gadgetAccepts h hgain)
  exact hs

/-- **THE CONSOLIDATED APEX SOUNDNESS — one theorem over the real per-slot ciphertext.**  An
accepting per-slot column assignment yields, simultaneously: the polynomial apex relation
`SameOpeningPoly`; the scalar apex relation `SameOpening` on the base-128 recombined carrier
(under the exact deployed-satisfiable headroom); and exact decryption of EVERY slot to its own
order code.  Everything the scalar gadget proved, now at the resolution the deployed receipt
actually has. -/
theorem gadgetAcceptsPoly_master
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ}
    {cols : GadgetColumnsPoly} {w : PrivateWitness}
    (h : GadgetAcceptsPoly P hash8 session B cols w)
    (hgain : SafeNoise P (PACK_GAIN * B)) (ht : 128 ≤ P.t) :
    SameOpeningPoly P hash8 session B (slotCts P cols) cols.root w
      ∧ SameOpening P hash8 session (packCt P (slotCts P cols)) cols.root w
      ∧ ∀ j, (slotCts P cols j).decrypt = orderCode (w.orders j) := by
  have hs := gadgetAcceptsPoly_sound h
  exact ⟨hs, sameOpeningPoly_packs_to_sameOpening hs hgain,
    fun j => slot_decrypts_exact hs ht j⟩

/-! ## 5. Completeness — the gadget is a faithful column form, not strictly stronger. -/

/-- **Completeness (the converse of master soundness)**: every `SameOpeningPoly` instance is
realizable by an accepting per-slot column assignment — phases from the real slot ciphertexts,
noise columns from the per-slot existential witnesses, root lanes as given.  Proving an emitted
AIR sound for `GadgetAcceptsPoly` neither over- nor under-shoots the poly apex relation. -/
theorem gadgetPoly_complete
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ}
    {cts : Fin 4 → Ct P} {root : Fin 8 → Int} {w : PrivateWitness}
    (h : SameOpeningPoly P hash8 session B cts root w) :
    ∃ cols : GadgetColumnsPoly, (∀ j, cols.phase j = (cts j).phase) ∧ cols.root = root ∧
      GadgetAcceptsPoly P hash8 session B cols w := by
  obtain ⟨hB, hslots, hroot⟩ := h
  choose e he hp using hslots
  refine ⟨⟨fun j => (cts j).phase, e, root⟩, fun _ => rfl, rfl, hB,
    fun j => ⟨?_, he j⟩, fun i => hroot i⟩
  show (cts j).phase - ((P.Δ : ℤ) * orderCode (w.orders j) + e j) = 0
  rw [hp j]
  ring

/-! ## 6. RED — one slot on a different order than the root commits is REJECTED.

The scalar gadget's shared-`w` failing side, lifted per slot: the gate at the forged slot forces
its noise column to `Δ·(code difference)`, provably outside every in-margin budget. -/

/-- **The slot gate pins the slot's code.**  If slot `j`'s phase column encodes `Δ·c` exactly
(zero-noise — the adversary's cleanest attempt) and the slot dec-constraint holds for witness `u`
under an in-margin budget, then `orderCode (u.orders j) = c`.  No parameter hypotheses:
`delta_unsafe` is unconditional. -/
theorem slot_gate_pins_code {P : Params} {B : ℤ} {cols : GadgetColumnsPoly} {u : PrivateWitness}
    {j : Fin 4} {c : ℤ}
    (hphase : cols.phase j = (P.Δ : ℤ) * c)
    (hB : SafeNoise P B)
    (hdec : SlotDecConstraint P B cols u j) :
    orderCode (u.orders j) = c := by
  by_contra hne
  obtain ⟨hgate, hnb⟩ := hdec
  unfold slotGate at hgate
  rw [hphase] at hgate
  have hde : cols.noise j = (P.Δ : ℤ) * (c - orderCode (u.orders j)) := by
    rw [mul_sub]; linarith
  have hd : c - orderCode (u.orders j) ≠ 0 := sub_ne_zero.mpr fun hc => hne hc.symm
  have hsafe : SafeNoise P |cols.noise j| := safeNoise_mono hnb hB
  rw [hde] at hsafe
  exact delta_unsafe P hd hsafe

/-- The split per-slot column assignment: root lanes from `w`, every slot phase an EXACT
(zero-noise) encryption of `w`'s own order — except slot `j`, which exactly encrypts a different
order `o'`; noise columns free (`en`).  The per-slot form of the two-independent-objects attack. -/
def splitSlotColumns (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) (j : Fin 4) (o' : PrivateOrder) (en : Fin 4 → ℤ) : GadgetColumnsPoly where
  phase := fun k => if k = j then (P.Δ : ℤ) * orderCode o'
    else (P.Δ : ℤ) * orderCode (w.orders k)
  noise := en
  root := orderRoot hash8 session w

/-- **RED (required failing side): a slot on a DIFFERENT order than the root commits does NOT
satisfy `GadgetAcceptsPoly`.**  For EVERY noise-column assignment and EVERY budget `B`: slot `j`
exactly encrypting `o'` with `orderCode o' ≠ orderCode (w.orders j)`, root lanes from `w` — the
gadget rejects the shared witness `w`.  The gate would force slot noise `Δ·d`, `d ≠ 0`, which
`delta_unsafe` proves is never inside the margin. -/
theorem split_slot_fails_gadgetPoly
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ} {w : PrivateWitness}
    (j : Fin 4) (o' : PrivateOrder)
    (hne : orderCode o' ≠ orderCode (w.orders j)) (en : Fin 4 → ℤ) :
    ¬ GadgetAcceptsPoly P hash8 session B (splitSlotColumns P hash8 session w j o' en) w := by
  rintro ⟨hB, hslots, -⟩
  exact hne (slot_gate_pins_code (c := orderCode o')
    (by simp [splitSlotColumns]) hB (hslots j)).symm

/-- **RED, itemized — both halves are INDEPENDENTLY valid, the conjunction still refuses.**  The
forged slot-`j` ciphertext genuinely opens to `o'` (zero noise), the root lanes are genuinely
`w`'s root — exactly the two-independently-valid-objects shape of the apex RED — yet
`GadgetAcceptsPoly` is FALSE.  The shared-`w` weld, per slot, is what the emitted AIR must
enforce. -/
theorem split_slot_red
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ} {w : PrivateWitness}
    (j : Fin 4) (o' : PrivateOrder)
    (hne : orderCode o' ≠ orderCode (w.orders j)) (en : Fin 4 → ℤ)
    (hpos : SafeNoise P (0 : ℤ)) :
    BfvOpensTo P (slotCts P (splitSlotColumns P hash8 session w j o' en) j) (orderCode o')
      ∧ (∀ i, (splitSlotColumns P hash8 session w j o' en).root i
          = orderRoot hash8 session w i)
      ∧ ¬ GadgetAcceptsPoly P hash8 session B (splitSlotColumns P hash8 session w j o' en) w :=
  ⟨⟨0, by simpa using hpos, by simp [slotCts, splitSlotColumns]⟩, fun _ => rfl,
    split_slot_fails_gadgetPoly j o' hne en⟩

/-- **RED, strengthened — split columns have NO shared witness short of a Poseidon2 collision.**
ANY `u` accepted on the split columns has its slot-`j` order code pinned to `o'` by the gate, yet
its root equal to `w`'s — a `RootCollision` between `u` and `w` (their packed books provably
differ, via `packedBook_injective_on_orders`).  Under the same computational binding assumption
the private descriptor already isolates, the split assignment is unsatisfiable outright. -/
theorem split_slot_shared_witness_is_collision
    {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int} {B : ℤ}
    {w u : PrivateWitness} (j : Fin 4) (o' : PrivateOrder)
    (hne : orderCode o' ≠ orderCode (w.orders j)) {en : Fin 4 → ℤ}
    (hacc : GadgetAcceptsPoly P hash8 session B (splitSlotColumns P hash8 session w j o' en) u) :
    RootCollision hash8 session u w := by
  obtain ⟨hB, hslots, hroot⟩ := hacc
  have hcj : orderCode (u.orders j) = orderCode o' :=
    slot_gate_pins_code (c := orderCode o') (by simp [splitSlotColumns]) hB (hslots j)
  refine ⟨Or.inl fun hpack => ?_, by funext i; exact (hroot i).symm⟩
  have hord : u.orders = w.orders := packedBook_injective_on_orders hpack
  rw [hord] at hcj
  exact hne hcj.symm

/-! ## 7. GREEN + deployed pins — both sides bite on the real fhe.rs degree-4096 numbers. -/

/-- The honest per-slot column assignment for witness `w` with slot noises `e`. -/
def honestColumnsPoly (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) (e : Fin 4 → ℤ) : GadgetColumnsPoly where
  phase := fun j => (P.Δ : ℤ) * orderCode (w.orders j) + e j
  noise := e
  root := orderRoot hash8 session w

/-- An honest prover with per-slot in-budget noise is accepted — the relation is satisfiable,
not an everything-rejector. -/
theorem honest_poly_accepts (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) {B : ℤ} {e : Fin 4 → ℤ}
    (hB : SafeNoise P B) (he : ∀ j, |e j| ≤ B) :
    GadgetAcceptsPoly P hash8 session B (honestColumnsPoly P hash8 session w e) w := by
  refine ⟨hB, fun j => ⟨?_, he j⟩, fun _ => rfl⟩
  show ((P.Δ : ℤ) * orderCode (w.orders j) + e j)
      - ((P.Δ : ℤ) * orderCode (w.orders j) + e j) = 0
  ring

/-- The deployed fresh-noise budget `B = 2^20` is inside the margin on the real degree-4096
parameter set (kernel-checked on the 109-bit `q`). -/
theorem deployed_budget_safe : SafeNoise fheRs4096 ((2 : ℤ) ^ 20) := by
  unfold SafeNoise; decide

/-- The deployed honest fixture columns (descriptor fixture book, zero slot noise). -/
def deployedHonestCols : GadgetColumnsPoly :=
  honestColumnsPoly fheRs4096 toyHash8 99 fixtureWitness (fun _ => 0)

/-- **GREEN pin on the deployed numbers**: the descriptor's fixture book, honestly encrypted per
slot at zero noise under `fheRs4096`, is accepted at budget `2^20`. -/
theorem deployed_fixture_accepts_poly :
    GadgetAcceptsPoly fheRs4096 toyHash8 99 (2 ^ 20) deployedHonestCols fixtureWitness :=
  honest_poly_accepts fheRs4096 toyHash8 99 fixtureWitness deployed_budget_safe
    (fun _ => by rw [abs_zero]; norm_num)

/-- The tampered slot-0 order of the descriptor's tamper fixture (`bid 11 @ 2` vs the fixture's
`bid 10 @ 2`). -/
def tamperedSlotOrder : PrivateOrder := ⟨⟨2, by omega⟩, ⟨11, by omega⟩⟩

/-- The tampered order's code really differs from the fixture's slot-0 code (kernel-evaluated:
`90 ≠ 82`). -/
theorem deployed_codes_differ :
    orderCode tamperedSlotOrder ≠ orderCode (fixtureWitness.orders 0) := by decide

/-- **RED pin on the deployed numbers**: root lanes from the fixture book, slot 0 exactly
encrypting the tampered order — rejected for every noise-column assignment, on `fheRs4096`. -/
theorem deployed_split_slot_rejected (en : Fin 4 → ℤ) :
    ¬ GadgetAcceptsPoly fheRs4096 toyHash8 99 (2 ^ 20)
        (splitSlotColumns fheRs4096 toyHash8 99 fixtureWitness 0 tamperedSlotOrder en)
        fixtureWitness :=
  split_slot_fails_gadgetPoly 0 tamperedSlotOrder deployed_codes_differ en

/-- **The whole master chain runs on the deployed numbers**: the accepted fixture columns yield
`SameOpeningPoly`, the scalar `SameOpening` on the packed carrier (headroom
`deployed_pack_headroom`), and exact per-slot decryption (`deployed_code_window`) — end to end,
no hypothesis left undischarged on the real parameter set. -/
theorem deployed_master_chain :
    SameOpeningPoly fheRs4096 toyHash8 99 (2 ^ 20) (slotCts fheRs4096 deployedHonestCols)
        deployedHonestCols.root fixtureWitness
      ∧ SameOpening fheRs4096 toyHash8 99
        (packCt fheRs4096 (slotCts fheRs4096 deployedHonestCols))
        deployedHonestCols.root fixtureWitness
      ∧ ∀ j, (slotCts fheRs4096 deployedHonestCols j).decrypt
          = orderCode (fixtureWitness.orders j) :=
  gadgetAcceptsPoly_master deployed_fixture_accepts_poly deployed_pack_headroom
    deployed_code_window

/-! ## 8. NAMED residuals (the honest boundary — none of these are faked above)

  1. **Emission — THE open piece of this lane.**  `GadgetAcceptsPoly` is the semantic acceptance
     relation; the emitted artifact — an `EffectVmDescriptor2` with 4 phase + 4 noise columns,
     per-slot bit-decomposition range checks realizing `|noiseⱼ| ≤ B`, and the
     `TableId.poseidon2` wide lookup binding the root lanes to the SAME witness columns that
     feed all four slot gates (sharing `PACKED_BOOK` with `darkBazaarPrivateN4K4Descriptor`) —
     plus its `Satisfied2` bridge (the analog of `darkBazaarPrivateN4K4_emitted_air_sound`) is
     NOT built here.  Until it is, this file is a proved spec of the per-slot AIR, not a
     proof-carrying AIR.  Note: `SafeNoise P B` is a parameter-level conjunct — in the emitted
     descriptor it is pinned per deployment (as `deployed_budget_safe` pins it), not a per-proof
     constraint; the per-proof constraint is the range check on each noise column.
  2. **RNS residue rows / CRT.**  Slot phases here are the CRT-reconstructed coefficients; the
     bijection `ℤ_q ≃ ∏ᵢ ℤ_{qᵢ}`, per-residue consistency, mod-`q` wrap, and the negacyclic
     ring/NTT encoding are the SAME named gaps as `DarkBazaarSameOpeningPoly` — inherited, not
     widened.
  3. **Collective-key decryption-share columns** (roadmap §3.2).  No single party can fill a
     phase column in the deployed n-of-n setting; each slot's dec-constraint must be restated
     over collective decryption-share columns.  NAMED, unbuilt.
  4. **Distributed witness production** (roadmap §3.3).  `w` must be produced so no single
     prover sees the full book.  Out of scope of the acceptance relation; named so the boundary
     is explicit.
-/

#assert_all_clean [Market.DarkBazaarSameOpeningGadgetPoly.gadgetAcceptsPoly_sound,
  Market.DarkBazaarSameOpeningGadgetPoly.gadgetAcceptsPoly_slot_decrypts,
  Market.DarkBazaarSameOpeningGadgetPoly.gadgetAcceptsPoly_packs_to_gadgetAccepts,
  Market.DarkBazaarSameOpeningGadgetPoly.pack_routes_agree,
  Market.DarkBazaarSameOpeningGadgetPoly.gadgetAcceptsPoly_sound_via_scalar_gadget,
  Market.DarkBazaarSameOpeningGadgetPoly.gadgetAcceptsPoly_master,
  Market.DarkBazaarSameOpeningGadgetPoly.gadgetPoly_complete,
  Market.DarkBazaarSameOpeningGadgetPoly.slot_gate_pins_code,
  Market.DarkBazaarSameOpeningGadgetPoly.split_slot_fails_gadgetPoly,
  Market.DarkBazaarSameOpeningGadgetPoly.split_slot_red,
  Market.DarkBazaarSameOpeningGadgetPoly.split_slot_shared_witness_is_collision,
  Market.DarkBazaarSameOpeningGadgetPoly.honest_poly_accepts,
  Market.DarkBazaarSameOpeningGadgetPoly.deployed_budget_safe,
  Market.DarkBazaarSameOpeningGadgetPoly.deployed_fixture_accepts_poly,
  Market.DarkBazaarSameOpeningGadgetPoly.deployed_codes_differ,
  Market.DarkBazaarSameOpeningGadgetPoly.deployed_split_slot_rejected,
  Market.DarkBazaarSameOpeningGadgetPoly.deployed_master_chain]

end Market.DarkBazaarSameOpeningGadgetPoly
