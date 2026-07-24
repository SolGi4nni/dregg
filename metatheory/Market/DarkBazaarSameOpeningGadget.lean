import Dregg2.Tactics
import Bfv.Noise
import Market.DarkBazaarPrivateDescriptor
import Market.DarkBazaarSameOpening

/-!
# The SameOpeningGadget: the Tier-0 apex construction, stated as a Lean in-circuit relation

**Substrate, said out loud:** this AIR is AUTHORED IN LEAN.  The gadget below is the in-circuit
relation (columns + vanishing constraints) whose emitted descriptor would DISCHARGE
`Market.DarkBazaarSameOpening.SameOpening` — the relation handoff §53 names as the cryptographic
apex.  No Rust AIR exists or will exist for this; Rust only fills a Lean-authored layout.

**The construction.**  One shared private witness `w : PrivateWitness` feeds BOTH halves:

  1. **Decryption-consistency** (`DecConstraint`): the ciphertext phase column satisfies the
     vanishing gate `phase − (Δ·packedBook w + noise) = 0`, and the private noise column is inside
     the decrypt margin (`SafeNoise P |noise|`).  This is the in-circuit form of `BfvOpensTo`: the
     existential noise of the spec relation becomes an explicit witness column, and the margin
     becomes a range constraint on that column (bit-decomposition in the emitted AIR, exactly like
     `DIFF_BITS` in `darkBazaarPrivateN4K4Descriptor`).
  2. **Root consistency** (`RootConstraint`): the eight root columns equal
     `orderRoot hash8 session w` — the SAME root-chip relation `DarkBazaarPrivateDescriptor`
     already binds through its wide Poseidon2 lookup (`wide_root_lookup_sound`).  Poseidon2 is NOT
     re-authored here; the gadget reuses the existing chip relation.

`GadgetAccepts` is their conjunction over the shared `w`.

**What is PROVED (the teeth):**

  * `gadgetAccepts_sound` — **the point of the gadget**: if the AIR accepts, `SameOpening` holds.
  * `gadget_complete` — the converse: every `SameOpening` instance is realizable by an accepting
    column assignment (the gadget is a faithful in-circuit form, not a strictly stronger relation).
  * `split_books_fail_gadget` — **RED, the shared-`w` binding bites**: columns whose two halves use
    DIFFERENT books (root from `w`, phase from `w'`, `packedBook w ≠ packedBook w'`) are rejected
    for the shared witness `w`, for EVERY value of the private noise column.  No parameter-side
    hypotheses: the needed `q ≤ 2tΔ` is now a THEOREM (`q_le_two_t_delta`) for every `Params`.
  * `split_books_shared_witness_is_collision` — stronger: ANY witness `u` that makes the split
    columns accept yields a `RootCollision` with `w`.  So absent a Poseidon2 binding break, split
    columns have NO shared witness at all — the conjunction is a real weld, not two parallel checks.
  * `deployed_fixture_accepts` / `deployed_split_fixture_rejected` — both sides pinned on the real
    deployed numbers (`fheRs4096`, the descriptor's fixture book vs. its tampered book).

**Scope, honest (NAMED residuals, see the closing section):** scalar `Bfv` phase model (the
RNS-polynomial lift is a named gap, as in `Bfv.Noise`); emission to a real `EffectVmDescriptor2`
with the `Satisfied2` bridge is not done here; the phase column of the deployed system must come
from collective-key decryption shares (no single party holds `s`), and witness production must be
distributed — both named, neither faked.
-/

namespace Market.DarkBazaarSameOpeningGadget

open Bfv Market.DarkBazaarPrivateDescriptor Market.DarkBazaarSameOpening

/-! ## 1. The gadget columns.

The scalar-model column set of the joint AIR: the ciphertext phase (public, from the posted
ciphertext), the private noise witness column, and the eight public root lanes (the same lanes
`darkBazaarPrivateN4K4Descriptor` pins at columns 2..9). -/

/-- The gadget's column view: ciphertext phase, private noise witness, eight root lanes. -/
structure GadgetColumns where
  /-- The ciphertext phase column (scalar model of the posted BFV ciphertext). -/
  phase : ℤ
  /-- The private noise witness column — the explicit `e` of `BfvOpensTo`'s existential. -/
  noise : ℤ
  /-- The eight public root lanes (`ROOT 0 .. ROOT 7` of the private descriptor). -/
  root : Fin 8 → Int

/-! ## 2. The two constraint halves, over ONE shared witness. -/

/-- The decryption-consistency vanishing gate, in AIR form (an expression that must equal `0`):
`phase − (Δ·packedBook w + noise)`. -/
def decGate (P : Params) (cols : GadgetColumns) (w : PrivateWitness) : ℤ :=
  cols.phase - ((P.Δ : ℤ) * packedBook w + cols.noise)

/-- **Half 1 — decryption consistency**: the gate vanishes AND the noise column is inside the
decrypt margin.  In the emitted AIR the margin is a range check (bit decomposition) on the noise
column; here it is the exact `SafeNoise` predicate the range check enforces. -/
def DecConstraint (P : Params) (cols : GadgetColumns) (w : PrivateWitness) : Prop :=
  decGate P cols w = 0 ∧ SafeNoise P |cols.noise|

/-- **Half 2 — root consistency**: the eight root lanes equal the existing Poseidon2 root-chip
relation output for the SAME witness.  `orderRoot` is the exact function
`DarkBazaarPrivateDescriptor.wide_root_lookup_sound` binds to the real chip — reused, not
re-authored. -/
def RootConstraint (hash8 : List Int → Fin 8 → Int) (session : Int)
    (cols : GadgetColumns) (w : PrivateWitness) : Prop :=
  ∀ i, cols.root i = orderRoot hash8 session w i

/-- **The SameOpeningGadget acceptance relation**: both halves over ONE shared `w`.  The sharing is
the entire cryptographic content — see the REDs below for what breaks without it. -/
def GadgetAccepts (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int)
    (cols : GadgetColumns) (w : PrivateWitness) : Prop :=
  DecConstraint P cols w ∧ RootConstraint hash8 session cols w

/-! ## 3. Parameter facts: the RED's side conditions are THEOREMS, not hypotheses.

`delta_diff_unsafe` (apex file) needs `q ≤ 2tΔ`.  That holds for EVERY `Params` because
`q = Δt + r` with `r < t ≤ Δt` — so the gadget REDs below carry no parameter hypotheses at all. -/

/-- The standard BFV parameter fact, proved for every parameter set: `q ≤ 2·t·Δ`. -/
theorem q_le_two_t_delta (P : Params) : (P.q : ℤ) ≤ 2 * (P.t : ℤ) * (P.Δ : ℤ) := by
  have hnat : P.q ≤ 2 * P.t * P.Δ := by
    have h2 : P.t ≤ P.Δ * P.t := Nat.le_mul_of_pos_left P.t P.Δ_pos
    calc P.q = P.Δ * P.t + P.r := P.q_eq
      _ ≤ P.Δ * P.t + P.t := Nat.add_le_add_left (Nat.le_of_lt P.r_lt_t) _
      _ ≤ P.Δ * P.t + P.Δ * P.t := Nat.add_le_add_left h2 _
      _ = 2 * P.t * P.Δ := by ring
  exact_mod_cast hnat

/-- `Δ` times a nonzero difference is never safe noise — the apex file's `delta_diff_unsafe` with
all four side conditions DISCHARGED for every parameter set. -/
theorem delta_unsafe (P : Params) {d : ℤ} (hd : d ≠ 0) :
    ¬ SafeNoise P |(P.Δ : ℤ) * d| :=
  delta_diff_unsafe hd (by positivity) (by exact_mod_cast P.t_pos) (by positivity)
    (q_le_two_t_delta P)

/-! ## 4. Soundness — the whole point: if the AIR accepts, SameOpening holds. -/

/-- Half 1 alone is the in-circuit form of `BfvOpensTo`: the explicit noise column realizes the
spec relation's existential. -/
theorem decConstraint_opens {P : Params} {cols : GadgetColumns} {w : PrivateWitness}
    (h : DecConstraint P cols w) :
    BfvOpensTo P ⟨cols.phase⟩ (packedBook w) := by
  obtain ⟨hgate, hsafe⟩ := h
  refine ⟨cols.noise, hsafe, ?_⟩
  have hph : cols.phase = (P.Δ : ℤ) * packedBook w + cols.noise := by
    unfold decGate at hgate
    linarith
  exact hph

/-- **KEYSTONE (soundness): the gadget DISCHARGES the apex relation.**  Any accepting column
assignment witnesses `SameOpening` for the ciphertext read off the phase column and the root read
off the root lanes — with the SAME `w` on both sides.  This is the statement that an emitted AIR
faithful to `GadgetAccepts` closes the Tier-0 gap the apex RED
(`independent_valid_objects_break_same_opening`) proves the composite receipt leaves open. -/
theorem gadgetAccepts_sound {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int}
    {cols : GadgetColumns} {w : PrivateWitness}
    (h : GadgetAccepts P hash8 session cols w) :
    SameOpening P hash8 session ⟨cols.phase⟩ cols.root w :=
  ⟨decConstraint_opens h.1, h.2⟩

/-- Chained consequence through the apex file: an accepting trace forces the ciphertext's noise AT
the committed book inside the margin — so it decrypts to exactly `packedBook w`, never a silently
different book. -/
theorem gadgetAccepts_noise_safe {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int}
    {cols : GadgetColumns} {w : PrivateWitness}
    (h : GadgetAccepts P hash8 session cols w) :
    SafeNoise P |(Ct.mk cols.phase : Ct P).noiseAtInt (packedBook w)| :=
  sameOpening_noise_safe (gadgetAccepts_sound h)

/-- **Completeness (the converse): every SameOpening instance is realizable in-circuit.**  The
gadget is a faithful column form of the spec relation, not a strictly stronger one — so proving
the emitted AIR sound for `GadgetAccepts` neither over- nor under-shoots `SameOpening`. -/
theorem gadget_complete {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int}
    {ct : Ct P} {root : Fin 8 → Int} {w : PrivateWitness}
    (h : SameOpening P hash8 session ct root w) :
    ∃ cols : GadgetColumns,
      cols.phase = ct.phase ∧ cols.root = root ∧ GadgetAccepts P hash8 session cols w := by
  obtain ⟨⟨e, he, hp⟩, hroot⟩ := h
  refine ⟨⟨ct.phase, e, root⟩, rfl, rfl, ⟨?_, he⟩, hroot⟩
  show ct.phase - ((P.Δ : ℤ) * packedBook w + e) = 0
  rw [hp]
  ring

/-! ## 5. The failing side: the shared-`w` binding bites.

The decryption-consistency half PINS the packed book: a phase honestly encoding book `w'` cannot
satisfy the gate for any other book, whatever the noise column claims, because the forced noise is
`Δ·(difference)` — provably outside the margin. -/

/-- **The gate pins the book.**  If the phase column encodes `packedBook wPhase` (zero-noise
encryption — the adversary's cleanest attempt) and `DecConstraint` holds for witness `u`, then
`packedBook u = packedBook wPhase`.  No parameter hypotheses: `delta_unsafe` is unconditional. -/
theorem dec_pins_book {P : Params} {cols : GadgetColumns} {u wPhase : PrivateWitness}
    (hphase : cols.phase = (P.Δ : ℤ) * packedBook wPhase)
    (hdec : DecConstraint P cols u) :
    packedBook u = packedBook wPhase := by
  by_contra hne
  obtain ⟨hgate, hsafe⟩ := hdec
  have heq : cols.phase = (P.Δ : ℤ) * packedBook u + cols.noise := by
    unfold decGate at hgate
    linarith
  have hnoise : cols.noise = (P.Δ : ℤ) * (packedBook wPhase - packedBook u) := by
    rw [mul_sub]
    rw [hphase] at heq
    linarith
  have hd : packedBook wPhase - packedBook u ≠ 0 := by
    intro h0
    exact hne (by omega)
  rw [hnoise] at hsafe
  exact delta_unsafe P hd hsafe

/-- The split column assignment: root lanes from `wRoot`, phase from a zero-noise encryption of
`wPhase`'s book, noise column free (`e`) — exactly the two-independent-objects attack the apex RED
builds against the composite receipt. -/
def splitColumns (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int)
    (wRoot wPhase : PrivateWitness) (e : ℤ) : GadgetColumns where
  phase := (P.Δ : ℤ) * packedBook wPhase
  noise := e
  root := orderRoot hash8 session wRoot

/-- **RED — different books do NOT satisfy GadgetAccepts.**  Root half from `w`, phase half from
`w'` with a different packed book: the gadget REJECTS the shared witness `w`, for EVERY value of
the private noise column.  Contrast with the apex RED: there, the two objects are each
independently valid and the composite receipt accepts them; here, the shared-`w` conjunction is
exactly what refuses. -/
theorem split_books_fail_gadget {P : Params} {hash8 : List Int → Fin 8 → Int} {session : Int}
    {w w' : PrivateWitness} (hne : packedBook w ≠ packedBook w') (e : ℤ) :
    ¬ GadgetAccepts P hash8 session (splitColumns P hash8 session w w' e) w := by
  intro hacc
  exact hne (dec_pins_book rfl hacc.1)

/-- **RED, strengthened — split columns have NO shared witness short of a Poseidon2 collision.**
Any `u` accepted on the split columns has its book pinned to `w'` by the gate, yet its root equal
to `w`'s — a `RootCollision` between `u` and `w`.  So under computational Poseidon2 binding (the
same assumption `DarkBazaarPrivateDescriptor` already isolates in `RootCollision`), the split
assignment is unsatisfiable outright: the conjunction is a weld, not two parallel checks. -/
theorem split_books_shared_witness_is_collision {P : Params}
    {hash8 : List Int → Fin 8 → Int} {session : Int} {w w' u : PrivateWitness}
    (hne : packedBook w ≠ packedBook w') {e : ℤ}
    (hacc : GadgetAccepts P hash8 session (splitColumns P hash8 session w w' e) u) :
    RootCollision hash8 session u w := by
  have hpb : packedBook u = packedBook w' := dec_pins_book rfl hacc.1
  refine ⟨Or.inl fun hc => hne ?_, ?_⟩
  · rw [← hc, hpb]
  · funext i
    exact (hacc.2 i).symm

/-! ## 6. Non-vacuity: the honest side accepts, on the deployed numbers. -/

/-- The honest column assignment for witness `w` with noise `e`. -/
def honestColumns (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) (e : ℤ) : GadgetColumns where
  phase := (P.Δ : ℤ) * packedBook w + e
  noise := e
  root := orderRoot hash8 session w

/-- An honest prover with in-margin noise is accepted — the relation is satisfiable, not an
everything-rejector. -/
theorem honest_columns_accept (P : Params) (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) {e : ℤ} (he : SafeNoise P |e|) :
    GadgetAccepts P hash8 session (honestColumns P hash8 session w e) w := by
  refine ⟨⟨?_, he⟩, fun _ => rfl⟩
  show ((P.Δ : ℤ) * packedBook w + e) - ((P.Δ : ℤ) * packedBook w + e) = 0
  ring

/-- Zero noise is inside the deployed margin (kernel-evaluated on the real 109-bit `q`). -/
theorem deployed_zero_noise_safe : SafeNoise fheRs4096 |(0 : ℤ)| := by
  unfold SafeNoise
  decide

/-- **GREEN pin on the deployed numbers**: the descriptor's fixture book, honestly encrypted at
zero noise under `fheRs4096`, is accepted. -/
theorem deployed_fixture_accepts :
    GadgetAccepts fheRs4096 toyHash8 99
      (honestColumns fheRs4096 toyHash8 99 fixtureWitness 0) fixtureWitness :=
  honest_columns_accept fheRs4096 toyHash8 99 fixtureWitness deployed_zero_noise_safe

/-- The fixture book and the descriptor's tampered book really differ (kernel-evaluated). -/
theorem deployed_books_differ :
    packedBook fixtureWitness ≠ packedBook tamperedOrderWitness := by decide

/-- **RED pin on the deployed numbers**: root lanes from the fixture book, phase from the tampered
book — rejected for every noise column value, on `fheRs4096`. -/
theorem deployed_split_fixture_rejected (e : ℤ) :
    ¬ GadgetAccepts fheRs4096 toyHash8 99
        (splitColumns fheRs4096 toyHash8 99 fixtureWitness tamperedOrderWitness e)
        fixtureWitness :=
  split_books_fail_gadget deployed_books_differ e

/-! ## 7. NAMED residuals (the honest boundary of this file — none of these are faked above)

  1. **Emission.**  `GadgetAccepts` is the semantic relation; the emitted artifact — an
     `EffectVmDescriptor2` with the phase/noise columns, a bit-decomposition range check realizing
     `SafeNoise` on the noise column, and the `TableId.poseidon2` wide lookup sharing the SAME
     `PACKED_BOOK` column with `darkBazaarPrivateN4K4Descriptor` — plus its `Satisfied2` bridge
     (the analog of `darkBazaarPrivateN4K4_emitted_air_sound` through the integer decode) is NOT
     built here.  Until it is, the gadget is a proved spec of the AIR, not a proof-carrying AIR.
  2. **RNS-polynomial lift.**  `phase : ℤ` is the scalar `Bfv` model coefficient; the deployed
     ciphertext is degree-4096 RNS.  Same named gap as `Bfv.Noise`, inherited, not widened.
  3. **Collective-key decryption columns.**  The phase is not a column any single prover can fill
     in the deployed n-of-n setting — no single party holds `s`.  The decryption-consistency half
     must be restated over collective decryption-share columns.  NAMED, unbuilt.
  4. **Distributed witness production.**  `w` must be produced so that no single prover sees the
     full book (handoff §53's second missing piece).  Out of scope of the relation, named here so
     the boundary is explicit.
-/

#assert_all_clean [Market.DarkBazaarSameOpeningGadget.q_le_two_t_delta,
  Market.DarkBazaarSameOpeningGadget.delta_unsafe,
  Market.DarkBazaarSameOpeningGadget.gadgetAccepts_sound,
  Market.DarkBazaarSameOpeningGadget.gadgetAccepts_noise_safe,
  Market.DarkBazaarSameOpeningGadget.gadget_complete,
  Market.DarkBazaarSameOpeningGadget.dec_pins_book,
  Market.DarkBazaarSameOpeningGadget.split_books_fail_gadget,
  Market.DarkBazaarSameOpeningGadget.split_books_shared_witness_is_collision,
  Market.DarkBazaarSameOpeningGadget.honest_columns_accept,
  Market.DarkBazaarSameOpeningGadget.deployed_fixture_accepts,
  Market.DarkBazaarSameOpeningGadget.deployed_split_fixture_rejected]

end Market.DarkBazaarSameOpeningGadget
