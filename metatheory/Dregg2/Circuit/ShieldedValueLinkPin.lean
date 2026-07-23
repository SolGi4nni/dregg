/-
# Dregg2.Circuit.ShieldedValueLinkPin — the spent-leaf VALUE is never tied to the amount
  conservation clears (WOUND #16, the shielded-pool INFLATION vector).

**What this proves, and why it was missing.** The deployed shielded transfer
(`turn/src/executor/apply.rs :: apply_shielded_transfer`) accepts on two value gates that never meet:

  * **the STARK/wide side** — `verify_stark_with_wide_bindings(&transfer, &wide_bindings)`
    (`apply.rs:1753`) proves each input's membership + nullifier AND ties the published one-felt
    `value_binding` (spend circuit C7, `hash_fact(value,[asset,rand,0])`) to a full-`u64` wide carrier
    (`circuit-prove/src/shielded/wide_value_binding.rs`). Both digests are honest images of the
    STARK-witnessed **leaf value** (`spend_circuit.rs` C6+C7a). So far so good — the leaf value is bound.
  * **the Pedersen side** — `verify_full_conservation_bytes(input_legs, output_legs, …)`
    (`apply.rs:1764`, `cell-crypto/src/value_commitment.rs:490`) checks `Σ C_in = Σ C_out` in the group
    plus one `[0,2^64)` range proof per output. But it sums the **prover-supplied Pedersen legs**
    (`transfer.input_commitment_bytes()`, `transfer.rs:247`), opaque `commit(legValue, blinding)` blobs.
  * **nowhere** is the Pedersen leg's committed value tied to the STARK leaf value. `transfer.rs:196`
    says it in one line: *"This transcript binding does not prove leaf↔leg value equality."* And
    `transfer.rs:64-68`: the `value_binding` *"does not yet tie the deployed Pedersen leg to the
    STARK-witnessed leaf: `verify_value_link` exercises that compatibility bridge in tests only."*

So a malicious prover spends a note they genuinely own worth `v = 1`, honestly proving membership,
nullifier, `value_binding = Bind 1`, and the wide carrier of `1` — then supplies an input Pedersen leg
`commit(1_000_000, blinding)`. Conservation `Σ C_in = Σ C_out` balances the **fake** million against a
million of outputs (whose range proofs pass — a million is a perfectly good `[0,2^64)` value), and the
pool **mints 1_000_000 from a 1-token note.** No forged leaf (that is #15) — the spent note is real;
the theft is purely the missing leaf↔leg value link. As the decision brief puts it
(`docs/DECISION-shielded-redesign-2026-07-20.md` #16): *"Deployed conservation proves only that the
Ristretto legs balance, not that they equal the STARK-witnessed leaf values → a prover can mint by
decoupling them."*

**The LAUNDER, exposed.** Two things make the deployed path *look* closed:
  * the C7 `value_binding` IS honestly bound to the leaf value in-AIR, and the wide carrier is a
    mandatory full-`u64` binding — a reader concludes "value is bound." It is — but conservation never
    consults `value_binding`; it sums the *separate, free* Pedersen leg. A binding on a quantity the
    no-mint gate does not use buys nothing.
  * the Rust test `leaf_leg_value_link_matches_verifies_mismatch_rejects`
    (`circuit-prove/tests/shielded_transfer_m2a.rs:441`) exercises `verify_value_link`, which DOES tie
    leg↔leaf (`commit(value,blinding) == leg` AND `value_link_binding(value) == value_binding`), and it
    even asserts the inflated leg is `LegMismatch`-rejected. Real — but `verify_value_link` is
    **never called by `apply_shielded_transfer`**. The test is a green light on a check the deployed
    gate does not run.

**What is proved here** (theorems over ALL inputs; the model is faithful to the two-gate structure,
HASH-AGNOSTIC — the C7/wide binding hashes `Bind`/`Wide` are abstract deterministic functions, so the
statements hold for the real Poseidon2):

  * **THE FALSIFIER (`genuine_note_mints_anything`, `genuine_note_inflates`).** The deployed accept —
    conservation over the leg values, with membership + the honest C7/wide bindings on the leaf, and NO
    `legValue = leafValue` conjunct — admits, for a genuinely committed note of ANY value `v`, a
    transfer that mints ANY amount `M` (`genuine_note_mints_anything`); concretely a `v`-note that mints
    `v+1` while the C7 binding stays honestly bound to `v` and the value-link check fails
    (`genuine_note_inflates`).
  * **THE LAUNDER, exposed (`verify_value_link_forces_link` vs `link_test_is_not_the_gate`).** The
    value-link predicate faithfully captures `verify_value_link` (with `Bind` injective, its two checks
    force `legValue = leafValue`), and the test rejecting a mismatch is real — yet the deployed accept
    (which omits it) STILL admits the inflating transfer.
  * **THE FIX, sound (`linked_conservation_over_real_value`, `linked_no_inflation`,
    `link_closes_the_falsifier`).** Adding the conjunct `∀ input, legValue = leafValue` (exactly
    `verify_value_link`'s leg tie, folded into acceptance) forces conservation to run over the REAL
    spent values, so the minted total EQUALS the real spent value — the inflation is rejected, over all
    inputs.

**Byte-safe / posture.** This module does NOT touch deployed code. The in-AIR fix — recomputing
`value_binding`/`leaf_commit` over shared value cells and enforcing `Σ value = Σ out` in-circuit — is
authored as Lean AIR in `Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor` (Option-A lane 2), and
*routing the deployed transfer through it* (retiring the split `verify_full_conservation_bytes` over
free Pedersen legs) is the gated deploy, NOT this file. This is the machine-checked statement of the
invariant that redesign must establish: the falsifier that prices the open wound and the soundness the
link buys.

**Scope (honest).** This is the value-link brick of the `spend_circuit → Lean` campaign, at the
resolution of the leaf↔leg value-conservation trust boundary (NOT the full AIR). Membership/nullifier
soundness (#15's root-pin is its own module), the Ristretto DLog floor and its PQ replacement (#17),
the negative-output range-proof gate (present, orthogonal), and folding `verify_value_link` into the
deployed AIR are the rest of the campaign. Modeled faithfully, they are ORTHOGONAL to this gap: the
theft here uses a genuine note and positive, in-range output values.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Circuit.ShieldedValueLinkPin`.
-/
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Circuit.ShieldedValueLinkPin

/-! ## 1. Felt, an input, and a transfer.

Faithful to the deployed two-gate object. One field element per lane (the BabyBear range prices offline
grind but is irrelevant to the leaf↔leg gap, so a lane is an integer, as in `ShieldedMerkleRootPin` /
`FinalityCertWidth`). Each input carries the value the STARK leaf witnesses (`leafValue`, C6-bound), the
value the Pedersen leg conservation actually sums (`legValue`, prover-supplied and opaque), and the two
honest published bindings (`valueBinding` = C7, `wideBinding` = the full-`u64` carrier). -/

/-- One field element, modeled by its canonical value. -/
abbrev Felt : Type := ℤ

/-- One spent input. `leafValue` is the STARK-witnessed spent value (spend circuit C6). `legValue` is
the value inside the input's Pedersen leg that `verify_full_conservation_bytes` sums — prover-supplied,
NOT tied to `leafValue` on the deployed path. `valueBinding`/`wideBinding` are the honest published
C7 / wide bindings (each an image of `leafValue`). -/
structure Input where
  leafValue    : Felt
  legValue     : Felt
  valueBinding : Felt
  wideBinding  : Felt
deriving DecidableEq, Repr

/-- A published shielded transfer: the hidden inputs + the output Pedersen leg values (the minted
amounts, each range-proved into `[0,2^64)` downstream). -/
structure Transfer where
  inputs  : List Input
  outLegs : List Felt

/-- The REAL value entering the pool: `Σ` of the STARK-witnessed leaf values. -/
def realSpent (t : Transfer) : Felt := (t.inputs.map (fun i => i.leafValue)).sum

/-- The value conservation actually sums: `Σ` of the input Pedersen-leg values
(`verify_full_conservation_bytes` over `input_commitment_bytes`). -/
def legTotal (t : Transfer) : Felt := (t.inputs.map (fun i => i.legValue)).sum

/-- The value MINTED: `Σ` of the output Pedersen-leg values. -/
def mintedTotal (t : Transfer) : Felt := t.outLegs.sum

/-- Pointwise-equal maps sum equally (structural recursion, no IH-weakening hazard). -/
theorem sum_map_congr {α : Type} (f g : α → Felt) :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → (l.map f).sum = (l.map g).sum
  | [], _ => rfl
  | a :: t, h => by
      simp only [List.map_cons, List.sum_cons]
      rw [h a (List.mem_cons.mpr (Or.inl rfl)),
          sum_map_congr f g t (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

/-- A single-input single-output transfer reduces its three totals to the bare cell values. Isolates
the `List.sum` reduction so the falsifiers can `rw` with concrete equations. -/
theorem single_reduces (leaf leg vb wb out : Felt) :
    realSpent ⟨[⟨leaf, leg, vb, wb⟩], [out]⟩ = leaf ∧
    legTotal ⟨[⟨leaf, leg, vb, wb⟩], [out]⟩ = leg ∧
    mintedTotal ⟨[⟨leaf, leg, vb, wb⟩], [out]⟩ = out := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [realSpent, legTotal, mintedTotal]

/-! ## 2. The DEPLOYED accept predicate — conservation over the leg values, leaf↔leg link ABSENT.

Faithful to `apply_shielded_transfer` at HEAD: membership holds (`Member` on each leaf — #15's domain,
which HOLDS here: the attacker spends a note they genuinely own), the C7 `value_binding` and the wide
carrier are honestly bound to `leafValue`, and conservation sums the `legValue`s. The one thing missing
is any conjunct forcing `legValue = leafValue` — that omission IS the wound. -/

/-- The deployed accept, HEAD-faithful. Every conjunct is a check the deployed path actually runs;
`legValue` is constrained ONLY through conservation, never tied to `leafValue`. -/
def accepts (Bind Wide : Felt → Felt) (Member : Felt → Prop) (t : Transfer) : Prop :=
  (∀ i ∈ t.inputs, Member i.leafValue) ∧               -- membership (spend circuit; here it HOLDS)
  (∀ i ∈ t.inputs, i.valueBinding = Bind i.leafValue) ∧ -- C7 value_binding, honestly bound (the launder)
  (∀ i ∈ t.inputs, i.wideBinding = Wide i.leafValue) ∧  -- the mandatory full-u64 wide carrier
  legTotal t = mintedTotal t                            -- conservation over the PEDERSEN LEGS

/-- The leaf↔leg VALUE LINK the deployed path omits — exactly `verify_value_link`'s leg tie folded into
acceptance: the value inside each input's Pedersen leg equals the STARK-witnessed leaf value. -/
def linkHolds (t : Transfer) : Prop := ∀ i ∈ t.inputs, i.legValue = i.leafValue

/-- The SOUND accept: the deployed checks PLUS the leaf↔leg link. This is what routing the transfer
through the in-AIR value-link/Σ-conservation block (`ShieldedValueLinkDescriptor`, Option-A) establishes
— conservation over the SAME value cells the leaf commits, no free second "Pedersen value." -/
def acceptsLinked (Bind Wide : Felt → Felt) (Member : Felt → Prop) (t : Transfer) : Prop :=
  accepts Bind Wide Member t ∧ linkHolds t

/-- **`accepts_of_conservation` (the wound in one line).** Acceptance follows from membership, the
honest bindings, and conservation ALONE — the leaf value never has to match the leg value conservation
sums. The link is nowhere in the sufficient condition. -/
theorem accepts_of_conservation (Bind Wide : Felt → Felt) (Member : Felt → Prop) (t : Transfer)
    (hm : ∀ i ∈ t.inputs, Member i.leafValue)
    (hb : ∀ i ∈ t.inputs, i.valueBinding = Bind i.leafValue)
    (hw : ∀ i ∈ t.inputs, i.wideBinding = Wide i.leafValue)
    (hc : legTotal t = mintedTotal t) : accepts Bind Wide Member t := ⟨hm, hb, hw, hc⟩

/-- **`link_rejects_leg_leaf_mismatch` (the link bites, directly).** Any transfer with an input whose
leg value differs from its leaf value is REJECTED by the linked predicate — no decoupling survives. -/
theorem link_rejects_leg_leaf_mismatch (Bind Wide : Felt → Felt) (Member : Felt → Prop) (t : Transfer)
    (i : Input) (hi : i ∈ t.inputs) (hne : i.legValue ≠ i.leafValue) :
    ¬ acceptsLinked Bind Wide Member t := by
  rintro ⟨-, hlink⟩; exact hne (hlink i hi)

/-! ## 3. THE FALSIFIER — a genuinely committed note mints anything.

No forged leaf (that is #15): the attacker spends a note they own (`Member v`), honestly binds it, and
supplies an input Pedersen leg committing to a DIFFERENT value. Conservation balances the fake value
against the outputs; the pool mints it. -/

/-- **`genuine_note_mints_anything` (THE FALSIFIER, unbounded).** For every honest note value `v`
(genuinely committed, `Member v`) and every target mint `M`, the deployed predicate ACCEPTS a transfer
whose real spent value is `v` but whose minted total is `M`. A single small real note mints any amount.
Hash-agnostic: the C7/wide bindings are honestly `Bind v`/`Wide v`, so acceptance holds for the real
Poseidon2 whatever it is. -/
theorem genuine_note_mints_anything (Bind Wide : Felt → Felt) (Member : Felt → Prop)
    (v M : Felt) (hmem : Member v) :
    ∃ t : Transfer, accepts Bind Wide Member t ∧ realSpent t = v ∧ mintedTotal t = M := by
  refine ⟨{ inputs := [{ leafValue := v, legValue := M, valueBinding := Bind v, wideBinding := Wide v }],
            outLegs := [M] }, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact hmem
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl
  · simp [legTotal, mintedTotal]
  · simp [realSpent]
  · simp [mintedTotal]

/-- **`genuine_note_inflates` (THE FALSIFIER, theft form — the whole shape at once).** Given ANY note
the attacker genuinely owns (`Member v`), there is a transfer that:
  * spends only that genuine note (`realSpent = v`, every leaf `Member`),
  * is ACCEPTED by the deployed predicate,
  * mints `v + 1` (`mintedTotal > realSpent` — strict inflation),
  * keeps the C7 `value_binding` HONESTLY bound to the leaf (the launder: value IS bound, uselessly),
  * FAILS the value-link check (`¬ linkHolds`, so `verify_value_link` would reject it),
  * and is REJECTED by the linked predicate.
That is the mint: a real `v`-note becomes `v+1`, and only the missing link would stop it. -/
theorem genuine_note_inflates (Bind Wide : Felt → Felt) (Member : Felt → Prop)
    (v : Felt) (hmem : Member v) :
    ∃ t : Transfer,
      accepts Bind Wide Member t ∧
      (∀ i ∈ t.inputs, Member i.leafValue) ∧
      (∀ i ∈ t.inputs, i.valueBinding = Bind i.leafValue) ∧
      realSpent t = v ∧
      mintedTotal t = v + 1 ∧
      mintedTotal t > realSpent t ∧
      ¬ linkHolds t ∧
      ¬ acceptsLinked Bind Wide Member t := by
  obtain ⟨hr, hl, hm⟩ := single_reduces v (v + 1) (Bind v) (Wide v) (v + 1)
  refine ⟨⟨[⟨v, v + 1, Bind v, Wide v⟩], [v + 1]⟩,
          ⟨?_, ?_, ?_, by rw [hl, hm]⟩, ?_, ?_, hr, hm, ?_, ?_, ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact hmem
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact hmem
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl
  · rw [gt_iff_lt, hr, hm]; exact lt_add_one v
  · intro hlink
    have h : (v + 1 : Felt) = v := hlink ⟨v, v + 1, Bind v, Wide v⟩ (by simp)
    exact absurd h (lt_add_one v).ne'
  · rintro ⟨-, hlink⟩
    have h : (v + 1 : Felt) = v := hlink ⟨v, v + 1, Bind v, Wide v⟩ (by simp)
    exact absurd h (lt_add_one v).ne'

/-! ## 4. THE LAUNDER, exposed — the value-link check is faithful, but it is not the deployed gate.

`verify_value_link` (`cell-crypto/src/value_commitment.rs:1655`) checks, for a prover opening `openVal`:
(1) `value_link_binding(openVal) == value_binding` and (2) `commit(openVal, blinding) == leg`. With the
binding injective and `value_binding = Bind leafValue` (C7) and the leg opening to `legValue`, the two
checks pin `openVal = leafValue` and `openVal = legValue`, hence `legValue = leafValue`. So `linkHolds`
IS the check. The Rust test runs it and rejects the mismatch — yet `apply` never calls it. -/

/-- **`verify_value_link_forces_link` (the check IS the link).** `verify_value_link`'s two equations,
under an injective binding, force the leaf↔leg equality that `linkHolds` states — so `linkHolds` is a
faithful model of the deployed-absent check, not an invented predicate. -/
theorem verify_value_link_forces_link
    (Bind : Felt → Felt) (hInj : Function.Injective Bind)
    (leafValue legValue valueBinding openVal : Felt)
    (hC7 : valueBinding = Bind leafValue)          -- the published binding is the leaf's (spend C7)
    (hCheck1 : Bind openVal = valueBinding)         -- verify_value_link (1): value_link_binding == binding
    (hCheck2 : openVal = legValue) :                -- verify_value_link (2): commit(open) == leg ⇒ open = leg value
    legValue = leafValue := by
  have hopen : openVal = leafValue := hInj (hCheck1.trans hC7)
  rw [← hCheck2, hopen]

/-- **`link_test_is_not_the_gate` (the LAUNDER, exposed).** The value-link check (which the test
exercises and passes) rejecting a mismatch does NOT close the theft: the deployed predicate `accepts`
STILL admits an inflating transfer that `linkHolds` rejects. The test and the gate are different teeth;
only the link (folded into acceptance) bites the mint. -/
theorem link_test_is_not_the_gate (Bind Wide : Felt → Felt) (Member : Felt → Prop)
    (v : Felt) (hmem : Member v) :
    ∃ t : Transfer,
      accepts Bind Wide Member t ∧ ¬ linkHolds t ∧ mintedTotal t > realSpent t := by
  obtain ⟨t, hacc, _, _, _, _, hinf, hnl, _⟩ := genuine_note_inflates Bind Wide Member v hmem
  exact ⟨t, hacc, hnl, hinf⟩

/-! ## 5. THE FIX, sound — fold the leaf↔leg link into acceptance.

The single missing conjunct closes it: conservation over the REAL spent values (`acceptsLinked`, §2). -/

/-- **`linked_conservation_over_real_value` (the fix, PURE).** Under the link, the leg total equals the
real spent total, so conservation forces the minted total to equal the real spent value. No floor —
substitution of the pointwise link into the conservation equation. -/
theorem linked_conservation_over_real_value (Bind Wide : Felt → Felt) (Member : Felt → Prop)
    (t : Transfer) (h : acceptsLinked Bind Wide Member t) :
    mintedTotal t = realSpent t := by
  obtain ⟨⟨_, _, _, hcons⟩, hlink⟩ := h
  have hlink' : ∀ i ∈ t.inputs, i.legValue = i.leafValue := hlink
  have hleg : legTotal t = realSpent t := by
    unfold legTotal realSpent
    exact sum_map_congr (fun i => i.legValue) (fun i => i.leafValue) t.inputs hlink'
  rw [← hcons, hleg]

/-- **`linked_no_inflation` (the fix, no-mint form).** Under the link, the minted total does NOT exceed
the real spent value — the inflation the deployed predicate admitted is impossible. -/
theorem linked_no_inflation (Bind Wide : Felt → Felt) (Member : Felt → Prop)
    (t : Transfer) (h : acceptsLinked Bind Wide Member t) :
    ¬ mintedTotal t > realSpent t := by
  have heq := linked_conservation_over_real_value Bind Wide Member t h
  rw [gt_iff_lt, heq]; exact lt_irrefl _

/-- **`link_closes_the_falsifier` (the two halves meet).** The very inflation the deployed predicate
admits (`genuine_note_inflates`) is (a) accepted by the deployed gate with a strict mint, (b) rejected
by the linked predicate directly, and (c) COULD NEVER be linked-accepted, because the link forces the
minted total to equal the real spent value — contradicting the strict inflation. The missing conjunct
is exactly the wound; (c) is the deeper reason the link closes the mint. -/
theorem link_closes_the_falsifier (Bind Wide : Felt → Felt) (Member : Felt → Prop)
    (v : Felt) (hmem : Member v) :
    ∃ t : Transfer,
      accepts Bind Wide Member t ∧
      mintedTotal t > realSpent t ∧
      ¬ acceptsLinked Bind Wide Member t ∧
      (acceptsLinked Bind Wide Member t → False) := by
  obtain ⟨t, hacc, _, _, _, _, hinf, _, hnal⟩ := genuine_note_inflates Bind Wide Member v hmem
  refine ⟨t, hacc, hinf, hnal, ?_⟩
  intro hlinked
  have heq := linked_conservation_over_real_value Bind Wide Member t hlinked
  rw [gt_iff_lt, heq] at hinf
  exact lt_irrefl _ hinf

/-! ## 6. NON-VACUITY — the falsifier and the fix FIRE on a concrete transfer (executable witnesses).

A false `#guard` is a build error. `BindDemo`/`WideDemo` are concrete deterministic stand-ins for the
C7 / wide binding hashes (their only USED property is determinism). The guards check that a genuine
1-token note mints 1_000_000 with conservation passing, that the value-link check fails on it while the
C7 binding stays honest, and that an honest transfer mints exactly what it spends. -/

/-- Concrete deterministic C7 value binding (stand-in for `hash_fact(value,[asset,rand,0])`). -/
def BindDemo (v : Felt) : Felt := v * 7 + 1
/-- Concrete deterministic wide carrier (stand-in for the full-u64 16-felt binding). -/
def WideDemo (v : Felt) : Felt := v * v + 3

/-- The theft input: a genuine note worth 1, whose Pedersen leg claims 1_000_000; bindings honest. -/
def theftInput : Input :=
  { leafValue := 1, legValue := 1000000, valueBinding := BindDemo 1, wideBinding := WideDemo 1 }
def theftTransfer : Transfer := { inputs := [theftInput], outLegs := [1000000] }

/-- An honest transfer: leg value equals leaf value; mints exactly what it spends. -/
def honestInput : Input :=
  { leafValue := 5, legValue := 5, valueBinding := BindDemo 5, wideBinding := WideDemo 5 }
def honestTransfer : Transfer := { inputs := [honestInput], outLegs := [5] }

-- Conservation PASSES on the theft (input leg sum = output leg sum): both 1_000_000.
#guard decide (legTotal theftTransfer = mintedTotal theftTransfer) = true
-- … yet the minted total STRICTLY exceeds the real spent value: 1_000_000 > 1 (INFLATION).
#guard decide (realSpent theftTransfer < mintedTotal theftTransfer) = true
-- The real spent value is just 1; the mint is 1_000_000.
#guard decide (realSpent theftTransfer = 1) = true
#guard decide (mintedTotal theftTransfer = 1000000) = true
-- The value-link check FAILS on the theft (leg ≠ leaf) — `verify_value_link` would reject it.
#guard decide (theftInput.legValue = theftInput.leafValue) = false
-- The launder: the C7 value_binding is HONESTLY bound to the leaf value (real, yet unused by conservation).
#guard decide (theftInput.valueBinding = BindDemo theftInput.leafValue) = true
-- The wide carrier is likewise honestly bound to the leaf value (mandatory, yet unused by conservation).
#guard decide (theftInput.wideBinding = WideDemo theftInput.leafValue) = true
-- The honest transfer: conservation passes AND the mint equals the real spend AND the link holds.
#guard decide (legTotal honestTransfer = mintedTotal honestTransfer) = true
#guard decide (mintedTotal honestTransfer = realSpent honestTransfer) = true
#guard decide (honestInput.legValue = honestInput.leafValue) = true

/-! ## 7. Axiom hygiene. -/

#assert_axioms accepts_of_conservation
#assert_axioms link_rejects_leg_leaf_mismatch
#assert_axioms genuine_note_mints_anything
#assert_axioms genuine_note_inflates
#assert_axioms verify_value_link_forces_link
#assert_axioms link_test_is_not_the_gate
#assert_axioms linked_conservation_over_real_value
#assert_axioms linked_no_inflation
#assert_axioms link_closes_the_falsifier

end Dregg2.Circuit.ShieldedValueLinkPin
