/-
# Dregg2.Circuit.ShieldedWideJoinPin — the ring↔wide value-join is a ~31-bit `legacy_binding`
  squeeze, NOT a same-opening (C5 DARK-VALUE v4, the sidecar-decouple vector).

**What this proves, and why it was missing.** The shielded exact-spend path joins TWO proofs whose
value coordinates must agree:

  * the **wide carrier** (`circuit-prove/src/shielded/wide_value_binding.rs`) commits the FULL-`u64`
    `(value, asset)` opening: four 16-bit limbs each, bit-constrained, two domain-separated `node8`
    Poseidon2 images over the complete limbs plus seven blinding lanes (`WIDE_VALUE_BINDING_LANES = 16`).
    Its own AIR ALSO recomputes the legacy one-felt binding from those limbs (`col::LEGACY_BINDING`,
    `wide_value_binding.rs:12-14,62`), so WITHIN that proof wide and legacy agree.
  * the **ring / conservation proof** (`shielded_ring_clearing_air.rs`, per-leg claim
    `[nullifier, merkle_root, value_binding]`, `RING_LEG_CLAIM_LEN = 3`) exposes only the ONE-felt
    `value_binding` as the join slot.

  * **the join is ONE felt.** `apply_shielded_transfer` reconstructs the wide carrier from
    `input.legacy_value_binding` and the ring/spend proof from that SAME `legacy_value_binding`
    (`turn/src/executor/apply.rs:1723-1743`). The two proofs are tied to each other ONLY by
    felt-equality on the ~31-bit `legacy_binding`. As HORIZONLOG (2026-07-22) states it: *"The present
    ring↔wide sidecar join is only one BabyBear `legacy_binding` (~31 bits), not a cryptographic
    same-opening; v4 must share one witness or a faithful full-width commitment across both proofs."*

So a malicious prover picks two DISTINCT full-width openings `o₁ ≠ o₂` whose `legacy_binding` felts
collide (birthday-cheap at ~2^15.5, chosen at ~2^31 — the `legacy_binding` reduces `value`/`asset`
modulo BabyBear `p` and squeezes to one felt, so distinct `u64` values alias): let the **ring** proof
conserve `o₁` (the value that actually moves) while the **wide carrier** advertises `o₂` (the "dark
value" the receipt binds). The join accepts because the two share a `legacy_binding` felt — yet
`o₁.value ≠ o₂.value`. The carrier's dark value is decoupled from the value the conservation clears.
This is the C5 wound: the sidecar join is not a same-opening.

**The LAUNDER, exposed.** The wide carrier is *internally faithful* — its 16-lane image distinguishes
every `(value, asset)` in the `u64×u64` domain, and a reader who audits `wide_value_binding.rs`
concludes "the value is bound full-width." It is — inside that one proof. But the RING proof never
consumes the 16 wide lanes; it consumes the single `legacy_binding` felt. A binding the join does not
use buys nothing: the wide carrier can bind `o₂` while the ring conserves `o₁`.

**What is proved here** (theorems over ALL inputs; the binds are ABSTRACT deterministic functions —
the statements hold for the real Poseidon2 carrier and the real BabyBear squeeze):

  * **THE FALSIFIER (`narrow_join_admits_dark_value_decouple`, `dark_value_decouples`).** The deployed
    join — equality on the narrow `legacy_binding` alone — accepts a ring/carrier pair whose full-width
    values DIFFER, whenever the squeeze has a value-distinct collision (which the ~31-bit squeeze does:
    `demo_narrow_collides`). The carrier's advertised value is not the value that conserves.
  * **THE LAUNDER, exposed (`wide_carrier_internally_faithful` vs `join_still_decouples`).** Even with
    the wide carrier's own binding injective on the openings (internally faithful), the *narrow join*
    STILL admits the decouple — the wide lanes are not what the ring consults.
  * **THE FIX A — share one witness (`shared_witness_forbids_decouple`).** If the join runs over ONE
    opening cell feeding both proofs (`ringOpen = wideOpen` by construction), the values are forced
    equal — the same-opening becomes literally one opening; the decouple is unrepresentable.
  * **THE FIX B — a faithful full-width join (`wide_join_forces_same_opening`, `wide_join_same_value`).**
    Joining on the injective WIDE binding instead of the narrow felt forces `ringOpen = wideOpen` (hence
    equal value), under the wide carrier's collision-resistance floor NAMED as `Function.Injective`.
  * **THE HONEST OBLIGATION, named (`CrossSchemeSameOpening`, `cross_scheme_join_needs_argument`).** If
    the two proofs keep DIFFERENT commitment schemes (the ring's conservation representation vs the wide
    Poseidon carrier — e.g. Ristretto Pedersen vs `node8`), tying them is a genuine SAME-OPENING
    ARGUMENT — a proof obligation `RingCommit`/`WideCommit` open to the same `(value, asset)` — never a
    wiring step. It enters as a NAMED hypothesis; it is the crypto work v4 owes, not free.

**Byte-safe / posture.** This module touches NO deployed code and NO descriptor. It is the machine-checked
statement of the C5 wound (the narrow sidecar join decouples the dark value) and of what each v4 fix buys:
sharing one witness (Fix A) dispatches the same-opening obligation *by collapse*; a faithful full-width
join (Fix B) discharges it under the wide-hash CR floor; keeping two schemes leaves a genuine
same-opening argument (the honest crypto obligation). It is the C5 twin of `ShieldedValueLinkPin` (which
priced the leaf↔leg link at ONE felt) lifted to the ring↔wide join, and of `Cell/InterfaceIdWidth`'s
`narrow_conflates`/`wideId_injective` shape.

**Scope (honest).** At the resolution of the ring↔wide value-join trust boundary — NOT the full v4 AIR.
The hiding substrate (FWS1 / HidingFRI whole-note-swap, `shielded-whole-note-swap-substrate-v1`) and the
wide carrier itself already exist; what is genuinely NEW is the same-opening BINDING relation this
module states and its two discharges. The full v4 apex (the 19+27 FXC4 consequence, output-note
transaction, selector/persistence, committee authority; `shielded_exact_apex_v4.rs`) and the emit/route
of the shared-witness clearing descriptor are the campaign residual.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Circuit.ShieldedWideJoinPin`.
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Circuit.ShieldedWideJoinPin

/-! ## 1. A full-width note opening, the narrow squeeze, and the wide carrier.

One field element per lane (the `u64` domain lands in ℤ, as in `ShieldedValueLinkPin` /
`InterfaceIdWidth` — the offline grind is priced elsewhere; here the gap is the value-JOIN, not the
per-lane width). An `Opening` is the `(value, asset)` the note commits; `.value` is the amount the
conservation must clear and the wide carrier must advertise. -/

/-- A full-width note opening: `(value, asset)`. -/
structure Opening where
  value : ℤ
  asset : ℤ
deriving DecidableEq, Repr

/-- The DEPLOYED join key: the ~31-bit `legacy_binding` felt (abstract deterministic squeeze). The
wound is that it is NOT injective on `Opening` — distinct full-width openings alias to one felt. -/
abbrev Narrow : Type := Opening → ℤ

/-- The faithful full-width carrier (abstract). Fix B's floor is `Function.Injective` on it — the wide
`node8` image distinguishing every `(value, asset)` pair, under Poseidon2 collision-resistance. -/
abbrev Wide : Type := Opening → ℤ

/-! ## 2. The DEPLOYED join — equality on the narrow `legacy_binding` alone.

Faithful to `apply_shielded_transfer` at HEAD: the ring/spend proof and the wide carrier are both
reconstructed from `input.legacy_value_binding` (`apply.rs:1723-1743`), so the ONLY constraint tying
`ringOpen` to `wideOpen` is `NarrowBind ringOpen = NarrowBind wideOpen`. Nothing forces their values
to agree. -/

/-- The deployed join predicate: the ring proof's opening and the wide carrier's opening share a
`legacy_binding` felt. This is the whole tie between the two proofs. -/
def joinedNarrow (NarrowBind : Narrow) (ringOpen wideOpen : Opening) : Prop :=
  NarrowBind ringOpen = NarrowBind wideOpen

/-- The SOUND join (Fix B): the openings share the WIDE binding — a faithful full-width tie. -/
def joinedWide (WideBind : Wide) (ringOpen wideOpen : Opening) : Prop :=
  WideBind ringOpen = WideBind wideOpen

/-- **`narrow_join_ignores_value` (the wound in one line).** The deployed join is decided entirely by
the narrow felts; it never looks at the openings' values. So whatever value the ring conserves, a
carrier opening with a matching `legacy_binding` is accepted on its own. -/
theorem narrow_join_ignores_value (NarrowBind : Narrow) (ringOpen wideOpen : Opening) :
    joinedNarrow NarrowBind ringOpen wideOpen ↔ NarrowBind ringOpen = NarrowBind wideOpen := Iff.rfl

/-! ## 3. THE FALSIFIER — the narrow join decouples the dark value.

Given ANY value-distinct collision of the squeeze (`o₁.value ≠ o₂.value` yet
`NarrowBind o₁ = NarrowBind o₂`), the ring conserves `o₁` while the carrier advertises `o₂`: the join
accepts, the dark value the carrier binds is not the value that moves. -/

/-- **`narrow_join_admits_dark_value_decouple` (THE FALSIFIER).** For any narrow squeeze with a
value-distinct collision, there is a ring opening and a wide-carrier opening that the deployed join
ACCEPTS while their conserved/advertised values DIFFER. -/
theorem narrow_join_admits_dark_value_decouple (NarrowBind : Narrow)
    (hcol : ∃ o₁ o₂ : Opening, o₁.value ≠ o₂.value ∧ NarrowBind o₁ = NarrowBind o₂) :
    ∃ ringOpen wideOpen : Opening,
      joinedNarrow NarrowBind ringOpen wideOpen ∧ ringOpen.value ≠ wideOpen.value := by
  obtain ⟨o₁, o₂, hval, hbind⟩ := hcol
  exact ⟨o₁, o₂, hbind, hval⟩

/-- **`dark_value_decouples` (THE FALSIFIER, theft form — the whole shape at once).** The ring
conserves `ringOpen.value` (the value that moves) while the wide carrier's PI advertises a strictly
larger dark value `wideOpen.value`, and the deployed narrow join ACCEPTS the pair. Only a same-opening
tie would stop it. -/
theorem dark_value_decouples (NarrowBind : Narrow)
    (hcol : ∃ o₁ o₂ : Opening, o₁.value ≠ o₂.value ∧ NarrowBind o₁ = NarrowBind o₂) :
    ∃ ringOpen wideOpen : Opening,
      joinedNarrow NarrowBind ringOpen wideOpen ∧
      ringOpen.value ≠ wideOpen.value ∧
      ¬ (ringOpen = wideOpen) := by
  obtain ⟨ringOpen, wideOpen, hj, hval⟩ := narrow_join_admits_dark_value_decouple NarrowBind hcol
  refine ⟨ringOpen, wideOpen, hj, hval, ?_⟩
  intro h; exact hval (by rw [h])

/-! ## 4. THE LAUNDER, exposed — the wide carrier is internally faithful, but the join is narrow.

A reader audits `wide_value_binding.rs`, sees the 16-lane full-`u64` image, and concludes "value is
bound." It is — inside that proof. But the ring proof consumes only the narrow felt, so the decouple
survives even when the wide binding is injective. -/

/-- The wide carrier's own binding is FAITHFUL: injective on openings (its 16-lane `node8` image
distinguishes every `(value, asset)`). Modeled as `Function.Injective WideBind` — the honest reading
of `wide_value_binding.rs`. -/
def WideCarrierFaithful (WideBind : Wide) : Prop := Function.Injective WideBind

/-- **`join_still_decouples` (the LAUNDER, exposed).** Even when the wide carrier is internally
faithful, the NARROW join still admits a dark-value decouple: the wide lanes are not what the ring
consults. Internal faithfulness of the carrier does not close the join. -/
theorem join_still_decouples (NarrowBind : Narrow) (WideBind : Wide)
    (_faithful : WideCarrierFaithful WideBind)
    (hcol : ∃ o₁ o₂ : Opening, o₁.value ≠ o₂.value ∧ NarrowBind o₁ = NarrowBind o₂) :
    ∃ ringOpen wideOpen : Opening,
      joinedNarrow NarrowBind ringOpen wideOpen ∧ ringOpen.value ≠ wideOpen.value :=
  narrow_join_admits_dark_value_decouple NarrowBind hcol

/-! ## 5. FIX A — share one witness: `ringOpen = wideOpen` by construction.

The v4 shared-witness shape: ONE hidden `(value, asset)` cell feeds BOTH the wide carrier hash and the
ring conservation. There is no second opening to decouple — the same-opening is literally one opening. -/

/-- **`shared_witness_forbids_decouple` (Fix A, PURE).** If both proofs consume the SAME opening cell,
the ring-conserved value and the carrier-advertised value are equal — the decouple is unrepresentable.
No floor: substitution. -/
theorem shared_witness_forbids_decouple (o ringOpen wideOpen : Opening)
    (hr : ringOpen = o) (hw : wideOpen = o) : ringOpen.value = wideOpen.value := by
  rw [hr, hw]

/-- **`shared_witness_join_is_reflexive` (Fix A, join form).** Under a shared witness the join holds
for FREE for any narrow squeeze — because there is only one opening, so there is nothing to reconcile.
The security is that the value is shared, not that the felts happen to match. -/
theorem shared_witness_join_is_reflexive (NarrowBind : Narrow) (o : Opening) :
    joinedNarrow NarrowBind o o := rfl

/-! ## 6. FIX B — a faithful full-width join: tie on the injective WIDE binding.

Instead of the narrow felt, join on the 16-lane wide binding. Under its collision-resistance (modeled
as injectivity), a shared wide binding forces a shared opening — same-opening as a THEOREM. -/

/-- **`wide_join_forces_same_opening` (Fix B, sound).** Under the wide carrier's collision-resistance
floor (`Function.Injective WideBind`), the wide join forces the two openings equal. -/
theorem wide_join_forces_same_opening (WideBind : Wide) (hInj : Function.Injective WideBind)
    (ringOpen wideOpen : Opening) (h : joinedWide WideBind ringOpen wideOpen) :
    ringOpen = wideOpen := hInj h

/-- **`wide_join_same_value` (Fix B, value form).** Hence the wide join forces the conserved value to
equal the carrier's advertised value: the dark-value decouple is closed. -/
theorem wide_join_same_value (WideBind : Wide) (hInj : Function.Injective WideBind)
    (ringOpen wideOpen : Opening) (h : joinedWide WideBind ringOpen wideOpen) :
    ringOpen.value = wideOpen.value := by
  rw [wide_join_forces_same_opening WideBind hInj ringOpen wideOpen h]

/-- **`wide_join_rejects_the_falsifier` (the two halves meet).** The very decouple the narrow join
admits — distinct-value openings sharing a `legacy_binding` felt — could NEVER pass the wide join: a
faithful wide binding would force the openings (hence values) equal, contradicting the decouple. -/
theorem wide_join_rejects_the_falsifier (WideBind : Wide) (hInj : Function.Injective WideBind)
    (ringOpen wideOpen : Opening) (hval : ringOpen.value ≠ wideOpen.value) :
    ¬ joinedWide WideBind ringOpen wideOpen := by
  intro h; exact hval (wide_join_same_value WideBind hInj ringOpen wideOpen h)

/-! ## 7. THE HONEST OBLIGATION — keeping two schemes needs a same-opening ARGUMENT.

If the ring's conservation representation and the wide carrier stay DIFFERENT commitment schemes
(Ristretto Pedersen vs Poseidon `node8`), tying them is not a wiring step: it is a proof that the two
open to the SAME `(value, asset)`. It enters as a NAMED hypothesis — the crypto work v4 owes. -/

/-- The cross-scheme same-opening RELATION, named (never a `def`-used-as-proof). Given a ring-side
commitment `RingCommit` and a wide-side commitment `WideCommit`, this asserts that agreement on BOTH
forces one opening. Discharging it for genuinely different schemes is a real argument (a sigma protocol
/ equality-of-committed-value proof), NOT free. -/
def CrossSchemeSameOpening (RingCommit WideCommit : Wide) : Prop :=
  ∀ ringOpen wideOpen : Opening,
    RingCommit ringOpen = RingCommit wideOpen →
    WideCommit ringOpen = WideCommit wideOpen →
    ringOpen = wideOpen

/-- **`cross_scheme_join_needs_argument` (the obligation stated).** GIVEN the same-opening argument
(the named crypto obligation) and agreement on both scheme commitments, the values agree. The point is
the HYPOTHESIS: without discharging `CrossSchemeSameOpening`, a two-scheme join proves nothing about
value equality. This is what dies when v4 shares one witness (Fix A) or moves to one faithful binding
(Fix B) — the argument is dispatched by collapse or by injectivity, not carried. -/
theorem cross_scheme_join_needs_argument (RingCommit WideCommit : Wide)
    (arg : CrossSchemeSameOpening RingCommit WideCommit) (ringOpen wideOpen : Opening)
    (hr : RingCommit ringOpen = RingCommit wideOpen)
    (hw : WideCommit ringOpen = WideCommit wideOpen) :
    ringOpen.value = wideOpen.value := by
  rw [arg ringOpen wideOpen hr hw]

/-! ## 8. NON-VACUITY — the squeeze REALLY has value-distinct collisions; the wide bind separates them.

A false `#guard` is a build error. `demoNarrow` is a concrete stand-in for the `legacy_binding`
squeeze (reduce the value modulo a small modulus — the shape of "reduce `u64` mod BabyBear `p` and
squeeze to one felt"); `demoWide` is a concrete full-width bind that DISTINGUISHES the pair the squeeze
conflates (the 16-lane carrier's job). -/

/-- A concrete narrow squeeze: reduce the value modulo 5 (the shape of the modular `legacy_binding`
squeeze — distinct values alias). -/
def demoNarrow : Narrow := fun o => o.value % 5

/-- A concrete faithful full-width bind: separates value from asset with a big stride (distinguishes
the colliding pair). -/
def demoWide : Wide := fun o => o.value * 1000 + o.asset

/-- Two openings with DIFFERENT values (1 vs 6) that the narrow squeeze conflates. -/
def oRing : Opening := ⟨1, 0⟩
def oWide : Opening := ⟨6, 0⟩

-- The two openings have DISTINCT values (the ring conserves 1; the carrier advertises 6).
#guard decide (oRing.value ≠ oWide.value) = true
-- … yet the narrow squeeze CONFLATES them: 1 % 5 = 1, 6 % 5 = 1 — the deployed join ACCEPTS.
#guard decide (demoNarrow oRing = demoNarrow oWide) = true
-- The wide carrier SEPARATES the pair: 1·1000+0 ≠ 6·1000+0 — Fix B's faithful join would reject.
#guard decide (demoWide oRing ≠ demoWide oWide) = true
-- The demo squeeze therefore witnesses a value-distinct collision — the falsifier's hypothesis is real.
#guard decide (oRing.value ≠ oWide.value ∧ demoNarrow oRing = demoNarrow oWide) = true

/-- The demo squeeze exhibits the value-distinct collision the falsifier consumes — so the falsifier is
about an INHABITED situation, not an empty one. -/
theorem demo_narrow_collides :
    ∃ o₁ o₂ : Opening, o₁.value ≠ o₂.value ∧ demoNarrow o₁ = demoNarrow o₂ :=
  ⟨oRing, oWide, by decide, by decide⟩

/-- **The falsifier FIRES on the concrete squeeze** — the deployed narrow join accepts a real
dark-value decouple. Non-vacuity of `dark_value_decouples`. -/
theorem falsifier_fires_on_demo :
    ∃ ringOpen wideOpen : Opening,
      joinedNarrow demoNarrow ringOpen wideOpen ∧
      ringOpen.value ≠ wideOpen.value ∧ ¬ (ringOpen = wideOpen) :=
  dark_value_decouples demoNarrow demo_narrow_collides

/-! ## 9. Axiom hygiene. -/

#assert_axioms narrow_join_ignores_value
#assert_axioms narrow_join_admits_dark_value_decouple
#assert_axioms dark_value_decouples
#assert_axioms join_still_decouples
#assert_axioms shared_witness_forbids_decouple
#assert_axioms shared_witness_join_is_reflexive
#assert_axioms wide_join_forces_same_opening
#assert_axioms wide_join_same_value
#assert_axioms wide_join_rejects_the_falsifier
#assert_axioms cross_scheme_join_needs_argument
#assert_axioms demo_narrow_collides
#assert_axioms falsifier_fires_on_demo

end Dregg2.Circuit.ShieldedWideJoinPin
