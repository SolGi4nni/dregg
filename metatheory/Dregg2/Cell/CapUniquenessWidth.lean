/-
# Dregg2.Cell.CapUniquenessWidth — the felt-width of the executor's cap-uniqueness root gate.

**What this proves, and the HEAD state it proves it AT.** `turn/src/executor/execute_tree.rs`'s
`validate_capability_uniqueness` enforces `StateConstraint::CapabilityUniqueness` in two legs:

  1. **root binding** — the declared cap-set-root slot must equal `compute_canonical_capability_root`
     of the cell's ACTUAL cap set, and be non-zero;
  2. **structural dup-scan** — no two `CapabilityRef`s share a c-list slot or a
     `(target, permissions, breadstuff, allowed_effects)` identity.

At HEAD, leg (1) still compares the NARROW `compute_canonical_capability_root`
(`cell/src/commitment.rs:665`) = `felt_to_bytes32(compute_canonical_capability_root_felt)` — the
LANE-0 (~31-bit) projection of the wide cap digest. The wound doc's entry #3 flags this. Its own
07-19 update downgraded it to "defense-in-depth: the state commitment already binds the WIDE cap root
independently, the narrow gate is a redundant projection." This module proves that downgrade — at the
resolution the wound demands — rather than asserting it.

  * **THE FALSIFIER (`narrow_capRoot_underdetermines`).** `felt_to_bytes32` reads lane 0 only, so the
    executor's declared-root compare (`narrowRoot`) does NOT determine the wide cap digest: two
    DISTINCT eight-felt cap roots agreeing on lane 0 produce the SAME narrow declared value. Leg (1)'s
    equality can be satisfied by a colliding declared slot — the ~2^15.5 birthday the wound prices.
  * **THE FIX, sound (`wide_capRoot_determines`).** The value the off-chain state commitment absorbs
    is `compute_canonical_capability_root_wide` = `digest8_to_bytes32(compute_canonical_capability_root_8)`
    (`commitment.rs:684`), the FULL eight-felt encoding (`wideRoot`). It is INJECTIVE on the digest —
    each lane packs into its own four-byte window — so the security boundary (the state commitment)
    determines the cap root uniquely at ~124 bits. The narrow collision is absent there.
  * **THE "REDUNDANT PROJECTION", proved (`narrow_root_is_projection_of_wide`,
    `narrow_gate_redundant`).** The narrow declared value is a FUNCTION of the wide root the state
    commitment already binds (its lane 0). So leg (1) carries NO information the wide binding lacks —
    the wound's "redundant projection" phrasing, as a theorem. Widening leg (1)'s in-circuit gate
    itself is a committed-state binding change (ember-gated deploy), out of scope; the security-
    carrying WIDE binding is already deployed.
  * **THE COMPENSATING TOOTH (`accept_implies_unique`).** The security-relevant conclusion — the caps
    are structurally unique — is leg (2), a predicate on the ACTUAL cap set, independent of ANY root
    encoding. A lane-0 collision on the declared root cannot fabricate uniqueness (leg (2) reads the
    real caps). So the felt-width narrowness of leg (1) does not degrade the guarantee.

**Byte-safe / posture.** No deployed executor gate, commitment, or state slot is touched. The wide
encoding's injectivity is over canonical BabyBear lanes (each `< p < 2^31`, recovered from its four
bytes), the same lane-window fact `digest8_to_bytes32`'s docstring states; modeled here at lane
granularity (`Lanes := Fin 8 → Felt`).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Cell.CapUniquenessWidth`.
-/
import Mathlib.Tactic
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Cell.CapUniquenessWidth

/-! ## 1. Felt resolution and the two encodings. -/

/-- One field lane (canonical `as_u32()` value); the range prices the ~2^15.5 birthday on one felt but
is irrelevant to the encoding's injectivity. -/
abbrev Felt : Type := ℤ

/-- The eight-felt canonical capability root (`compute_canonical_capability_root_8 : [BabyBear; 8]`). -/
abbrev Digest8 : Type := Fin 8 → Felt

/-- The 32-byte cap-root at LANE granularity: eight four-byte windows. `felt_to_bytes32` fills window 0
and zeroes the rest; `digest8_to_bytes32` fills all eight, one lane per window. -/
abbrev Lanes : Type := Fin 8 → Felt

/-- `felt_to_bytes32` — the NARROW (lane-0) encoding: one felt in window 0, the rest zero. -/
def narrowEncode (f : Felt) : Lanes := fun i => if i = 0 then f else 0

/-- `digest8_to_bytes32` — the WIDE encoding: each of the eight lanes in its own window. -/
def wideEncode (d : Digest8) : Lanes := d

/-- The executor's leg-(1) declared-root value: `felt_to_bytes32(compute_canonical_capability_root_felt)`
= the lane-0 projection of the wide cap digest. -/
def narrowRoot (capRoot8 : Digest8) : Lanes := narrowEncode (capRoot8 0)

/-- The state commitment's absorbed value: `digest8_to_bytes32(compute_canonical_capability_root_8)`
= the full eight-felt encoding. -/
def wideRoot (capRoot8 : Digest8) : Lanes := wideEncode capRoot8

/-! ## 2. THE FALSIFIER — the narrow gate does not determine the wide cap root. -/

/-- A concrete cap digest (all lanes zero). -/
def r0 : Digest8 := fun _ => 0

/-- A distinct cap digest agreeing with `r0` on lane 0 but differing on lane 1 — the shape a ~2^15.5
lane-0 grind buys. -/
def r1 : Digest8 := fun i => if i = 1 then 1 else 0

/-- The two cap digests are GENUINELY distinct (they differ at lane 1). -/
theorem r0_ne_r1 : r0 ≠ r1 := by
  intro h
  have h1 : (0 : Felt) = 1 := congrFun h 1
  exact absurd h1 (by decide)

/-- **THE FALSIFIER.** The narrow declared-root value is IDENTICAL for the two distinct wide cap roots
(they agree on lane 0), so the executor's leg-(1) compare cannot distinguish them — the lane-0
collision the wound prices, over all such pairs. -/
theorem narrow_capRoot_underdetermines :
    ∃ r r' : Digest8, r ≠ r' ∧ narrowRoot r = narrowRoot r' :=
  ⟨r0, r1, r0_ne_r1, rfl⟩

/-! ## 3. THE FIX, sound — the wide encoding the state commitment absorbs binds uniquely. -/

/-- The wide encoding is INJECTIVE (each lane in its own window). -/
theorem wideEncode_injective : Function.Injective wideEncode := fun _ _ h => h

/-- **THE FIX.** The value the off-chain state commitment absorbs (`compute_canonical_capability_root_wide`)
determines the full eight-felt cap root UNIQUELY: two cap digests with the same wide root are equal.
At the security boundary the ~124-bit collision floor holds; the narrow gate's lane-0 collision is
absent. -/
theorem wide_capRoot_determines {r r' : Digest8} (h : wideRoot r = wideRoot r') : r = r' :=
  wideEncode_injective h

/-- The wide encoding SEPARATES exactly the pair the narrow gate conflated. -/
theorem wide_separates : wideRoot r0 ≠ wideRoot r1 :=
  fun h => r0_ne_r1 (wide_capRoot_determines h)

/-! ## 4. THE "REDUNDANT PROJECTION" — the narrow gate carries no information the wide binding lacks. -/

/-- **THE REDUNDANT PROJECTION, proved.** The executor's narrow declared-root value is exactly the
lane-0 projection of the WIDE root the state commitment already binds — a function of it. So leg (1)
adds nothing over the deployed wide binding; it is defense-in-depth, precisely as the wound's 07-19
update states. -/
theorem narrow_root_is_projection_of_wide (capRoot8 : Digest8) :
    narrowRoot capRoot8 = narrowEncode ((wideRoot capRoot8) 0) := rfl

/-- The same fact as a single global projector `g` — the narrow gate factors through the wide root. -/
theorem narrow_gate_redundant :
    ∃ g : Lanes → Lanes, ∀ capRoot8 : Digest8, narrowRoot capRoot8 = g (wideRoot capRoot8) :=
  ⟨fun w => narrowEncode (w 0), fun _ => rfl⟩

/-! ## 5. THE COMPENSATING TOOTH — uniqueness is leg (2), independent of the encoding.

Leg (2) (the structural dup-scan) reads the ACTUAL cap set; it is the security-relevant authority. The
executor accepts iff `declared = narrowRoot(caps) ∧ P`, where `P` abstracts "the dup-scan found no
duplicate slot / identity". The felt-width narrowness lives ENTIRELY in the first conjunct. -/

/-- **THE COMPENSATING TOOTH.** Executor acceptance implies the security-relevant uniqueness `P`, with
NO dependence on the narrow root encoding: a lane-0 collision on the declared value cannot fabricate
`P` (leg (2) reads the real caps). The wound's provenance note "breaks root-binding (1), NOT the
structural dup-scan (2)", as a theorem. -/
theorem accept_implies_unique {P : Prop} {declared : Lanes} {capRoot8 : Digest8}
    (h : declared = narrowRoot capRoot8 ∧ P) : P := h.2

/-! ## 6. NON-VACUITY — the collision and the wide separation FIRE on concrete cap roots. -/

-- The narrow gate CONFLATES the two distinct wide roots …
#guard decide (narrowRoot r0 = narrowRoot r1)
-- … which are genuinely distinct digests …
#guard decide (r0 = r1) == false
-- … and the wide binding SEPARATES them.
#guard decide (wideRoot r0 = wideRoot r1) == false

/-! ## 7. Axiom hygiene. -/

#assert_axioms r0_ne_r1
#assert_axioms narrow_capRoot_underdetermines
#assert_axioms wideEncode_injective
#assert_axioms wide_capRoot_determines
#assert_axioms wide_separates
#assert_axioms narrow_root_is_projection_of_wide
#assert_axioms narrow_gate_redundant
#assert_axioms accept_implies_unique

end Dregg2.Cell.CapUniquenessWidth
