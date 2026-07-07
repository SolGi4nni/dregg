/-
# Dregg2.Circuit.Emit.PresentationEmit — the emit-from-Lean face of the `presentation` family
(`circuit/src/presentation.rs`): the token-presentation summary AIR + its off-AIR FRESHNESS
binding, internalized as an IR-v2 descriptor.

## What this file IS (and why it is NOT a mirror)

The deployed hand AIR (`PresentationAir::constraints`, `presentation.rs:807–818`) enforces ONLY a
19-column copy check: `row[i] == public_inputs[i]` over the summary
`{federation_root(1), request_predicate(8), timestamp(1), presentation_tag(1),
revealed_facts_commitment(8)}` (`SUMMARY_WIDTH = 19`). ALL of the presentation's real security
lives in plaintext Rust `PresentationProof::verify` (`presentation.rs:224–283`): fold-chain
continuity, derivation-root binding, issuer-federation membership, temporal binding, the
presentation-tag hash, and the FRESHNESS binding. A descriptor that mirrored ONLY the 19-column
copy would be trivial and internalize NONE of that security — the pre-law violation.

This descriptor is faithful to the literal hand AIR (the 19 summary `.piBinding` copies) AND
internalizes the one off-AIR check that is a self-contained arithmetic tooth: the FRESHNESS
binding (`verify_freshness_binding`, `presentation.rs:316–345`).

## The freshness tooth (the load-bearing edge internalized here)

`verify_freshness_binding` rejects (`TokenExpired`) iff, with both heights non-zero,
`(not_after_height − verifier_block_height).as_u32() > 1_006_632_960` — i.e. it ACCEPTS exactly
`diff := not_after − verifier ∈ [0, p/2]`, where `p/2 = 1_006_632_960` (`p = 2013265921`). This is
`not_after ≥ verifier` read as a "small non-negative field difference" (a `not_after < verifier`
wraps `diff` to `p − (verifier − not_after)`, far above `p/2`).

`p/2` is NOT a power of two (`2^29 < p/2 < 2^30`), so a single `Range{bits}` cannot express
`diff ≤ p/2`. This descriptor uses the EXACT less-than-constant gadget: witness `hi := p/2 − diff`
and prove BOTH `diff ∈ [0, 2^30)` and `hi ∈ [0, 2^30)` (two `Range{30}` lookups) with
`diff + hi = p/2` (a base gate). Soundness: `diff, hi < 2^30 ⇒ diff + hi < 2^31 < p/2 + p`, so the
field equation `diff + hi ≡ p/2 (mod p)` forces the INTEGER sum `diff + hi = p/2`, hence
`diff ≤ p/2` (`freshness_bound_sound` below). The two teeth bite the two failure regions: a wrapped
`diff` (near `p`) fails its own range; an in-`[0,2^30)`-but-`> p/2` `diff` forces `hi < 0 ⇒ hi = p − …`
which fails the `hi` range.

## Constraint map (hand `presentation.rs` → IR-v2 here)

| hand check                                                    | IR-v2 constraint                       |
|---------------------------------------------------------------|----------------------------------------|
| 19 summary copies `row[i] == pi[i]` (`constraints()` @807)    | 19 × `.base (.piBinding .first i i)`   |
| `verifier_block_height` is the public anchor (`verify` @317)  | `.base (.piBinding .first VERIFIER 19)`|
| `diff = not_after − verifier` (`verify_freshness_binding` @338)| `.base (.gate …)` (diff-binding)      |
| `hi = p/2 − diff`, i.e. `diff + hi = p/2` (the `≤ p/2` bound)  | `.base (.gate …)` (bound)             |
| `diff ∈ [0, 2^30)`                                             | `.lookup ⟨.range, [diff]⟩`             |
| `hi ∈ [0, 2^30)` (closes the exact `p/2`, non-power-of-two)   | `.lookup ⟨.range, [hi]⟩`               |

## The NAMED gates (executor-verified recursion carriers, left off-descriptor by design)

Per the `FITS_WITH_NAMED_GATE` verdict, the following `verify()` checks are NOT internalized here —
they ride the named recursion/STARK-leaf argument (DECO-leaf posture) and are verified by the
executor, exactly as the descriptor's chip/range lookups ride the LogUp bus rather than a row-local
poly. `not_after_height` itself is a value PUBLISHED by the derivation leaf; this descriptor binds
the freshness ARITHMETIC over it and names the leaf that furnishes it:
  - fold-chain continuity + derivation-root binding (`verify` @239–255) — recursion `ProofBind`;
  - issuer Merkle membership in the federation (STARK sub-proof, `verify` @263–267);
  - temporal-predicate STARKs (`verify_temporal_proofs` @357–378);
  - the presentation-tag hash `tag = hash_many(compute_presentation_tag(final_root, r, nonce))`
    (`binding.rs:345`, a two-stage Poseidon2 sponge — "enforced by the STARK internally", `verify`
    @258): a Poseidon2Chip sub-descriptor, not a row-local tooth of THIS AIR.

## The byte-pin and the Rust gate

`emitVmJson2 presentationFreshnessDesc` is BYTE-PINNED below (`#guard`). The Rust gate
(`circuit-prove/tests/presentation_emit_gate.rs`) decodes this exact string via
`parse_vm_descriptor2`, asserts it EQUALS an independently hand-built descriptor, proves an HONEST
fresh-token witness through the REAL `prove_vm_descriptor2` / `verify_vm_descriptor2` (ACCEPT), and
runs mutation canaries that each bite a distinct constraint: a wrapped (expired) `diff` → the diff
`Range` tooth; an in-`[0,2^30)`-but-`> p/2` `diff` → the `hi` `Range` tooth (the EXACT `p/2` bound);
an in-range but inconsistent `diff` → the diff-binding gate; a forged summary PI → a summary copy;
a forged `verifier_block_height` PI → the freshness public anchor.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + genuinely-proven,
non-vacuous semantic lemmas (`diffBind_body_zero_iff`, `bound_body_zero_iff`,
`freshness_bound_sound` — each TRUE iff its identity holds / the gadget is sound). `#assert_axioms`
⊆ {} (pure `omega`). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.PresentationEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows)

set_option autoImplicit false

/-! ## §1 — The trace column layout (a single logical row, repeated to a power-of-two height).

The 19 summary columns mirror `PresentationAir::trace_width` (`presentation.rs:801–810`), then the
four freshness columns. The range-decomposition limbs for `DIFF`/`HI` are NOT base columns — the
assembler appends `decomp_cols(30)` limbs per range lookup past `trace_width`. -/

/-- Summary col 0: `federation_root`. -/
def FEDERATION_ROOT : Nat := 0
/-- Summary cols 1..8: `request_predicate` (ACTION_BINDING_WIDTH = 8 felts). -/
def REQUEST_PREDICATE_BASE : Nat := 1
/-- Summary col 9: `timestamp`. -/
def TIMESTAMP : Nat := 9
/-- Summary col 10: `presentation_tag` (narrow; its HASH well-formedness is a named STARK leaf). -/
def PRESENTATION_TAG : Nat := 10
/-- Summary cols 11..18: `revealed_facts_commitment` (WideHash::WIDTH = 8 felts). -/
def REVEALED_FACTS_BASE : Nat := 11

/-- The deployed summary width (`presentation.rs::SUMMARY_WIDTH = 1 + 8 + 1 + 1 + 8`). -/
def SUMMARY_WIDTH : Nat := 19

/-- Freshness col 19: `verifier_block_height` (the public anchor; PI-bound). -/
def VERIFIER : Nat := 19
/-- Freshness col 20: `not_after_height` (published by the named derivation leaf). -/
def NOT_AFTER : Nat := 20
/-- Freshness col 21: `diff = not_after − verifier`; range-proved into `[0, 2^30)`. -/
def DIFF : Nat := 21
/-- Freshness col 22: `hi = p/2 − diff`; range-proved into `[0, 2^30)` (closes the exact bound). -/
def HI : Nat := 22

/-- Total base-trace width (23 = 19 summary + 4 freshness; range limbs are appended). -/
def PRES_WIDTH : Nat := 23

/-- Public-input slot for the `verifier_block_height` anchor (after the 19 summary PIs). -/
def PI_VERIFIER : Nat := 19

/-- Number of public inputs: the 19 summary slots + the verifier-height anchor. -/
def PI_COUNT : Nat := 20

/-- The freshness limb width. `p/2 = 1_006_632_960 < 2^30`, so `DIFF`/`HI` fit in 30-bit limbs;
30 is also the deployed canonical limb width (`BAL_LIMB_BITS`). -/
def FRESH_BITS : Nat := 30

/-- The freshness acceptance bound `p/2` (`presentation.rs:341`, `p = 2013265921`). -/
def HALF_P : ℤ := 1006632960

/-! ## §2 — The constraint list (19 summary copies · verifier anchor · freshness gadget). -/

/-- The 19 summary copy constraints `row[i] == pi[i]` (`PresentationAir::constraints`, @807–818),
generated from the layout exactly as the hand AIR generates them. -/
def summaryPins : List VmConstraint2 :=
  (List.range SUMMARY_WIDTH).map (fun i => .base (.piBinding VmRow.first i i))

/-- The `verifier_block_height` public anchor: the freshness check reads it from the presentation's
own public inputs (`verify` @317), so its column is PI-bound. -/
def verifierPin : VmConstraint2 := .base (.piBinding VmRow.first VERIFIER PI_VERIFIER)

/-- The diff-binding body `DIFF − NOT_AFTER + VERIFIER` (`verify_freshness_binding` @338,
`diff = not_after_height − verifier_height`). -/
def diffBindBody : EmittedExpr :=
  .add (.add (.var DIFF) (.mul (.const (-1)) (.var NOT_AFTER))) (.var VERIFIER)

/-- The diff-binding gate (`diff = not_after − verifier`). -/
def diffBindGate : VmConstraint2 := .base (.gate diffBindBody)

/-- The bound body `DIFF + HI − p/2` (the exact `diff ≤ p/2` gadget's linear leg: `hi = p/2 − diff`,
i.e. `diff + hi = p/2`). -/
def boundBody : EmittedExpr := .add (.add (.var DIFF) (.var HI)) (.const (-1006632960))

/-- The bound gate (`diff + hi = p/2`). -/
def boundGate : VmConstraint2 := .base (.gate boundBody)

/-- Range lookup: `diff ∈ [0, 2^30)` (the wrapped-`diff`/expired tooth). -/
def diffRangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF]⟩

/-- Range lookup: `hi ∈ [0, 2^30)` (the exact-`p/2` tooth: forces `diff ≤ p/2`, not `diff < 2^30`). -/
def hiRangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var HI]⟩

/-- **`presentationFreshnessDesc`** — the presentation summary AIR + internalized freshness binding.
`tables` declares the single shared range table (`bits = 30` feeds the assembler's `decomp_cols`);
the byte table is Presence-detected from the range lookups, so no other table is declared. -/
def presentationFreshnessDesc : EffectVmDescriptor2 :=
  { name        := "dregg-presentation-freshness::summary-v1"
  , traceWidth  := PRES_WIDTH
  , piCount     := PI_COUNT
  , tables      := [rangeTableDef FRESH_BITS]
  , constraints := summaryPins ++
      [verifierPin, diffBindGate, boundGate, diffRangeLookup, hiRangeLookup]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string). -/

#guard emitVmJson2 presentationFreshnessDesc ==
  "{\"name\":\"dregg-presentation-freshness::summary-v1\",\"ir\":2,\"trace_width\":23,\"public_input_count\":20,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":30}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":13,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":14,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":15,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":17,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":18,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":19},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}}},\"r\":{\"t\":\"var\",\"v\":19}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"const\",\"v\":-1006632960}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":21}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":22}]}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — Genuinely-proven, non-vacuous semantic lemmas (the freshness teeth). -/

/-- The diff-binding gate body is zero iff `diff = not_after − verifier`. -/
theorem diffBind_body_zero_iff (a : Assignment) :
    diffBindBody.eval a = 0 ↔ a DIFF = a NOT_AFTER - a VERIFIER := by
  simp only [diffBindBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The bound gate body is zero iff `diff + hi = p/2`. -/
theorem bound_body_zero_iff (a : Assignment) :
    boundBody.eval a = 0 ↔ a DIFF + a HI = HALF_P := by
  simp only [boundBody, HALF_P, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- **The exact-bound soundness of the two-range gadget.** Given both `diff` and `hi` in
`[0, 2^30)` and `diff + hi = p/2` (as integers — the field equation forces the integer sum since
`diff + hi < 2^31 < p/2 + p`), `diff ≤ p/2`. This is the tooth a single non-power-of-two `Range`
could not express; a `diff > p/2` has no in-range `hi`. -/
theorem freshness_bound_sound (diff hi : ℤ)
    (hd : 0 ≤ diff ∧ diff < 2 ^ 30) (hh : 0 ≤ hi ∧ hi < 2 ^ 30)
    (hsum : diff + hi = HALF_P) : diff ≤ HALF_P := by
  simp only [HALF_P] at *
  omega

/-- **The gadget bites.** A `diff` strictly above `p/2` (yet still in `[0, 2^30)`) admits NO
in-range `hi` closing `diff + hi = p/2` — the `hi` range lookup is UNSAT. -/
theorem freshness_bound_bites (diff hi : ℤ)
    (hd : diff < 2 ^ 30) (hgt : diff > HALF_P) (hh : 0 ≤ hi ∧ hi < 2 ^ 30) :
    diff + hi ≠ HALF_P := by
  simp only [HALF_P] at *
  omega

-- Non-vacuity witnesses: each gate ACCEPTS a satisfying assignment and REJECTS a violating one.
-- diff-binding: not_after 1500, verifier 1000 ⇒ diff = 500 satisfies; 501 does not.
#guard decide (diffBindBody.eval
  (fun i => if i = DIFF then 500 else if i = NOT_AFTER then 1500 else if i = VERIFIER then 1000 else 0) = 0)
#guard decide (¬ (diffBindBody.eval
  (fun i => if i = DIFF then 501 else if i = NOT_AFTER then 1500 else if i = VERIFIER then 1000 else 0) = 0))
-- bound: diff 500, hi = p/2 − 500 satisfies; hi off by one does not.
#guard decide (boundBody.eval
  (fun i => if i = DIFF then 500 else if i = HI then 1006632460 else 0) = 0)
#guard decide (¬ (boundBody.eval
  (fun i => if i = DIFF then 500 else if i = HI then 1006632461 else 0) = 0))

-- The range teeth, in Lean: an honest `diff = 500 ∈ [0, 2^30)` is a range row; the first
-- out-of-range value `2^30` (and hence any wrapped/expired diff) is NOT.
#guard decide (([500] : List ℤ) ∈ rangeRows FRESH_BITS)
#guard decide (¬ (([2 ^ 30] : List ℤ) ∈ rangeRows FRESH_BITS))
-- The exact `p/2` tooth: for `diff = p/2 + 1` the complement `hi = -1 = p − 1` is out of range.
#guard decide (¬ (([2013265920] : List ℤ) ∈ rangeRows FRESH_BITS))

-- Shape pins.
#guard presentationFreshnessDesc.traceWidth == PRES_WIDTH
#guard presentationFreshnessDesc.piCount == PI_COUNT
#guard presentationFreshnessDesc.constraints.length == SUMMARY_WIDTH + 5
#guard presentationFreshnessDesc.tables.length == 1

#assert_axioms diffBind_body_zero_iff
#assert_axioms bound_body_zero_iff
#assert_axioms freshness_bound_sound
#assert_axioms freshness_bound_bites

end Dregg2.Circuit.Emit.PresentationEmit
