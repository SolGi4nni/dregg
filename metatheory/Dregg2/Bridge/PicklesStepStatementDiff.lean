/-
# Dregg2.Bridge.PicklesStepStatementDiff — the STEP statement layout, ENUMERATED, MODELED in Lean,
and diffed against the TWO independent implementations that agree on it (OCaml Pickles + openmina
Rust), with the `fq = Type2/Fq` field-key source-confirmed and a kernel diverging control.

Complement to `Dregg2.Bridge.PicklesStatementDiff` (the WRAP statement, confirmed byte-exact against
live devnet block 539508). The STEP per-proof statement has a DIFFERENT flat layout and its own
field-key; the Wrap lane enumerated it and handed it here.

## ⚑ SUBSTRATE — House Law #1, said at constraint #1
This is **Lean-authored synthesis**. `stepFqBlock` / `stepToDataFlat` / `type2OfField shift2Fq` (the
last from `PicklesRecursion`) are the Lean emitters for the Step per-proof flat public-input packing;
nothing here is a Rust AIR. The references are READ-ONLY oracles:
  * `~/dev/mina/src/lib/pickles/composition_types/composition_types.ml:1268-1318` — the Step
    `Per_proof.spec` + `to_data` (a 2024 snapshot).
  * `~/dev/mina/src/lib/pickles/impls.ml:128-143` — the Step statement `typ`, which binds the `Field`
    spec leaf to `Shifted_value.Type2.typ Other_field` (Other_field = Tock = Fq): the field-key.
  * `~/dev/mina-rust/crates/ledger/src/proofs/unfinalized.rs:103-435` — openmina's INDEPENDENT Rust
    `Unfinalized` / `to_field_elements`, the code that produced the kimchi-accepted wires the Wrap
    lane diffed. Its `// Fq` block takes `.shifted` (= `ShiftedValue<Fq>` = Type2, `plonk_checks.rs:113`).

## ⚑ PHASE A discipline — LAYOUT / ORDER FIDELITY, and NOT byte-exact-against-a-live-wire
Unlike the Wrap lane, **this fixture carries NO step-statement public input** (§Residual): the live
block is a Wrap-proof decode, so `step_deferred_values` in it is the WRAP statement's payload ABOUT
the step proof (its `_shifted` fields are Type1/Fp = the Wrap `fp` block), not a step proof's own
public input. So the STEP claims proven here are, precisely:
  * **ORDER + slot-count** (27 slots: `fq 5 · digest 1 · challenge 2 · scalar_challenge 3 ·
    bulletproof 15 · bool 1`) — ORDER-CONFIRMED against two implementations that AGREE (OCaml
    `composition_types.to_data` + openmina `Unfinalized::to_field_elements`), and o1js bytecode carries
    the code path (the paired oracle greps it, green-or-bust).
  * **FIELD-KEY `fq = Type2/Fq`** — SOURCE-DEFINITIVE (`impls.ml:135` + openmina `unfinalized.rs:105`),
    with a kernel control proving the choice is OBSERVABLE (identity / Type1-over-Fq / Type2-over-Fq are
    pairwise distinct on a concrete scalar), so a wrong key WOULD diverge if a wire existed.
  * **NOT proven**: the PACKED VALUES against a live step wire, and the Fq→Fp slot embedding when q>p.
    Both need a decoded step statement (§Residual). This is FIDELITY of layout, **NOT** "machine-checked
    Pickles" and asserts nothing about IPA/recursion soundness (Phase B).

NOT imported by the `Dregg2` root, per house practice for gates.
-/
import Dregg2.Circuit.Emit.PicklesRecursion

set_option autoImplicit false
-- `PicklesRecursion` uses the same bound: the `decide` paths anchor 255-bit Pasta shift constants
-- (`2^255` via `npow`), which exceed the default recursion depth.
set_option maxRecDepth 40000

namespace Dregg2.Bridge.PicklesStepStatementDiff

open Dregg2.Circuit.Emit.PicklesRecursion
  (Fp Fq Shift1 Shift2 shift1Fp shift2Fq type1OfField type2OfField type2ToField
   StepDeferredValues deferredRounds)

/-! ## §0 — the enumerated Step per-proof slot map (`composition_types.ml:1268-1318`).

`Per_proof.spec bp_log2` is `Struct [ Vector (Field, N5); Vector (Digest, N1); Vector (Challenge, N2);
Vector (Scalar Challenge, N3); Vector (Bulletproof_challenge, bp_log2); Vector (Bool, N1) ]`, and
`to_data` emits the six blocks in that order. `bp_log2 = Backend.Tock.Rounds.n = 15` (the WRAP proof's
IPA rounds — a Step proof DEFERS a Wrap proof, mirror of the Wrap statement's 16 = Step rounds). -/

/-- The Step per-proof flat `to_data` layout (block name × slot count), in order. -/
def stepPerProofLayout : List (String × Nat) :=
  [("fq", 5), ("digest", 1), ("challenge", 2), ("scalar_challenge", 3),
   ("bulletproof_challenge", 15), ("bool", 1)]

/-- **27 slots**, and the bulletproof count is the DERIVED wrap round count — not a bare literal:
`stepPerProofLayout`'s bp entry equals `deferredRounds .step` (which reduces to `wrapShape.rounds`), so
a wrong round count fails here. The total public-input width of ONE per-proof block is 27. -/
theorem step_slot_count_and_bp_source :
    (stepPerProofLayout.map Prod.snd).sum = 27
    ∧ stepPerProofLayout.getD 4 ("", 0) = ("bulletproof_challenge", deferredRounds .step) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §1 — the fq block, and its Type2/Fq shift (the field-key). THE STEP-SPECIFIC SIGNAL.

`to_data`'s first block is `fq = [combined_inner_product; b; zeta_to_srs_length; zeta_to_domain_size;
perm]` (`composition_types.ml:1299-1305`; openmina `unfinalized.rs:399-403`). Same FIELD order as the
Wrap `fp` block — the DIFFERENCE is (a) the shift is **Type2 over Fq** (subtract-only, no halving) vs
Wrap's Type1/Fp, and (b) the block's POSITION in the flat layout (§2, digest comes right after). -/

variable {Chal Sc Fld : Type}

/-- The Step per-proof `fq` block, IN ORDER (`composition_types.ml:1299-1305`). -/
def stepFqBlock (dv : StepDeferredValues Chal Sc Fld) : List Fld :=
  [dv.combinedInnerProduct, dv.b, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize, dv.plonk.perm]

/-- The `challenge` block `[beta; gamma]` (`composition_types.ml:1307`). -/
def stepChallengeBlock (dv : StepDeferredValues Chal Sc Fld) : List Chal :=
  [dv.plonk.minimal.beta, dv.plonk.minimal.gamma]

/-- The `scalar_challenge` block `[alpha; zeta; xi]` (`composition_types.ml:1308`). -/
def stepScalarChallengeBlock (dv : StepDeferredValues Chal Sc Fld) : List Sc :=
  [dv.plonk.minimal.alpha, dv.plonk.minimal.zeta, dv.xi]

/-- **The Step fq block is carried Type2/Fq — subtract-only over Fq, `s ↦ s − 2^255`** — NOT the Wrap
side's Type1/Fp halving. `type2OfField shift2Fq` IS that map (`shifted_value.ml:185-187` `s − shift`,
`shift2Fq.shift = 2^255`). This states it for a variable scalar, so it is the shift itself, not a
coincidence of one input. -/
theorem step_fq_shift_is_subtract_only (s : Fq) :
    type2OfField shift2Fq s = s - shift2Fq.shift := rfl

/-! ### §1a — ⚑ THE DIVERGING CONTROL: the field-key choice is OBSERVABLE.

The field-key claim (`fq = Type2/Fq`) is only worth anything if the wrong encodings would produce
different wire words. Two same-field mistakes a first-pass port would make, plus identity:
  * **identity** — put the raw scalar on the wire (no shift).
  * **Type1-over-Fq** — reach for the halving encoding (the Wrap `fp` shift) over the right field.
Both must DIVERGE from Type2/Fq. (The wrong-FIELD control, Type2/Fp vs Type2/Fq, is a cross-modulus
bigint check in the paired oracle — the two live in different Lean types and cannot be compared here.)
-/

/-- Type1 over **Fq** — the WRONG-KIND control (halving instead of subtract-only). `c = 2^255 + 1`,
`twoInv = 2⁻¹ mod qN`; `shift1Fq_wellformed` kernel-checks the literal so it is not trusted. -/
def shift1Fq : Shift1 Fq :=
  { c := (28948022309329048855892746252171976963271935850878634640049049255563201871872 : Fq)
    twoInv := (14474011154664524427946373126085988481681528240970823689839871374196681474049 : Fq) }

/-- The control shift is well-formed: its `twoInv` really inverts 2, and `c = 2^255 + 1` over Fq. -/
theorem shift1Fq_wellformed :
    (2 : Fq) * shift1Fq.twoInv = 1 ∧ shift1Fq.c = (2 : Fq) ^ 255 + 1 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- An illustrative Fq scalar. ⚑ There is NO real step wire in this fixture (§Residual); this is a
representative value, and the control below proves the ENCODING CHOICE is observable, not a match to
live data. (Its integer matches the paired oracle's `SAMPLE`, so a human can eyeball TS == Lean.) -/
def SAMPLE_FQ : Fq :=
  (19890585860582513838359427261530390921328764305959386728558585581183530790096 : Fq)

/-- ⚑ **THE DIVERGING CONTROL (kernel).** On a concrete Fq scalar the three candidate fq-block
encodings are pairwise DISTINCT — identity (no shift), Type1-over-Fq (the wrong KIND, halving), and the
correct Type2-over-Fq (subtract-only) — and Type2/Fq round-trips. So IF a live step wire existed, at
most one matches; the field-key is FALSIFIABLE, the mirror of the Wrap lane's `fp_shift_is_load_bearing`
against its real block. -/
theorem step_fq_key_is_observable :
    SAMPLE_FQ ≠ type2OfField shift2Fq SAMPLE_FQ
    ∧ type1OfField shift1Fq SAMPLE_FQ ≠ type2OfField shift2Fq SAMPLE_FQ
    ∧ type2ToField shift2Fq (type2OfField shift2Fq SAMPLE_FQ) = SAMPLE_FQ := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **TS↔Lean pin.** The Type2/Fq shift of `SAMPLE_FQ` equals, to the digit, the value the paired
oracle (`pickles-step-statement-oracle.ts`) computes with `type2(SAMPLE, Q)` in bigint arithmetic. Two
independent emitters (the Lean kernel over `ZMod qN` vs the TS `(s − 2^255) mod q`) land on the SAME
field element — the field-key agreement is a byte-diff on this input, not eyeballed. -/
theorem step_fq_sample_shift_pins_oracle :
    type2OfField shift2Fq SAMPLE_FQ =
      (19890585860582513838359427261530390921419884937022399468189279074013691866322 : Fq) := by
  decide

/-! ## §2 — the flat `to_data` ORDER, and it DIFFERS from the Wrap statement.

`to_data` (`composition_types.ml:1312-1318`; openmina `unfinalized.rs:397-434`) emits the six blocks
`[fq; digest; challenge; scalar_challenge; bulletproof_challenges; bool]`. This is a DIFFERENT sequence
from the Wrap statement head (`composition_types.ml:855-878`), so a step assembler cannot reuse the
Wrap order. -/

/-- The Step per-proof block order. -/
def stepBlockOrder : List String :=
  ["fq", "digest", "challenge", "scalar_challenge", "bulletproof_challenge", "bool"]

/-- The Wrap statement head block order, for contrast (`composition_types.ml:855-882`
`fp; challenge; scalar_challenge; digest; bulletproof; branch_data; feature_flags; lookup_opt`). -/
def wrapBlockOrder : List String :=
  ["fp", "challenge", "scalar_challenge", "digest", "bulletproof_challenge", "branch_data",
   "feature_flags", "lookup_opt"]

/-- ⚑ **Step ≠ Wrap layout**, five ways, kernel-checked:
  (1) the digest comes EARLY in Step (block #2, slot after `fq`) vs LATE in Wrap (block #4);
  (2) Step carries a trailing `bool` (`should_finalize`); Wrap carries none;
  (3) Step has NO `branch_data` (its domain is fixed per branch); Wrap does;
  (4) the field block is `fq` (Step) vs `fp` (Wrap);
  (5) Step defers 15 bulletproof challenges (WRAP rounds) vs Wrap's 16 (STEP rounds). -/
theorem step_and_wrap_layouts_differ :
    stepBlockOrder.getD 1 "" = "digest"
    ∧ wrapBlockOrder.getD 3 "" = "digest"
    ∧ stepBlockOrder.getD 5 "" = "bool"
    ∧ "bool" ∉ wrapBlockOrder
    ∧ "branch_data" ∉ stepBlockOrder
    ∧ "branch_data" ∈ wrapBlockOrder
    ∧ stepBlockOrder.getD 0 "" = "fq"
    ∧ wrapBlockOrder.getD 0 "" = "fp"
    ∧ deferredRounds .step = 15
    ∧ deferredRounds .wrap = 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §3 — the flat encoding lays each block at its declared slot (the ORDER, concretely).

The field-generic flat `to_data`: `fq ++ [digest] ++ [beta,gamma] ++ [alpha,zeta,xi] ++ bp ++ [bool]`
(the `fq` block already in shifted form; openmina pushes everything into one `Vec<F>`). -/

/-- The Step per-proof flat `to_data`, field-generic. -/
def stepToDataFlat {T : Type} (fq : List T) (digest : T) (beta gamma alpha zeta xi : T)
    (bp : List T) (shouldFinalize : T) : List T :=
  fq ++ [digest] ++ [beta, gamma] ++ [alpha, zeta, xi] ++ bp ++ [shouldFinalize]

/-- **The slot ORDER, concretely.** Feeding the flat encoder distinct sentinels `0..26` (fq = 0–4,
digest = 5, challenge = 6–7, scalar_challenge = 8–10, bulletproof = 11–25, bool = 26) yields exactly
`[0,…,26]`: every block lands at the offset the layout (§0) declares, so nothing is dropped, merged, or
reordered, and the width is 27. -/
theorem stepToDataFlat_positions :
    stepToDataFlat [0, 1, 2, 3, 4] 5 6 7 8 9 10
        [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] 26
      = List.range 27 := by decide

/-! ## §Residual — what this rung does NOT close, named not chased.

**(1) No live step wire.** `metatheory/mina_real_block_proof.json` (block 539508) is a WRAP-proof
decode; its `step_deferred_values` is the WRAP statement's payload ABOUT the step proof (its `_shifted`
fields are Type1/Fp — the Wrap `fp` block, `PicklesStatementDiff §1`), NOT a step proof's own public
input. So the PACKED VALUES of the fq block are not byte-diffed against the chain here. The paired
oracle asserts this (the fixture's `combined_inner_product_shifted` reproduces `type1/Fp`, NOT
`type2/Fq`), so the residual is a MEASURED fact, not an assumption.

**(2) The Fq→Fp slot embedding.** Unlike Wrap (p<q, so a Type1/Fp shifted value drops into an Fq slot
directly), the Step statement is Fp-native but its fq scalars live in Fq with q>p. Type2 EXISTS for
exactly this larger-scalar-field case (`shifted_value.ml:140-150`). The exact embedding of a Type2/Fq
representative into the Fp public-input slots (the low-bit handling) is a value-level detail, tested
when a step wire exists; modeled here only as the subtract-only shift over Fq (§1).

**(3) Per-proof tiling.** The full step public input TILES this 27-slot per-proof across the
`unfinalized_proofs` vector (one per verified proof, up to `max_proofs_verified`) plus a
`messages_for_next_step_proof` digest (`composition_types.ml:1362-1369`) — the step analog of the Wrap
me-only slots. Only the per-proof layout is modeled here (the task's scope). -/

/-- The concrete fixture that closes residual (1). -/
def stepValueResidualClosedBy : String :=
  "a decoded STEP statement — a step proof's unfinalized_proofs.(i) per-proof public input " ++
  "(openmina Unfinalized), giving real Fq combined_inner_product/b/perm with their Type2/Fq " ++
  ".shifted forms: the analog of the Wrap _shifted pairing this fixture has for the Fp block"

/-! ## §Axiom hygiene — the diff rests on nothing but the kernel. -/

#assert_axioms step_slot_count_and_bp_source
#assert_axioms step_fq_shift_is_subtract_only
#assert_axioms shift1Fq_wellformed
#assert_axioms step_fq_key_is_observable
#assert_axioms step_fq_sample_shift_pins_oracle
#assert_axioms step_and_wrap_layouts_differ
#assert_axioms stepToDataFlat_positions

#print axioms step_fq_key_is_observable
#print axioms stepToDataFlat_positions

end Dregg2.Bridge.PicklesStepStatementDiff
