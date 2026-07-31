/-
# Dregg2.Bridge.PicklesR3BranchDataDiff — R3's EARLIEST FALSIFIABLE SIGNAL:
the Lean-emitted `branch_data` packed field, DIFFED byte-exact against the real chain's emission.

## ⚑ SUBSTRATE — House Law #1, said at constraint #1
This is **Lean-authored synthesis**. `branchDataPack` (in `PicklesRecursion`) is the Lean emitter for
the one Wrap-statement field that requires real *packing* logic; nothing here is a Rust AIR. The
reference (`~/dev/mina/.../composition_types/branch_data.ml`, `pickles_base/proofs_verified.ml`) is
READ-ONLY (a 2024 snapshot); the *operative* oracle is a live emission of that exact code (§Oracle).

## ⚑ PHASE A discipline — this is a FIDELITY diff, NOT a soundness proof
The claim proved here is: **the Lean-emitted `branch_data` field equals the packed value the deployed
OCaml Pickles `Spec.pack`/`Branch_data.pack` put on the wire, for one fixed input (MEASURED).** It is
NOT "machine-checked Pickles" and asserts nothing about IPA/recursion soundness (Phase B). Honest
label: *the Lean pack matches the real chain's field, byte-exact, at slot 29, for {N2, 16}.*

## The fixed input and the smallest piece
`branch_data` is the ONLY Wrap-statement field whose packed value differs from its raw inputs: it
folds `{proofs_verified ∈ {N0,N1,N2}, domain_log2}` into one field via
`pack = 4·domain_log2 + project(prefix_mask(proofs_verified))` (`branch_data.ml:63-74`). Every other
statement slot is identity placement of an already-field value (fp/challenge/scalar/digest blocks,
the 16 bulletproof challenges, the padding) — those are the LAYOUT question that
`Dregg2.Bridge.MinaWrapPublicInput` already pins against this same block, slot-by-slot. So the packing
CRUX — and the smallest emit-and-diff — is this single field.

The fixed input is the real block's own unpacked record: `proofs_verified = N2` (`to_int = 2`),
`domain_log2 = 16`.

## §Oracle — a live emission of exactly the code o1js wraps (zero build)
`metatheory/mina_real_block_proof.json` is a Mina **devnet** block (state hash
`3NLmVB6…jm12zNk`, height 539508) whose Wrap proof was decoded by
`metatheory/fixtures/pickles-extractors`. Its `wrap_public_input` is the 40-word public input
assembled by **openmina's own `PreparedStatement::to_public_input`**, and — this is what makes it an
oracle rather than a transcription — **o1-labs' own `kimchi::verifier::verify::<Pallas,…>` ACCEPTS
the Wrap proof against those 40 words** (extractor ground-truth #3). If slot 29 were wrong the VK
would reject; it does not. Measured: `wrap_public_input[29] = "67"`, and the block's decoded
`branch_data` is `{proofs_verified = N2, domain_log2 = 16}`.

o1js emits the SAME field from the SAME source: o1js is `js_of_ocaml` of Mina's Pickles, and its
bytecode carries this exact code path (`grep branch_data|Prefix_mask` in
`o1js_node.bc.cjs` → 102 hits; `proofs_verified` → 266; `composition_types` → 194). So the number `67`
below is an emission of precisely the `Branch_data.pack` o1js runs, only produced natively and
kimchi-verified. This is the R3 oracle, and it agrees FOUR ways: the deployed OCaml chain, openmina's
Rust reimplementation, the kimchi verifier's acceptance, and — below — the Lean synthesis.

## The residual, so this cannot be mistaken for all of R3
R3 has two halves (`docs/PICKLES-SYNTHESIS-EPOCH-SCOPE.md` §5 R3): the byte-exact statement PACKING
(this file's subject, plus the layout `MinaWrapPublicInput` pins) and the `internal_vars` witness
mapping. This diff clears the packing crux; it does NOT test `internal_vars`, which has no dregg model
and no zero-build oracle at this rung (the real block gives packed VALUES, not the witness recipe).
`internal_vars` is emitted BY the R1 builder, so it is tested when R1 exists, not here.

NOT imported by the `Dregg2` root, per house practice for gates.
-/
import Dregg2.Circuit.Emit.PicklesRecursion

set_option autoImplicit false

namespace Dregg2.Bridge.PicklesR3BranchDataDiff

open Dregg2.Circuit.Emit.PicklesRecursion (BranchData branchDataPack prefixMask)

/-- **The oracle**, `wrap_public_input[29]` of devnet block 539508 (`mina_real_block_proof.json`),
the packed `branch_data` field openmina's `PreparedStatement::to_public_input` produced and o1-labs'
kimchi verifier accepted — an emission of exactly the `Branch_data.pack` o1js wraps. -/
def realBlockBranchData : Nat := 67

/-- **The fixed input**: the block's own decoded, UNPACKED `branch_data` record
(`branch_data_proofs_verified = N2 ⇒ to_int 2`, `branch_data_domain_log2 = 16`). -/
def fixedInput : BranchData := { proofsVerified := 2, domainLog2 := 16 }

/-- ⚑⚑ **THE R3 EARLIEST FALSIFIABLE SIGNAL — the byte-exact diff, MATCHED.**
The Lean synthesizer's `branch_data` emitter, run on the block's own unpacked record, reproduces the
packed field the deployed chain put at slot 29 and kimchi accepted. This is a FIDELITY match, not a
soundness claim: Lean's `Spec.pack` of `branch_data` = the real chain's, byte-exact, for {N2, 16}. -/
theorem lean_branch_data_matches_real_block :
    branchDataPack fixedInput = realBlockBranchData := by decide

/-! ## §Falsifiability — the diff is a real gate, and the prefix-mask is load-bearing.

The signal is only worth anything if a WRONG emitter fails it. The subtlety `branch_data` exists to
test: the low 2 bits are the `prefix_mask` of `proofs_verified` (`N2 ↦ [true;true] = 3`), NOT the
integer tag (`to_int N2 = 2`). A synthesizer that packed the tag directly would emit `66`, and the
chain would reject. -/

/-- The NAIVE emitter a first-pass port would write: low 2 bits = the integer tag, not the mask. -/
def naiveBranchDataPack (b : BranchData) : Nat := 4 * b.domainLog2 + b.proofsVerified

/-- **The diff DISTINGUISHES correct from naive.** The naive emitter emits `66`, the real block
carries `67`; so this gate goes RED on the exact mistake `branch_data` is designed to catch, and the
`prefix_mask` (`N2 ↦ 3`, not `2`) is load-bearing. -/
theorem naive_emitter_diverges_and_is_rejected :
    naiveBranchDataPack fixedInput = 66
    ∧ naiveBranchDataPack fixedInput ≠ realBlockBranchData
    ∧ branchDataPack fixedInput ≠ naiveBranchDataPack fixedInput := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The load-bearing bit, isolated.** The real block's field minus `4·domain_log2` is exactly the
prefix mask `3 = project [true;true]`, i.e. the block confirms `prefix_mask N2 = 3` (not `to_int N2`),
which is the one non-identity fact the whole packing turns on. -/
theorem real_block_forces_the_prefix_mask :
    prefixMask 2 = 3
    ∧ realBlockBranchData - 4 * 16 = prefixMask 2
    ∧ prefixMask 2 ≠ (2 : Nat) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## §Non-vacuity — the emitter separates the three legal tags at this domain.

Without this, "the emitter matches at N2" is compatible with a constant. The three legal
`proofs_verified` values pack to three DISTINCT fields at `domain_log2 = 16`, and only `N2` hits the
real block's `67`. -/

/-- The three legal tags pack distinctly at `domain_log2 = 16`, and exactly `N2` reproduces `67`. -/
theorem the_emitter_separates_the_three_tags :
    branchDataPack { proofsVerified := 0, domainLog2 := 16 } = 64
    ∧ branchDataPack { proofsVerified := 1, domainLog2 := 16 } = 66
    ∧ branchDataPack { proofsVerified := 2, domainLog2 := 16 } = 67
    ∧ ([64, 66, 67] : List Nat).Nodup
    ∧ (([0, 1, 2].filter
        (fun pv => branchDataPack { proofsVerified := pv, domainLog2 := 16 } == realBlockBranchData))
        = [2]) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## §Axiom hygiene — the diff rests on nothing but the kernel. -/

#assert_axioms lean_branch_data_matches_real_block
#assert_axioms naive_emitter_diverges_and_is_rejected
#assert_axioms real_block_forces_the_prefix_mask
#assert_axioms the_emitter_separates_the_three_tags

#print axioms lean_branch_data_matches_real_block

end Dregg2.Bridge.PicklesR3BranchDataDiff
